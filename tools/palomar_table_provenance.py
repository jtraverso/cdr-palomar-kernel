"""Compare emitted kernel data with every off-diagonal archived table entry."""
import hashlib
import json
from pathlib import Path
import re

from palomar_tables import ROOT, decode

def parse_tree(text):
    tokens = re.findall(r'\(|\)|\.leaf|\.branch|[A-Za-z_][A-Za-z_0-9]*|[0-9]+', text)
    pos = 0
    def parse():
        nonlocal pos
        assert tokens[pos] == '('; pos += 1
        tag = tokens[pos]; pos += 1
        value = tokens[pos]; pos += 1
        if tag == '.leaf':
            tree = ('leaf', int(value) if value.isdigit() else value)
        else:
            assert tag == '.branch'
            tree = ('branch', int(value), parse(), parse())
        assert tokens[pos] == ')'; pos += 1
        return tree
    result = parse()
    assert pos == len(tokens)
    return result

def lookup(tree, index):
    while tree[0] == 'branch':
        tree = tree[2] if index < tree[1] else tree[3]
    return tree[1]

def parse_comparisons(text):
    tokens = re.findall(r'[()]|<|[A-Za-z_][A-Za-z_0-9]*|[0-9]+',text)
    pos = 0
    def parse():
        nonlocal pos
        token = tokens[pos]; pos += 1
        if token == '(':
            result = parse()
            assert tokens[pos] == ')'; pos += 1
            return result
        if token == 'if':
            left = tokens[pos]; pos += 1
            assert tokens[pos] == '<'; pos += 1
            right = tokens[pos]; pos += 1
            assert tokens[pos] == 'then'; pos += 1
            yes = parse()
            assert tokens[pos] == 'else'; pos += 1
            no = parse()
            return ('if',left,int(right) if right.isdigit() else right,yes,no)
        if token.isdigit():
            return ('leaf',int(token))
        arg = tokens[pos]; pos += 1
        assert arg in ('x','y')
        return ('call',token,arg)
    tree = parse()
    assert pos == len(tokens)
    return tree

def evaluate_comparisons(tree, values, functions):
    while tree[0] == 'if':
        right = tree[2] if isinstance(tree[2],int) else values[tree[2]]
        tree = tree[3] if values[tree[1]] < right else tree[4]
    if tree[0] == 'leaf':
        return tree[1]
    return evaluate_comparisons(functions[tree[1]],{'y':values[tree[2]]},functions)

def verify(path):
    profile, expected = decode(path)
    n = sum(profile)
    source = path.read_text(encoding='utf-8')
    if 'LookupTree Nat' in source:
        tree_expr = re.search(r'^def k_\d+_\d+_\d+_rows : LookupTree Nat := (.+)$', source, re.M)[1]
        dispatch = parse_tree(tree_expr)
        bits, base = map(int, re.search(r'Nat.shiftRight \(k_\d+_\d+_\d+_rows.get x\) \((\d+) \* y\) % (\d+)',source).groups())
        assert base == 1<<bits and n <= base
        def get(x,y):
            return (lookup(dispatch,x) >> (bits*y)) % base
    elif '_lookup_' in source:
        functions = {name:parse_comparisons(expr) for name,expr in re.findall(
            r'^def (k_\d+_\d+_\d+_lookup_\d+) \(y : Nat\) : Nat := (.+)$',source,re.M)}
        dispatch = parse_comparisons(re.search(r'^  (if x < y then .+)$',source,re.M)[1])
        get = lambda x,y: evaluate_comparisons(dispatch,{'x':x,'y':y},functions)
    elif ': Array (Array Nat)' in source:
        actual = [list(map(int,row.split(','))) for row in re.findall(r'^  #\[([0-9,]+)\]',source,re.M)]
        assert len(actual) == n and all(len(row) == n for row in actual)
        get = lambda x,y: actual[x][y]
    else:
        raise ValueError('Unrecognized certificate representation: ' + str(path))
    count = 0
    for x in range(n):
        for y in range(x+1,n):
            assert get(x,y) == expected[x][y] == get(y,x), (profile,x,y)
            count += 1
    return dict(profile=profile, order=n, unordered_pairs=count,
                source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(), status='pass')

if __name__ == '__main__':
    files = sorted((ROOT/'CDRBicolour/Base/Data').glob('W_*.lean'))
    results = [verify(path) for path in files]
    report = dict(status='pass', archived_revision='76431935a1d61dbd7d512f32c941e37de38f6ba0',
                  witnesses=len(results), unordered_pairs=sum(r['unordered_pairs'] for r in results),
                  results=results)
    (ROOT/'docs/palomar/TABLE_PROVENANCE.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
    print(report['status'], report['witnesses'], report['unordered_pairs'])
