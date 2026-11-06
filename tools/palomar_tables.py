"""Decode the archived off-diagonal tables; no private repository is required."""
from pathlib import Path
import json
ROOT = Path(__file__).resolve().parents[1]
DIGITS = '0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/'

def decode(path):
    profile = tuple(map(int, path.stem.split('_')[1:]))
    text = json.loads((ROOT/'data/archived_tables.json').read_text())[path.relative_to(ROOT).as_posix()]
    n = sum(profile)
    assert len(text) == n*(n-1)
    rows = [[i if i == j else 0 for j in range(n)] for i in range(n)]
    k = 0
    for i in range(n):
        for j in range(i+1,n):
            value = DIGITS.index(text[k])*64 + DIGITS.index(text[k+1])
            assert value < n
            rows[i][j] = rows[j][i] = value
            k += 2
    return profile, rows
