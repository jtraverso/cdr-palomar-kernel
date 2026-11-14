"""Verify the sealed source inventory and submission config; no Lean build."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def main():
    report = json.loads((ROOT/"evidence/STATIC_PACKAGING_CHECK.json").read_text(encoding="utf-8"))
    for item in report["sources"]:
        path = ROOT/item["path"]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == item["sha256"],item["path"]
    actual = set()
    for child in ROOT.iterdir():
        if child.name.startswith("."):
            continue
        paths = child.rglob("*.lean") if child.is_dir() else ([child] if child.suffix == ".lean" else [])
        actual.update(p.relative_to(ROOT).as_posix() for p in paths)
    assert actual == {item["path"] for item in report["sources"]}
    config = json.loads((ROOT/"cdr-iii-comparator.json").read_text(encoding="utf-8"))
    assert config["challenge_module"] == "CDRIIIChallenge"
    assert config["solution_module"] == "CDRIIISolution"
    assert len(config["theorem_names"]) == 4 and len(config["definition_names"]) == 25
    assert set(config["permitted_axioms"]) == {"propext","Classical.choice","Quot.sound"}
    manifest = json.loads((ROOT/"lake-manifest.json").read_text(encoding="utf-8"))
    for package in manifest["packages"]:
        assert package.get("subDir") is None
        if package["type"] == "git":
            assert re.fullmatch("[0-9a-f]{40}",package["rev"])
        else:
            assert package["type"] == "path"
            assert package["dir"].replace("\\","/").startswith(".lake/packages/cdr_bicolour/vendor/")
    alignment = json.loads((ROOT/"evidence/STATEMENT_ALIGNMENT.json").read_text(encoding="utf-8"))
    for item in alignment["evidence"]:
        assert hashlib.sha256((ROOT/item["path"]).read_bytes()).hexdigest() == item["sha256"]
    print(json.dumps({"status":"PASS_PACKAGE_INTEGRITY","source_files":len(actual),
                      "local_full_build":False,"official_palomar_preflight":"separate exact-commit workflow"}))


if __name__ == "__main__":
    main()
