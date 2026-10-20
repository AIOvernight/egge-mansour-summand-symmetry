#!/usr/bin/env python3
"""Build a Lean project and record exact theorem types, axioms and source hashes.

This checks declared axiom dependencies, not mathematical relevance of a type.
Review the generated type transcript and the definitions independently.
Only Python's standard library is needed. Run --selftest for failure-path tests.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*\Z")
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")
REPORT = re.compile(
    r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
    re.MULTILINE,
)


def code_only(source: str) -> str:
    """Mask nested Lean comments and string literals, preserving line numbers."""
    out = list(source)
    i = 0
    depth = 0
    quoted = False
    line = False
    while i < len(source):
        char = source[i]
        pair = source[i:i + 2]
        if line:
            if char == "\n":
                line = False
            else:
                out[i] = " "
        elif depth:
            if pair == "/-":
                out[i:i + 2] = [" ", " "]
                depth += 1
                i += 1
            elif pair == "-/":
                out[i:i + 2] = [" ", " "]
                depth -= 1
                i += 1
            elif char != "\n":
                out[i] = " "
        elif quoted:
            if char != "\n":
                out[i] = " "
            if char == "\\" and i + 1 < len(source):
                i += 1
                if source[i] != "\n":
                    out[i] = " "
            elif char == '"':
                quoted = False
        elif pair in ("/-", "--"):
            depth = int(pair == "/-")
            line = pair == "--"
            out[i:i + 2] = [" ", " "]
            i += 1
        elif char == '"':
            quoted = True
            out[i] = " "
        i += 1
    if depth or quoted:
        raise ValueError("unterminated comment or string in source")
    return "".join(out)


def check_source(source: str, label: str) -> None:
    masked = code_only(source)
    hit = FORBIDDEN.search(masked)
    if hit:
        line = masked[:hit.start()].count("\n") + 1
        raise ValueError(f"{label}:{line}: forbidden source token {hit.group()}")


def parse_axioms(transcript: str, expected: list[str]) -> dict[str, list[str]]:
    if re.search(r"\berror:|\bwarning:.*sorry", transcript, re.IGNORECASE):
        raise ValueError("compiler error or sorry warning in audit transcript")
    reports = {}
    for match in REPORT.finditer(transcript):
        theorem = match.group(1)
        if theorem in reports:
            raise ValueError(f"duplicate axiom report: {theorem}")
        axioms = sorted(x.strip() for x in (match.group(2) or "").split(",") if x.strip())
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"{theorem}: forbidden axioms {sorted(unexpected)}")
        reports[theorem] = axioms
    if set(reports) != set(expected):
        raise ValueError(f"axiom reports differ: missing={set(expected) - set(reports)}, "
                         f"unexpected={set(reports) - set(expected)}")
    return reports


def inventory(project: Path) -> dict[str, str]:
    paths = sorted(project.glob("*.lean")) + sorted((project / "EggeMansour").rglob("*.lean"))
    paths += [project / "lean-toolchain", project / "lake-manifest.json", project / "lakefile.toml"]
    if not paths or not (project / "EggeMansour").is_dir():
        raise ValueError("expected an EggeMansour project")
    hashes = {}
    for path in paths:
        data = path.read_bytes()
        if path.suffix == ".lean":
            check_source(data.decode(), str(path.relative_to(project)))
        hashes[str(path.relative_to(project))] = hashlib.sha256(data).hexdigest()
    return hashes


def run_logged(command: list[str], cwd: Path, log: Path) -> float:
    start = time.monotonic()
    with log.open("w") as output:
        result = subprocess.run(command, cwd=cwd, stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise ValueError(f"command failed ({result.returncode}); see {log}: {command}")
    return time.monotonic() - start


def selftest() -> None:
    safe = '/- sorry /- axiom -/ admit -/\n-- native_decide\n#eval "sorry \\\" axiom"\ntheorem x := True.intro'
    check_source(safe, "safe")
    for source in ("by sorry", "by admit", "axiom fake : False", "by native_decide", "/- unclosed"):
        try:
            check_source(source, "deliberate failure")
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted forbidden source: {source}")
    report = "'A.x' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
    assert parse_axioms(report, ["A.x"])["A.x"] == sorted(ALLOWED_AXIOMS)
    assert parse_axioms("'A.x' does not depend on any axioms\n", ["A.x"]) == {"A.x": []}
    for bad in ("", report[:-3], report + report, report.replace("Quot.sound", "sorryAx"),
                report.replace("A.x", "A.y"), report + "warning: declaration uses 'sorry'\n",
                report + "error: broken\n"):
        try:
            parse_axioms(bad, ["A.x"])
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted invalid axiom transcript: {bad}")
    with tempfile.TemporaryDirectory() as temporary:
        try:
            run_logged(["sh", "-c", "echo deliberate failure; exit 7"], Path(temporary),
                       Path(temporary) / "failure.log")
        except ValueError:
            pass
        else:
            raise AssertionError("accepted failed command")
    print("selftest: source rejection, incomplete/altered/duplicate axiom reports, and failed command checks passed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-dir", type=Path)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--module", action="append", default=[])
    parser.add_argument("--theorem", action="append", default=[])
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    if args.selftest:
        selftest()
        return
    if not args.lean_dir or not args.output_dir or not args.theorem:
        parser.error("--lean-dir, --output-dir and at least one --theorem are required")
    modules = args.module or ["EggeMansour"]
    for name in modules + args.theorem:
        if not NAME.fullmatch(name):
            parser.error(f"invalid Lean name: {name!r}")
    if len(set(args.theorem)) != len(args.theorem):
        parser.error("duplicate --theorem")
    project = args.lean_dir.resolve()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    summary = output / "audit.json"
    # Remove stale success before any operation that could fail.
    summary.unlink(missing_ok=True)
    before = inventory(project)
    audit = output / "Audit.lean"
    audit.write_text("\n".join([*(f"import {m}" for m in modules), "",
                               *(f"#check @{t}\n#print axioms {t}" for t in args.theorem)]) + "\n")
    # Keep the replayable command free of the machine's absolute private path.
    audit_argument = os.path.relpath(audit, start=project)
    commands = [["lake", "build", *modules], ["lake", "env", "lean", audit_argument]]
    build_seconds = run_logged(commands[0], project, output / "build.log")
    audit_seconds = run_logged(commands[1], project, output / "types-axioms.log")
    reports = parse_axioms((output / "types-axioms.log").read_text(), args.theorem)
    after = inventory(project)
    if before != after:
        raise ValueError("project sources changed during the build/audit; rerun on a fixed snapshot")
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=project,
                             check=True, capture_output=True, text=True).stdout.strip()
    revision = subprocess.run(["git", "rev-parse", "HEAD"], cwd=project,
                              check=True, capture_output=True, text=True).stdout.strip()
    status = subprocess.run(["git", "status", "--porcelain"], cwd=project,
                            check=True, capture_output=True, text=True).stdout
    result = {"status": "passed", "scope": "source-token scan; exact printed types; standard axiom dependencies",
              "lean_version": version, "git_revision": revision, "git_status": status,
              "commands": commands, "timings_seconds": {"build": build_seconds, "audit": audit_seconds},
              "source_sha256": after, "axioms": reports,
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "artifact_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                  for p in (audit, output / "build.log", output / "types-axioms.log")}}
    summary.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(f"passed: {len(reports)} declarations; {len(after)} source/config files; {summary}")


if __name__ == "__main__":
    main()
