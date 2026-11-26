"""Build, check or inventory the local closure of the two public FindAny modules."""
import argparse
import ast
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REPO = ROOT / "work_repo"
FROZEN = ROOT / "formal-quantum-computation"
BIN = ROOT / ".elan/toolchains/leanprover--lean4---v4.35.0/bin"
RUNNER = HERE / "check_module.py"
MANIFEST = HERE / "findany_replay_manifest.json"
ENTRY_POINTS = ("Track2Grover.TighterFindAny", "Track2Grover.FindAnyLowerBound")


def fingerprint(path):
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    return {"path": path.relative_to(ROOT).as_posix(), "sha256": digest}


def module_file(module, suffix):
    return REPO / Path(*module.split(".")).with_suffix(suffix)


def imports(module):
    """The local sources use ordinary one-line Lean module imports."""
    content = module_file(module, ".lean").read_text(encoding="utf-8-sig")
    # Preserve line breaks while skipping nested Lean block comments and line comments.
    depth = 0
    result = []
    for line in content.splitlines():
        pieces = []
        pos = 0
        while pos < len(line):
            if depth:
                marker = re.search(r"/-|-/", line[pos:])
                if marker is None:
                    break
                depth += 1 if marker.group() == "/-" else -1
                pos += marker.end()
            else:
                marker = re.search(r"/-|--", line[pos:])
                if marker is None:
                    pieces.append(line[pos:])
                    break
                pieces.extend([line[pos:pos + marker.start()], " "])
                if marker.group() == "--":
                    break
                depth += 1
                pos += marker.end()
        clean = "".join(pieces).strip()
        if not clean or clean in ("module", "prelude"):
            continue
        match = re.fullmatch(r"(?:(?:public|private|meta|all)\s+)*import\s+(.+)", clean)
        if not match:
            break  # Lean requires all imports to precede declarations.
        for name in match[1].split():
            if not re.fullmatch(r"\w+(?:\.\w+)*", name):
                raise ValueError(f"Unsupported import syntax in {module}: {clean}")
            result.append(name)
    return list(dict.fromkeys(result))


def dependencies():
    ordered = {}
    pending = set()

    def visit(module):
        if module in ordered:
            return
        if module in pending:
            raise ValueError(f"Import cycle at {module}")
        pending.add(module)
        direct = imports(module)
        for name in direct:
            if name.startswith("Track2Grover."):
                visit(name)
        pending.remove(module)
        ordered[module] = direct

    for name in ENTRY_POINTS:
        visit(name)
    return ordered


def accepted_receipt(path, module, checker, source, obj):
    """Match the pinned command and its terminal success line to this module."""
    body = path.read_text(encoding="utf-8-sig", errors="replace")
    terminal = re.search(r"(?:^|\n)exit=0(?: elapsed=([0-9.]+)s)?\s*\Z", body)
    if not terminal or re.search(r"\bsorryAx\b|declaration uses .?sorry", body):
        return None
    if body.startswith("command "):
        args = ast.literal_eval(body.splitlines()[0][len("command "):])
        start = path.stat().st_mtime - float(terminal[1])
    else:
        command = re.search(r"^cmd=(.+)$", body, re.MULTILINE)
        if not command:
            return None
        args = [a.strip('"') for a in shlex.split(command[1], posix=False)]
        stamp = path.stem.rsplit("_", 1)[-1]
        start = dt.datetime.strptime(stamp, "%Y%m%d-%H%M%S-%f").timestamp()
    binary = BIN / ("leanchecker.exe" if checker else "lean.exe")
    if Path(args[0]) != binary:
        return None
    if checker:
        if args[1:] not in ([module], ["--verbose", module]):
            return None
        if "--verbose" in args and f"replaying {module}" not in body.splitlines():
            return None
        current = obj.exists() and obj.stat().st_mtime <= start
    else:
        if "-o" not in args or (REPO / args[-1]).resolve() != source:
            return None
        output = (REPO / args[args.index("-o") + 1]).resolve()
        if output.name != obj.name:
            return None
        output_matches = output == obj or (
            output.exists() and obj.exists() and fingerprint(output)["sha256"] == fingerprint(obj)["sha256"]
        )
        current = (output_matches and obj.exists() and source.stat().st_mtime <= start
                   and obj.stat().st_mtime <= path.stat().st_mtime)
    return {**fingerprint(path), "current_by_timestamps": current}


def receipt(module, checker, source, obj):
    kind = "checker" if checker else "lean"
    all_paths = list((HERE / "receipts").glob(f"{module}_{kind}_*.log"))
    short_name = module.removeprefix("Track2Grover.")
    alternate = HERE / "lower_bound" / f"{short_name}_{'leanchecker' if checker else 'lean'}.log"
    if alternate.exists():
        all_paths.append(alternate)
    archived = None
    for path in sorted(all_paths, key=lambda f: f.stat().st_mtime_ns, reverse=True):
        record = accepted_receipt(path, module, checker, source, obj)
        if record:
            if record["current_by_timestamps"]:
                return record
            if archived is None:
                archived = record
    return archived


def inventory(ordered):
    modules = []
    unsealed = []
    for module, direct in ordered.items():
        source = module_file(module, ".lean")
        obj = module_file(module, ".olean")
        lean = receipt(module, False, source, obj)
        check = receipt(module, True, source, obj)
        if not all(r and r["current_by_timestamps"] for r in (lean, check)):
            unsealed.append(module)
        modules.append({
            "module": module, "imports": direct, "source": fingerprint(source),
            "object": fingerprint(obj) if obj.exists() else None,
            "object_sidecars": [fingerprint(p) for suffix in (".olean.private", ".olean.server", ".ir", ".ir.sig")
                                if (p := module_file(module, suffix)).exists()],
            "lean_receipt": lean, "leanchecker_receipt": check,
        })
    # Include transitive frozen project sources (and their build-tree counterparts).
    # Third-party Mathlib/package imports are identified by the pinned lake manifest.
    frozen_modules = {"QuantumComputationSpecs.Algorithms.Grover"}
    for direct in ordered.values():
        frozen_modules.update(n for n in direct if n.startswith(("QuantumComputation.", "QuantumComputationSpecs.")))
    todo = sorted(frozen_modules)
    frozen_sources = {}
    while todo:
        name = todo.pop()
        built = module_file(name, ".lean")
        original = FROZEN / built.relative_to(REPO)
        a, b = fingerprint(original), fingerprint(built)
        frozen_sources[name] = {"original": a, "build_source": b, "identical": a["sha256"] == b["sha256"]}
        for dep in imports(name):
            if dep.startswith(("QuantumComputation.", "QuantumComputationSpecs.")) and dep not in frozen_modules:
                frozen_modules.add(dep)
                todo.append(dep)
    reference = ROOT / "discoveries_ref/QuantumComputationDiscoveries/Algorithms"
    reference_sources = [reference / "GroverFindAny.lean"]
    reference_sources.extend(reference / "Grover/Solution" / f"{n}.lean" for n in ("Defs", "OddParityBridge", "FindAny"))
    return {
        "format": 1, "entry_points": list(ENTRY_POINTS), "module_count": len(modules),
        "complete": not unsealed and all(p["identical"] for p in frozen_sources.values()),
        "local_modules_with_missing_or_older_receipts": unsealed,
        "receipt_association": (
            "Each selected log names the pinned binary and module and ends with exit=0. "
            "Existing logs do not contain object hashes. current_by_timestamps associates the "
            "present source and object with the build time, and the object with checker start time. "
            "Hashes identify the files read when this manifest was written."
        ),
        "binaries": [fingerprint(BIN / n) for n in ("lean.exe", "leanchecker.exe", "lake.exe")],
        "replay_inputs": [fingerprint(p) for p in (Path(__file__).resolve(), RUNNER, HERE / "lower_bound/replay.py",
                                                   REPO / "lean-toolchain", REPO / "lake-manifest.json")],
        "reference_sources": [fingerprint(p) for p in reference_sources],
        "frozen_sources": dict(sorted(frozen_sources.items())), "modules_in_dependency_order": modules,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="Elaborate each local module in dependency order.")
    parser.add_argument("--check", action="store_true", help="Run the independent kernel checker on each local module.")
    args = parser.parse_args()
    ordered = dependencies()
    for requested, flags in ((args.build, []), (args.check, ["--checker"])):
        if requested:
            for module in ordered:
                subprocess.run([sys.executable, str(RUNNER), module, *flags], cwd=REPO, check=True)
    manifest = inventory(ordered)
    # Replace only a fully written manifest; interrupted runs preserve the last file.
    with tempfile.NamedTemporaryFile(mode="w", dir=HERE, prefix=".findany_manifest_",
                                     encoding="utf-8", newline="\n", delete=False) as out:
        temp = Path(out.name)
        try:
            json.dump(manifest, out, ensure_ascii=False, indent=2)
            out.write("\n")
        except BaseException:
            out.close()
            temp.unlink(missing_ok=True)
            raise
    try:
        os.replace(temp, MANIFEST)
    finally:
        temp.unlink(missing_ok=True)
    print(f"{MANIFEST}: {len(ordered)} local modules, complete={manifest['complete']}")
    for name in manifest["local_modules_with_missing_or_older_receipts"]:
        print(f"  missing or older receipt: {name}")


if __name__ == "__main__":
    main()
