"""Pinned toolchain and a project-local, append-only process receipt per invocation."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

PROJECT = Path(__file__).resolve().parent
ROOT = PROJECT.parent
REPO = ROOT / "work_repo"
LEAN = PROJECT / "lean"
REPLAY = LEAN / "Track2Weak" / "replay"
LIB = REPO / ".lake/build/lib/lean"
BIN = ROOT / ".elan/toolchains/leanprover--lean4---v4.35.0/bin"
RECEIPTS = PROJECT / "receipts"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def environment(extra=()):
    vendor = LEAN / "Track2Weak/vendor"
    local_dependencies = vendor if (vendor / "Track2Grover").is_dir() else REPO
    libraries = [*extra, LEAN, LIB, *sorted((REPO/".lake/packages").glob("*/.lake/build/lib/lean")), local_dependencies]
    return dict(os.environ, ELAN_HOME=str(ROOT/".elan"), LEAN_PATH=os.pathsep.join(map(str,libraries)),
                PATH=str(BIN)+os.pathsep+os.environ["PATH"], LEAN_NUM_THREADS="1",
                PYTHONDONTWRITEBYTECODE="1", PYTHONIOENCODING="utf-8")


def record(name, command, cwd=LEAN, env=None, stdin=None):
    RECEIPTS.mkdir(exist_ok=True)
    when = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    base = RECEIPTS / (when + "_" + name)
    log = Path(str(base) + ".log")
    start = time.monotonic()
    env = environment() if env is None else env
    with log.open("wb") as out:
        result = subprocess.run(list(map(str,command)), cwd=cwd, env=env, input=stdin, stdout=out, stderr=subprocess.STDOUT)
    receipt = dict(command=list(map(str,command)), cwd=str(cwd), lean_path=env["LEAN_PATH"],
                   utc_start=when, seconds=round(time.monotonic()-start,3), exit=result.returncode,
                   output=log.name, output_sha256=digest(log))
    Path(str(base)+".json").write_text(json.dumps(receipt,indent=2)+"\n", encoding="utf-8")
    return result.returncode, log


def build(mod):
    path = Path(*mod.split(".")).with_suffix(".lean")
    if not mod.startswith("Track2Weak.") or not (LEAN/path).is_file():
        raise ValueError(mod)
    return record(mod+"_lean", [BIN/"lean.exe","-j1","-o",path.with_suffix(".olean"),path])


if __name__ == "__main__":
    mod = sys.argv[1]
    if len(sys.argv)>2 and sys.argv[2]=="--check":
        code, log = record(mod+"_checker",[BIN/"leanchecker.exe","--verbose",mod])
    else:
        code, log = build(mod)
    print(log, "exit",code)
    if code:
        print(log.read_text(encoding="utf-8",errors="replace")[-8000:])
    sys.exit(code)
