import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

SRC = Path(r"C:\Users\OFFICE3\.gemini\antigravity\scratch\quantum_lean_breakthrough_20261125")
REL = Path(r"C:\Users\OFFICE3\.gemini\antigravity\scratch\paper1_quantum_deepmind_20261125\github_zenodo_release")
REPO = SRC / "work_repo"
BIN = SRC / ".elan/toolchains/leanprover--lean4---v4.35.0/bin"
OUT = REL / "receipts/external_checkers"
OUT.mkdir(parents=True, exist_ok=True)
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def sha256(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for ch in iter(lambda: f.read(1 << 20), b""):
            h.update(ch)
    return h.hexdigest()


packages = sorted((REPO / ".lake/packages").glob("*/.lake/build/lib/lean"))
base_libs = [REPO / ".lake/build/lib/lean", *packages, REPO]
env = dict(os.environ, ELAN_HOME=str(SRC / ".elan"), LEAN_NUM_THREADS="1")
env["PATH"] = str(BIN) + os.pathsep + env["PATH"]


def check_suite(name, extra_libs, modules, decls):
    env_run = dict(env, LEAN_PATH=os.pathsep.join(map(str, [*extra_libs, *base_libs])))
    rec = {
        "name": name,
        "utc_start": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "modules": modules,
        "declarations": decls,
        "permitted_axioms": AXIOMS,
        "tools_sha256": {t: sha256(BIN / f"{t}.exe") for t in ("leanexport", "nanoda_bin", "con-ron")},
    }
    with tempfile.TemporaryDirectory() as td_str:
        td = Path(td_str)
        exp = td / "export.ndjson"
        t0 = time.monotonic()
        with exp.open("wb") as so, (td / "exp.err").open("wb") as se:
            rc = subprocess.run([str(BIN / "leanexport.exe"), *modules, "--", *decls],
                                cwd=str(td), env=env_run, stdout=so, stderr=se).returncode
        dt = round(time.monotonic() - t0, 2)
        if rc != 0:
            err = (td / "exp.err").read_text(encoding="utf-8", errors="replace")[-800:]
            raise RuntimeError(f"export failed {name}: rc={rc}\n{err}")
        rec["export"] = {"exit": rc, "seconds": dt, "bytes": exp.stat().st_size, "sha256": sha256(exp)}

        cfg = {
            "export_file_path": str(exp),
            "use_stdin": False,
            "permitted_axioms": AXIOMS,
            "unpermitted_axiom_hard_error": True,
            "nat_extension": True,
            "string_extension": True,
            "pp_declars": decls,
            "pp_to_stdout": True,
            "print_success_message": True,
        }
        (td / "nanoda.json").write_text(json.dumps(cfg, indent=2), encoding="utf-8")
        t0 = time.monotonic()
        with (td / "nan.out").open("wb") as so, (td / "nan.err").open("wb") as se:
            rc_n = subprocess.run([str(BIN / "nanoda_bin.exe"), str(td / "nanoda.json")],
                                  cwd=str(td), env=env_run, stdout=so, stderr=se).returncode
        dt_n = round(time.monotonic() - t0, 2)
        nout = (td / "nan.out").read_text(encoding="utf-8", errors="replace")
        mn = re.search(r"Checked (\d+) declarations with no errors", nout)
        ax_seen = sorted({a.rstrip(".") for a in re.findall(r"^axiom ([^\s{:]+)", nout, re.MULTILINE)})
        rec["nanoda"] = {
            "version": "0.4.19",
            "exit": rc_n,
            "seconds": dt_n,
            "checked_declarations": int(mn[1]) if mn else None,
            "axioms_printed": ax_seen,
        }

        t0 = time.monotonic()
        with (td / "con.out").open("wb") as so, (td / "con.err").open("wb") as se:
            rc_c = subprocess.run([str(BIN / "con-ron.exe"), "--verified", "--jobs=4", str(exp)],
                                  cwd=str(td), env=env_run, stdout=so, stderr=se).returncode
        dt_c = round(time.monotonic() - t0, 2)
        cout = (td / "con.out").read_text(encoding="utf-8", errors="replace")
        mc = re.search(r"con-ron: accepted (\d+) declarations \(--verified\)", cout)
        rec["con_ron"] = {
            "mode": "--verified",
            "exit": rc_c,
            "seconds": dt_c,
            "accepted_declarations": int(mc[1]) if mc else None,
        }

        rec["ok"] = bool(rc == 0 and rc_n == 0 and mn and rc_c == 0 and mc)
        out_path = OUT / f"external_{name}.json"
        out_path.write_text(json.dumps(rec, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(
            f"{name}: export={dt}s | nanoda=rc{rc_n} ({rec['nanoda']['checked_declarations']} decls, {dt_n}s, ax={ax_seen})"
            f" | con-ron=rc{rc_c} ({rec['con_ron']['accepted_declarations']} decls, {dt_c}s)",
            flush=True,
        )
        assert rec["ok"], rec


check_suite(
    "findany_lowerbound",
    [],
    ["Track2Grover.FindAnyLowerBound"],
    [
        "Track2Grover.FindAnyLowerBound.finite",
        "Track2Grover.FindAnyLowerBound.actual_expected_rounds",
        "Track2Grover.FindAnyLowerBound.asymptotic_real",
        "Track2Grover.FindAnyLowerBound.no_smaller_rational",
        "Track2Grover.FindAnyLowerBound.exact_infimum",
    ],
)
check_suite(
    "findany_tighter",
    [],
    ["Track2Grover.TighterFindAny"],
    [
        "QuantumComputation.Specs.groverFindAnyCells_nonempty",
        "QuantumComputation.Specs.groverFindAnyCells_mem_grid",
        "QuantumComputation.Specs.groverFindAny_correctness",
        "QuantumComputation.Specs.groverFindAny_rel_cost",
    ],
)
