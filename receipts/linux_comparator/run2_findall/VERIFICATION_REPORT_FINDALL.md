# Independent Linux verification — Paper #1 (v1.0.0), GroverFindAll steps 15–20

*Report created 2026-11-26 23:25 UTC (2026-11-27 00:25 CET). Main run 2026-11-26 20:31:13 – 23:07:50 UTC;
separate fix run 22:06:50 – 23:07:52 UTC.*

## Result

| Solution module | Official `lake comparator` (bwrap sandbox) | `leanchecker` | `#print axioms` |
|---|---|---|---|
| `Track2Grover.FindAll` (sign-only, `27,014,193,664 / 10^12`) | **PASS** — *"Lean default kernel accepts the solution / Your solution is okay!"* | PASS | standard only |
| `Track2Weak.FindAllWeak` (weak filters, `26,768,771,052 / 10^12`) **as released** | **FAIL** — `error: Const does not match between challenge and target 'QuantumComputation.Specs.groverFindAllProgram'` | PASS | standard only |
| `Track2Weak.FindAllWeak` with a one-keyword fix (see below), separate copy | **PASS** — *"Lean default kernel accepts the solution / Your solution is okay!"* | PASS | standard only |

"Standard only" = `propext`, `Classical.choice`, `Quot.sound`; `groverFindAllCells_nonempty` uses no axioms.
No step ran out of memory (0 OOM kills); the highest whole-job memory peak was 13.14 GB (step 19).

## Main run: steps 15–20 (as released, no changes)

Inputs: `paper1_linux_comparator_bundle_v1.0.0.zip` (SHA-256 `28caa075d65607081ac84d5c27380ab7bbbdb66e92ea4e592144aa8eacf95a26`);
`release/SHA256SUMS.txt` 381/381 OK (273 of them under `lean/track2_weak/` and `lean/track2_grover/`).
Upstream `google-deepmind/formal-quantum-computation` `discoveries` = `a88de8ff65d78af564b2373088ca369dc95f6547`,
staged exactly like `run_linux_comparator.sh --all` (temporary branch `track2-verification`, `Track2Grover/` + `Track2Weak/`
copied from `release/lean/`, two `[[lean_lib]]` blocks appended to `lakefile.toml`), reusing the existing `.lake` cache.

| Step | Exit | Status | Wall time | max RSS of one process (`time -v`) | whole-job cgroup peak | OOM |
|---|---:|---|---:|---:|---:|---:|
| 15 `lake build +Track2Weak.FindAllWeak +Track2Weak.FiniteFromCutoff` | 0 | PASS | 48 min 36 s | 4.61 GB | 4.86 GB | 0 |
| **16 `lake comparator --config GroverFindAll_FindAllWeak.json`** | **1** | **FAIL** | 2 min 22 s | 0.90 GB | 4.99 GB | 0 |
| 17 `lake env leanchecker --verbose Track2Weak.FindAllWeak` | 0 | PASS | 44 s | 2.89 GB | 3.93 GB | 0 |
| 17b `#print axioms` — 4 public `groverFindAll*` theorems + `groverFindAll_cost_from_80000` | 0 | PASS | 19 s | 3.23 GB | 4.12 GB | 0 |
| 18 `lake build +Track2Grover.FindAll` | 0 | PASS | 46 min 01 s | 4.09 GB | 6.66 GB | 0 |
| **19 `lake comparator --config GroverFindAll_SignOnly.json`** | **0** | **PASS** | 56 min 42 s | 1.02 GB | 13.14 GB | 0 |
| 20 `lake env leanchecker --verbose Track2Grover.FindAll` | 0 | PASS | 1 min 30 s | 2.82 GB | 2.47 GB | 0 |
| 20b `#print axioms` — 4 public `groverFindAll*` theorems of `Track2Grover.FindAll` | 0 | PASS | 20 s | 3.20 GB | 2.70 GB | 0 |

Before step 15: both FindAll configs are key-for-key identical to the upstream
`QuantumComputationSpecs/ChallengeJsons/Algorithms/GroverFindAllRelCost.json` except `solution_module`
(upstream `QuantumComputationDiscoveries.Algorithms.GroverFindAll`) — `pre_3_config_vs_upstream_GroverFindAllRelCost.log`.
After step 20 the repository was restored to `pr-arcsin-366200` = `d6595dfd788eb4f719c41bb81a5a9e7296fff3c3`, clean working tree
(`post_restore_pr_branch.log`).

Theorem names printed by `#print axioms` (17b): `QuantumComputation.Specs.groverFindAll_correctness`, `groverFindAllCells_nonempty`,
`groverFindAllCells_mem_grid`, `groverFindAll_rel_cost` and `QuantumComputation.Specs.groverFindAll_cost_from_80000`
(this is the full name declared in `Track2Weak/FiniteFromCutoff.lean`; there is no `Track2Weak.FiniteFromCutoff.groverFindAll_cost_from_80000`).

### Step 16 — exact error and cause

```
Build completed successfully (3130 jobs).
error: Const does not match between challenge and target 'QuantumComputation.Specs.groverFindAllProgram'
```

The sandboxed build and both exports succeeded; the failure is in the comparison phase
(`Lake/Check/Compare.lean`, Lean 4.35.0). A declaration that is *not* listed in `definition_names`/`theorem_names` but is
reachable from them — here `groverFindAllProgram` — must be identical in challenge and solution, as a whole `ConstantInfo`,
including its `ReducibilityHints`. Read-only diagnostics (`diag_findall/`) show:

| constant | challenge (`QuantumComputationSpecs.Algorithms.Grover`) | released `Track2Weak.FindAllWeak` |
|---|---|---|
| `groverFindAllProgram` | `regular(37)`, value hash `4143947326` | **`regular(46)`**, value hash `4143947326` (same type and value) |
| `groverFindAllCircuit` (definition target, type-only check) | `regular(7)` (`:= sorry`) | `regular(45)` |
| `groverFindAllQubits` (definition target) | `regular(2)` | `regular(44)` |
| `weakChosenBatch` (solution-only helper) | — | `regular(43)` |

So the definition text of `groverFindAllProgram` is the same, but its definitional height is inherited from the much deeper
`weakChosenBatch → groverFindAllQubits → groverFindAllCircuit` chain. The upstream discovery has the same issue and
works around it explicitly (`QuantumComputationDiscoveries/Algorithms/Grover/Solution/StageLoop.lean`:
*"Marked `abbrev` so `groverFindAllProgram` retains `ReducibilityHints.regular(37)`."*).
`Track2Grover.FindAll` does not hit the problem (step 19 PASS).

The full list of the 41 challenge constants with hints and hashes, as seen from both modules, is in
`diag_findall/challenge_vs_solution_constants.txt`. The other differences are definition targets (type-only check) or
FindAny declarations already accepted by the comparator for `TighterFindAny` in the earlier run.

## Fix run (separate copy, sandbox unchanged)

To check that this is the *only* obstacle, step 15–17b were repeated on a separate `rsync` copy of the same repository and
`.lake` cache (the main run was not touched), with exactly one change:

```diff
--- a/Track2Weak/FindAllWeak.lean
+++ b/Track2Weak/FindAllWeak.lean
@@ -27,7 +27,7 @@
   exact ⟨Finset.mem_image.mpr ⟨10, by decide, by decide⟩,
     Finset.mem_image.mpr ⟨9, by decide, by decide⟩⟩
 
-noncomputable def weakChosenBatch (n : ℕ) :=
+noncomputable abbrev weakChosenBatch (n : ℕ) :=
   Track2Weak.routedBatch res Track2Weak.weakQubits 80000
     (Track2Weak.weakTrial res Track2Weak.Cert.certRows) n
```

(released file SHA-256 `d210ff50…ac929`, fixed file `8ba16994…bdd9a`; config `GroverFindAll_FindAllWeak.json` unchanged.)

| Step | Exit | Status | Wall time | max RSS (`time -v`) | cgroup peak | OOM |
|---|---:|---|---:|---:|---:|---:|
| fix15 `lake build +Track2Weak.FindAllWeak +Track2Weak.FiniteFromCutoff` (only these 2 modules rebuilt) | 0 | PASS | 1 min 46 s | 1.46 GB | 1.58 GB | 0 |
| fix15b reducibility hints: `weakChosenBatch` `abbrev`, `groverFindAllQubits` `regular(1)`, `groverFindAllCircuit` `regular(7)`, **`groverFindAllProgram` `regular(37)`** | 0 | PASS | 51 s | 3.19 GB | 2.91 GB | 0 |
| **fix16 `lake comparator --config GroverFindAll_FindAllWeak.json`** | **0** | **PASS** | 33 min 27 s | 0.88 GB | 6.57 GB | 0 |
| fix17 `lake env leanchecker --verbose Track2Weak.FindAllWeak` | 0 | PASS | 1 min 49 s | 2.81 GB | 3.60 GB | 0 |
| fix17b `#print axioms` (same 5 theorems) | 0 | PASS — standard only | 20 s | 3.20 GB | 3.78 GB | 0 |

Suggested change for the release / Issue: apply the diff above (or an equivalent `abbrev`/`@[reducible]` on the helper
chain), and state the comparator result for both FindAll modules instead of "interface comparisons".

## Threads and memory

- `LEAN_NUM_THREADS=1` was exported for all steps. It is effective for `lake build`, `leanchecker` and `#print axioms`
  (every sampled `lean`/`leanchecker` process carried it; one `lean` process at a time).
- `lake comparator` starts its build/export/kernel children inside `bwrap --clearenv` and passes only `PATH`, `HOME`,
  `LEAN_ABORT_ON_PANIC` (and `LEAN_PATH` for the exporter) — see `Lake/CLI/Check.lean`. So inside the comparator sandbox
  `LEAN_NUM_THREADS` is **unset** (recorded in `env_samples.tsv`). This is the tool's behaviour and was not changed.
- Memory columns: *max RSS* = largest single process (GNU `time -v`); *cgroup peak* = `memory.peak` of the job's cgroup per
  step (anonymous memory + page cache, incl. memory-mapped `.olean` files); `mem_samples.tsv` has 10-second samples
  (anonymous memory peaked at 8.9 GB in step 19, where the kernel checker `leanchecker` reached 8.2 GB RSS).
  The README's "~28 GB peak" was not reached on this setup.
- Most of the comparator time is the kernel check of the exported environment ("Running Lean default kernel on solution"):
  step 19 ≈ 54 min, fix16 ≈ 31 min, single-threaded.

## Environment

64-bit Linux (Ubuntu 26.04.1 LTS, kernel 7.0.0-38-generic, x86_64), 62 GB RAM, no swap. Job run as a transient systemd unit:
8 CPUs (`CPUQuota=800%`), `MemoryHigh=40G`, `MemoryMax=46G`, `MemorySwapMax=0`, `Nice=10`; fix run `MemoryMax=16G`, 4 CPUs.
Lean 4.35.0 (`eb6cafb7`), Lake 5.0.0, elan 4.4.0, bubblewrap 0.11.1. `--inadvisably-no-sandbox` was **not** used anywhere.

## Package contents

- `results_findall/` — main run: one `.log` + `.time.txt` (GNU `time -v`) per step, `steps.tsv`, `SUMMARY.md`, `SUMMARY.json`,
  `environment.txt`, `mem_samples.tsv`, `env_samples.tsv`, `run_findall.log`, the two `print_axioms_*.lean` inputs, `config_check.py`.
- `fix16/results_fix16/` — fix run: same per-step files, `FindAllWeak.fix.diff`, `FindAllWeak.lean.orig`, `git_state.txt`, `SUMMARY.json`.
- `diag_findall/` — read-only Lean diagnostics (reducibility hints, all 41 challenge constants compared).
- `tools/` — the runner scripts used (`findall_runner.py`, `fix16_runner.py`, `prep.sh`, `prep.log`).
- `SHA256SUMS.txt` — checksums of every file in this package.

**Privacy edit:** the internal host name, IP addresses, home-directory user name and numeric user id were replaced by
`<host>`, `<ip>`, `<user>`, `<uid>`. No other content was changed; `RESULT_SHA256SUMS.txt` files were computed after this edit.
