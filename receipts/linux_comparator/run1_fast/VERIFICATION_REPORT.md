# Independent Linux verification — Paper #1 (v1.0.0)

*Report created 2026-11-26 19:35 UTC (20:35 CET). Run executed 2026-11-26 17:38:12 – 19:08:55 UTC.*

## Result

`./run_linux_comparator.sh` (default `--fast` mode) from `paper1_linux_comparator_bundle_v1.0.0.zip`
(SHA-256 `28caa075d65607081ac84d5c27380ab7bbbdb66e92ea4e592144aa8eacf95a26`) finished with
**15 / 15 steps PASS** (exit code 0 for every step, none skipped).

| Step | Result | Time |
|---|---|---:|
| 00 release `SHA256SUMS.txt` (381 files) | PASS | 0 s |
| 01 Lean 4.35.0 + `lake comparator` available | PASS | 181 s |
| 02 `git apply arcsin_366200.patch` on `a88de8ff` (5 files) | PASS | 0 s |
| 03 `lake exe cache get` | PASS | 625 s |
| 04 `lake build` Specs + Discoveries Arcsin | PASS | 1 244 s |
| **05 official `lake comparator` — `ArcsinK25ConstCost.json`** | **PASS** — *"Lean default kernel accepts the solution / Your solution is okay!"* | 1 426 s |
| 06 `leanchecker --verbose` Arcsin (16 solution modules replayed) | PASS | 779 s |
| 07 `CompareFrozen.lean` | PASS — `PASS 25 challenge declarations` | 56 s |
| 08 `ExactCount` / `ExactPublic` / `DisjointWitness` + `leanchecker` | PASS | 180 s |
| 09 upstream `lake test` | PASS — *"All 7 challenge configurations are consistent with the specifications."* | 312 s |
| 10 `lake build` Grover spec + `FindAnyLowerBound` + `TighterFindAny` | PASS | 158 s |
| **11 official `lake comparator` — GroverFindAny ← `Track2Grover.TighterFindAny`** | **PASS** — *"Lean default kernel accepts the solution / Your solution is okay!"* | 330 s |
| 12 `leanchecker` `Track2Grover.FindAnyLowerBound` | PASS | 62 s |
| 13 `leanchecker` `Track2Grover.TighterFindAny` | PASS | 58 s |
| 14 `#print axioms` — 5 `FindAnyLowerBound` theorems | PASS — only `propext`, `Classical.choice`, `Quot.sound` | 19 s |

## What exactly was checked

- **Upstream:** `google-deepmind/formal-quantum-computation`, branch `discoveries` = `a88de8ff65d78af564b2373088ca369dc95f6547`
  (confirmed by `git ls-remote` at run time; the only remote branches were `main` = `489edc70` and `discoveries` = `a88de8ff`).
- **Step 05 used the upstream challenge file verbatim**: `QuantumComputationSpecs/ChallengeJsons/Primitives/ArcsinK25ConstCost.json`
  (theorems `arcsin_correctness`, `arcsin_k25_const_cost`; definitions `arcsinAncillas`, `arcsinProgram`, `arcsinK25ConstCost`;
  permitted axioms `propext`, `Quot.sound`, `Classical.choice`; `allow_disproofs = false`).
  The spec leaves `arcsinK25ConstCost := sorry`; the solution sets it to **366200** (pinned discovery: 369800; T-count 3698 → 3662).
- **Step 11** used `comparator_configs/GroverFindAny_TighterFindAny.json`, which is key-for-key identical to the upstream
  `QuantumComputationSpecs/ChallengeJsons/Algorithms/GroverFindAnyRelCost.json` except `solution_module`
  (`Track2Grover.TighterFindAny` instead of `QuantumComputationDiscoveries.Algorithms.GroverFindAny`).
- `lake comparator` ran **inside its `bwrap` sandbox** (bubblewrap 0.11.1); `--inadvisably-no-sandbox` was **not** used.
- **PR branch** `pr-arcsin-366200` = commit `d6595dfd788eb4f719c41bb81a5a9e7296fff3c3` on top of `a88de8ff`.
  Its tree is identical to applying `release/patches/arcsin_366200.patch` on `a88de8ff` (checked with a separate worktree).
  `pr-arcsin-366200_d6595df.patch` in this package is that commit as `git format-patch` output.
- Toolchain, dependency pins and both upstream challenge configs: `toolchain_and_configs.txt`.

## Notes for the PR / Issue texts

- `deepmind_pr_and_issue/PR_ARCSIN_366200.md` currently says *"the upstream `lake comparator` over `ChallengeJsons` was not run locally"*.
  That sentence can now be replaced, e.g.: *"The official `lake comparator --config QuantumComputationSpecs/ChallengeJsons/Primitives/ArcsinK25ConstCost.json`
  (Lean 4.35.0, bwrap sandbox) accepts the solution ("Lean default kernel accepts the solution"); `lake test` reports all 7 challenge configurations consistent."*
- **TighterFindAny:** the improvement over the pinned constant is ≈ 1.59 × 10⁻²¹ (same circuit, tighter rational bound for π).
  The comparator confirms it, but it is a numerical-precision refinement, not a new algorithm.
- **FindAnyLowerBound** (`exact_infimum`, `1/2 + 1/π` over the full `OracleDynamicCircuit` class): no `sorry`, standard axioms only,
  kernel replay passes. There is no frozen upstream challenge for a lower bound, so `lake comparator` cannot check the *statement*;
  whether the theorem says what the Issue claims has to be judged by reviewers (it is stated over the upstream
  `AvgOracleCostBound` / `groverParallelMarkingOracle` / `vanillaFindAnyCost` definitions).
- **Not run:** `--with-findall` (Track 2b weak filter) and `--with-signonly`.

## Environment

64-bit Linux (Ubuntu 26.04.1 LTS, kernel 7.0.0-38-generic, x86_64), 8 CPUs available to the job, 62 GB RAM
(job limited to 22 GB; peak observed ≈ 12 GB). Lean 4.35.0 (`eb6cafb7`), Lake 5.0.0, elan 4.4.0.

## Package contents

- `results/` — all step logs, `SUMMARY.md`, `SUMMARY.json`, `steps.tsv`, `environment.txt`, `upstream_head.txt`, `pr_arcsin_commit.txt`.
- `run_full.log` — complete console output of the run.
- `pr-arcsin-366200_d6595df.patch` — the PR commit (`git format-patch`).
- `toolchain_and_configs.txt` — versions, `lake-manifest.json` pins, upstream challenge configs, PR commit metadata.
- `SHA256SUMS.txt` — checksums of every file in this package.

**Privacy edit:** the internal host name, IP addresses and home-directory user name were replaced by `<host>`, `<ip>`, `<user>`
in `run_full.log`, `results/environment.txt`, `results/SUMMARY.md`, `results/01_*.log`, `results/08_*.log`.
No other content was changed. `results/RESULT_SHA256SUMS.txt` was recomputed after this edit. The original receipts archive
`comparator_results_20261126_190855Z.zip` (SHA-256 `268271033aab00cfa0430a7f7dbc99fbb35597ffc5bc9588a75d58d9b9e7fc7d`) is kept by the verifier.
