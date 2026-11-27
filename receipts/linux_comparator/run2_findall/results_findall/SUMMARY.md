# GroverFindAll steps 15–20 — Linux `lake comparator` run (Paper #1 v1.0.0)

- **Finished (UTC):** 2026-11-26T23:07:50Z
- **Upstream pinned commit:** `a88de8ff65d78af564b2373088ca369dc95f6547`
- **LEAN_NUM_THREADS:** `1`; sandbox: `bwrap` (default), `--inadvisably-no-sandbox` not used
- **Job memory limit:** MemoryHigh `42949672960` B, MemoryMax `49392123904` B; whole-job cgroup peak **13.14 GB**
- **Repo restored to `pr-arcsin-366200` (d6595df), clean:** True
- **All numbered steps passed:** False

| Step | Exit | Status | Time (s) | max RSS (GB, time -v) | cgroup peak (GB) | anon max (GB, sampled) | OOM kills | Log |
|---|---:|---|---:|---:|---:|---:|---:|---|
| `pre_1_release_track2_sha256` | 0 | **PASS** | 1 | 0.01 | 0.03 | None | 0 | `pre_1_release_track2_sha256.log` |
| `pre_2_setup_track2_verification_branch` | 0 | **PASS** | 2 | 0.01 | 0.03 | None | 0 | `pre_2_setup_track2_verification_branch.log` |
| `pre_3_config_vs_upstream_GroverFindAllRelCost` | 0 | **PASS** | 0 | 0.01 | 0.03 | None | 0 | `pre_3_config_vs_upstream_GroverFindAllRelCost.log` |
| `15_findall_weak_lake_build` | 0 | **PASS** | 2916 | 4.61 | 4.86 | 4.3 | 0 | `15_findall_weak_lake_build.log` |
| `16_findall_weak_OFFICIAL_lake_comparator` | 1 | **FAIL** | 142 | 0.9 | 4.99 | 0.82 | 0 | `16_findall_weak_OFFICIAL_lake_comparator.log` |
| `17_findall_weak_leanchecker` | 0 | **PASS** | 44 | 2.89 | 3.93 | 0.2 | 0 | `17_findall_weak_leanchecker.log` |
| `17b_findall_weak_print_axioms` | 0 | **PASS** | 19 | 3.23 | 4.12 | 0.09 | 0 | `17b_findall_weak_print_axioms.log` |
| `18_findall_signonly_lake_build` | 0 | **PASS** | 2761 | 4.09 | 6.66 | 3.75 | 0 | `18_findall_signonly_lake_build.log` |
| `19_findall_signonly_OFFICIAL_lake_comparator` | 0 | **PASS** | 3402 | 1.02 | 13.14 | 8.93 | 0 | `19_findall_signonly_OFFICIAL_lake_comparator.log` |
| `20_findall_signonly_leanchecker` | 0 | **PASS** | 90 | 2.82 | 2.47 | 0.18 | 0 | `20_findall_signonly_leanchecker.log` |
| `20b_findall_signonly_print_axioms` | 0 | **PASS** | 20 | 3.2 | 2.7 | 0.21 | 0 | `20b_findall_signonly_print_axioms.log` |
| `post_restore_pr_branch` | 0 | **PASS** | 1 | 0.01 | 2.29 | None | 0 | `post_restore_pr_branch.log` |

max_rss = largest single process (GNU time -v, ru_maxrss); cgroup_peak = memory.peak of the whole job cgroup per step (anon + page cache incl. mmapped .olean files); sampled_anon_max = max of memory.stat anon sampled every 10 s.
