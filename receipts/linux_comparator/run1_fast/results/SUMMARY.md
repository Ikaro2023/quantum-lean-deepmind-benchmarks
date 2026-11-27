# Linux Comparator Verification Summary — Paper #1 (v1.0.0)

- **Timestamp (UTC):** 2026-11-26T19:08:55Z
- **Host:** <host> (`Linux 7.0.0-38-generic x86_64`, 8 CPUs, ~62 GB RAM)
- **Mode:** `fast`
- **Upstream pinned commit:** `a88de8ff65d78af564b2373088ca369dc95f6547`
- **Clean PR branch in `work/formal-quantum-computation`:** `pr-arcsin-366200` (`d6595dfd788eb4f719c41bb81a5a9e7296fff3c3`)

| Step | Exit Code | Status | Time (s) | Log |
|---|---:|---|---:|---|
| `00_release_sha256_verify` | 0 | **PASS** | 0 | `00_release_sha256_verify.log` |
| `01_lean_version_and_comparator_help` | 0 | **PASS** | 181 | `01_lean_version_and_comparator_help.log` |
| `02_arcsin_git_apply_patch` | 0 | **PASS** | 0 | `02_arcsin_git_apply_patch.log` |
| `03_lake_cache_get` | 0 | **PASS** | 625 | `03_lake_cache_get.log` |
| `04_arcsin_lake_build` | 0 | **PASS** | 1244 | `04_arcsin_lake_build.log` |
| `05_arcsin_OFFICIAL_lake_comparator` | 0 | **PASS** | 1426 | `05_arcsin_OFFICIAL_lake_comparator.log` |
| `06_arcsin_leanchecker` | 0 | **PASS** | 779 | `06_arcsin_leanchecker.log` |
| `07_arcsin_compare_frozen` | 0 | **PASS** | 56 | `07_arcsin_compare_frozen.log` |
| `08_arcsin_exact_and_nonvacuity` | 0 | **PASS** | 180 | `08_arcsin_exact_and_nonvacuity.log` |
| `09_upstream_lake_test` | 0 | **PASS** | 312 | `09_upstream_lake_test.log` |
| `10_findany_lake_build` | 0 | **PASS** | 158 | `10_findany_lake_build.log` |
| `11_findany_OFFICIAL_lake_comparator_TighterFindAny` | 0 | **PASS** | 330 | `11_findany_OFFICIAL_lake_comparator_TighterFindAny.log` |
| `12_findany_leanchecker_LowerBound` | 0 | **PASS** | 62 | `12_findany_leanchecker_LowerBound.log` |
| `13_findany_leanchecker_TighterFindAny` | 0 | **PASS** | 58 | `13_findany_leanchecker_TighterFindAny.log` |
| `14_findany_print_axioms` | 0 | **PASS** | 19 | `14_findany_print_axioms.log` |
