# TASK-025: one module has no test coverage (was seven -- five of those claims were wrong)

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **TASK-075** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.

**Priority:** P3.
**Status:** CLOSED 2026-09-15. Verified by running the coverage it claims:
`val/amba/test_cg_peer_ready.py` is 13 passed (82.7s) and `apb4_master_cg` is
one of its collected cells, so the one real gap this task found is genuinely
covered. The other five "no coverage" claims were mine and were already
corrected. Nothing outstanding.
Was: open 2026-09-02, corrected. qc round_38 disputed my "no coverage"
claim on the ECC pair and was RIGHT.

**What I got wrong.** I searched for `val/**/test_<module>.py` and for parents
in the RTL instantiation graph. Neither finds a test that names the module in a
Python string and builds its own wrapper. Re-checked by searching test SOURCES
for each module name:

| Module | Actually covered by |
|---|---|
| `dataint_ecc_hamming_encode_secded` | `test_dataint_ecc_hamming_secded.py` -- builds `ecc_secded_wrapper` around encoder+decoder, 5 tests |
| `dataint_ecc_hamming_decode_secded` | same |
| `sdpram_slave_axi4_axi4` | `test_sdpram_slave.py` |
| `axis4_master_injector` | `test_axis4_pattern_pair.py` |
| `axis4_slave_pattern_check` | same |

Both ECC modules were the P2 items in the original filing. They were covered
all along, and five of the seven pages carried a false "no test coverage"
warning that I put there. All five corrected.

**Fixed while checking:** `apb4_master_cg` had no coverage, and the reason was
that it had **no filelist** -- nothing could build it. Created
`rtl/amba/filelists/apb4_master_cg.f` and added it to
`val/amba/test_cg_peer_ready.py`, which needed per-DUT clock names because the
APB family uses `pclk`/`presetn` rather than `aclk`/`aresetn`. It now passes
both gating assertions.

**Genuinely uncovered, still open:**

| Module | Note |
|---|---|
| `monbus_axi4_axi4_group` | No test names it and no filelist-reachable parent has one. The axil/axil variant IS tested, so the gap is this variant only. |

**Method for next time:** a module is covered if any file under `val/` names
it, not merely if `test_<module>.py` exists. Tests that synthesise a wrapper
are invisible to the filename convention.
