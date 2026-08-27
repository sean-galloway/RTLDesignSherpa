# Board A/B: runtime page policy OPEN vs CLOSE (2026-07-08)

Nexys A7, MT47H64M16 x16, 100 MHz, harness UART /dev/ttyUSB2. **Runtime-policy
bitstream** (rebuilt from commit b8faf9fe; routed WNS = +0.419 ns, all timing met).
Host: `build-perf/host/compare_page_policy.py`. Board DFI cfg: t_phy_wrlat=0,
rddata_delay=8, rd_phase=0, t_rddata_en=6. Leveling clean (bitslip 0, tap 5, eye 0..11).

## Headline — the committed page-policy fix works on silicon

`incremental` (contiguous streaming, same-row), bl=16:

| policy | wr MB/s | rd MB/s | cyc/beat (rd) |
|--------|--------:|--------:|--------------:|
| CLOSE  |    12.7 |    12.7 |          62.8 |
| OPEN   |    44.3 |   112.0 |           7.1 |

**Read bandwidth 8.80x (12.7 -> 112.0 MB/s); 62.8 -> 7.1 cyc/beat.** Reproduced
across 3 runs (txn 250 / 1000 / 2000). Writes 3.5x (12.7 -> 44.3).

Before this fix the page-policy CSR was compile-time-inert, so the 2026-07-08
baseline char showed a FLAT 12.7 MB/s under every policy. The CLOSE column here
reproduces that 12.7 / ~63-cyc baseline exactly — which validates the meter
methodology — and OPEN is the same-row batching the fix unlocked (skip ACT+PRE on
every beat after the first).

## Caveats / open bugs (not policy-related)
- **Engine wedge** ("read/write engine did not complete") trips even at 4000 beats
  — the known read-CAM ~4790 ceiling + a write-side wedge. The perf meter captures
  the active-transfer window so the *rate* is trustworthy (self-consistent: 112/12.7
  = 8.8x == 62.8/7.1 cyc/beat), but runs don't finish cleanly -> `ok=False`.
  Fix tracked in PERF_FIX_PLAN.md at the time (widen rd_cmd_cam counter +
  retire path); that plan LANDED and its doc was deleted 2026-08-27 with the
  FSM design it patched -- the current path is
  `rtl/macro/pumice_axi4_ifc.sv` + `rtl/fub/pumice_rd_cmd_cam.sv`.
- **row_major** wedges almost immediately (every burst row-miss -> hist total 0-1);
  needs the wedge fix before it can be characterized.
- Intermittent 1-3 beat mismatches at scale (known; clean at small counts).

## Interpretation vs the remaining perf work
OPEN at 7.1 cyc/beat is the single-op FSM streaming a row (S_IDLE->NEED_RDWR->DONE
->S_IDLE + real CAS). The residual gap to ~1 cyc/beat + random/multi-bank
parallelism is exactly what the issue-per-clock scheduler rewrite targets
(SCHEDULER_ANATOMY.md at the time; that rewrite LANDED and the doc was deleted
2026-08-27 -- current design: `rtl/PUMICE_MEM_CMD_SCHEDULER_UARCH.md`).
This A/B confirms the page-policy lever alone recovers
most of the *streaming* loss; the FSM serialization is the next lever.
