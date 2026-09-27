# TASK-012: size the harness observer's latency-histogram FIFO for the latency sweep

**Status:** OPEN — filed 2026-09-27 from the observer campaign (perf report v1.2 section 7.5).

`rapids_char_harness.sv` instantiates `axi4_intf_master_observer` with
`HIST_MAX_OUTSTANDING(8)`: eight command timestamps per channel in the
`axi_perf_latency_hist` FIFO. On the memory-latency sweep (`RESP_DELAY` >= 48 cycles)
the source read engine keeps more than eight ARs in flight per channel, the FIFO
overflows, and the observer reports it honestly -- `OBS_STICKY.HIST_SAMPLE_LOST = 1`
on every row from 48 to 512 cycles (`genesys_obs_E.json`, `observer_sticky.axi`).
The utilization counters are unaffected (the sweep's knee is measured); only the
latency histograms are from a subset of transactions there, which is why the report's
latency means for those rows carry a caveat.

Do: raise `HIST_MAX_OUTSTANDING` on `u_obs_axi` (32 covers the ~20 beats in flight per
channel the sweep measured, with margin), rebuild `USE_OBSERVERS=1`, re-run phase E
(`--suite-delay 0,8,16,32,48,64,96,128,192,256,384,512`) and confirm `OBS_STICKY` reads 0
on every row; then drop the caveat from 7.5. Cost is the FIFO flops only; check the
post-route WNS stays positive (v3 was +1.317 ns).

---

**CLOSED 2026-09-27.** `u_obs_axi` in `rapids_char_harness.sv` now sets
`HIST_MAX_OUTSTANDING (32)`. Bitstream v4 (`USE_OBSERVERS=1`, built 13:52,
post-route WNS +0.224 ns, still positive) programmed and phase E re-run
(`--suite-delay 0,8,16,32,48,64,96,128,192,256,384,512`, 8 ch x 1024 beats):
12/12 pass, `OBS_STICKY` = 0 on every row for both observers
(`genesys_obs_E.json`, `observer_sticky.axi` and `.axis`). Utilization and
bandwidth columns identical to the v1.2 run; the latency columns moved to the
full-population log2-bin midpoints (192/384/768 where the sampled subset had
read 170/264-320/530). Report re-issued as `RAPIDS_Char_Perf_v1.3` with the
7.5 caveat replaced by the measurement.
