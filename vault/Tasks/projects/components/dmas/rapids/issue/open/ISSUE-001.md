# ISSUE-001: after TASK-082, snkGB/s reports ingress latency, not datapath rate
> **Was `TASK-086` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Priority:** Medium -- the number is not wrong, it answers a different question
than its column heading implies. **Status:** open 2026-09-23.

`_min_util` takes the MINIMUM utilisation across a direction's interfaces, on the
principle that a direction is limited by its slowest interface. Since TASK-082
gave `s_axis` its own window opening at ARM, `sin` is that minimum on 7 of 8
board rows -- so the reported sink throughput is now set by ingress utilisation,
which includes the arm-to-busy dead zone.

Measured on the board (8 channels, bpoff, seed default):

```
  beats/ch  total   sin prod  sin starv  sin util  wr util   snkGB/s from sin
         1      8          8        204     0.038    0.381       0.24
         4     32         32        197     0.140    0.842       0.89
        16    128        128        197     0.394    0.955       2.52
        64    512        512        205     0.714    0.973       4.57
       256   2048       2048        197     0.912    0.997       5.84
```

`sin util == prod/(prod+starv)` holds to four decimals on every row, and
`starv` is a CONSTANT ~197-205 cycles regardless of transfer size. So the column
is dilution-limited: pessimistic for short transfers, asymptotically correct for
long ones. `wr` -- the actual sink datapath -- reads 0.381..0.997 over the same
sweep.

Consequence: short-transfer sink numbers are NOT comparable with anything
recorded before TASK-082. Long transfers converge, which is why the 4096-beat
peak (12.75 GB/s full-duplex) is unaffected.

**Do:**
- [ ] Decide what `snkGB/s` should mean and make the heading match. Options:
      report per-interface instead of a single bottleneck figure; keep the
      minimum but exclude arm latency from `sin` (subtract the dead zone);
      or label the column as end-to-end-including-launch.
- [ ] Unexplained outlier, do not paper over it: `ch8_b4_bpoff_seed0xA5A5A5A5`
      reports `sin starv=0, util=1.000` while all 19 other configs in the same
      sweep report ~197-205. It reproduces EXACTLY across two independent sweeps
      (so it is deterministic, not jitter) and sits at position #7 of 20 (so it
      does not correlate with first-arm-after-reset). Cause not established; the
      sink re-arm quirk documented in `run_characterization.py` was the obvious
      suspect and the ordering does not support it.
