---
title: Board results vs the RTL
summary: A board perf delta is a design delta only after a from-reset run matches the RTL cosim; sweeps carry leftover state and marginal builds misbehave with correct data.
---

# Board results vs the RTL
## A perf-sweep delta is not a design delta until the board matches the RTL from reset (2026-11-07)

The amber FPGA rework (cache-ip items 1/4/6) came back from the pair-rig
perf sweep with ~8% fewer misses on every thrash config while the
resident configs matched the baseline exactly. Two things were wrong with
reading that as a behaviour change. First, the sweep runs its configs
back to back without flushing the caches, so every config after the first
starts from leftover state shaped by the racy shared-region configs
before it; the per-config numbers are not from-reset numbers. Second, the
baseline bitstream was not implementing its RTL: the same baseline RTL
rebuilt with today's flow failed timing (WNS -0.116 ns) and, run from
reset on one config, produced 22,308 misses where the cosim of that RTL
produces 20,442 -- with bit-identical injector CRCs, because a false miss
only refetches. The reworked bitstream matched the cosim exactly (same
CRCs, same run-cycle counts, 20,442) and reproduced its own sweep
run-to-run to the miss, which the old design never did (10-miss jitter
between two baseline runs). The method that settled it, in order of cost:
cosim old vs new RTL on the same config and seeds (bit-identical => not
an RTL change); a from-reset board run of ONE config compared to the
cosim's injector CRCs and fill count; only then an A/B rebuild of the
baseline RTL. The injector CRC alone proves data, not hits: compare the
fill-end count too.
