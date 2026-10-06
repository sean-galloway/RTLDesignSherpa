# Honest Limits

## What the board evidence does not cover

- The soak is statistical, not exhaustive. One million blocks is large, but it
does not visit every possible error pattern.
- The AXI4 flavour was not run to million-block depth. It refuses large runs
because of job-memory capacity, so long soaks belong on AXIS.
- BCH has no erasure path in this harness by design; the injector's
`out_erasure` is tied off.
- The board validates only the `BCH(4224,4120) t=8` profile. Smaller profiles
like `(63,57) t=1` are covered in simulation and component DV.
- The component DV matrix exercises the codec in ways the board harness does
not replicate.

## Traceability

Every quantitative claim in this book can be traced to an artifact under
`stable/`:

| Claim | Artifact |
|-------|----------|
| Timing-clean at 100 MHz | `stable/reports/genesys2_axis/timing_summary.txt`, WNS +0.586 ns, 0 failing endpoints. |
| AXI4 timing-clean | `stable/reports/genesys2_axi4/timing_summary.txt`, WNS +0.493 ns, 0 failing endpoints. |
| One million blocks, zero mis-decodes | `stable/results/2026-10-05_soak/battery.json` and `FINDINGS.md`. |
| 74,560 over-t blocks all flagged | `stable/results/2026-10-05_soak/battery.json`, `soak_final.over_t_blocks`. |
| 3,119,679 bits corrected | `stable/results/2026-10-05_soak/battery.json`, `soak_final.bits_corrected`. |

: Table 5.1: Traceability from claim to stable artifact.
