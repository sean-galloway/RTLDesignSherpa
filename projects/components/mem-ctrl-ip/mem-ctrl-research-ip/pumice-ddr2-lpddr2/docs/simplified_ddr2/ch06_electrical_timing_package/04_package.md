# Package and Electrical Notes

A light pass: what matters when connecting a DDR2 device, deliberately
skipping the full ballout tables (consult the spec figures for those).

## Packages

- Single-die parts use FBGA per MO-207; x4/x8 in a 60-ball grid, x16 in
  an 84-ball grid.
- Dual-die and quad-die stacked parts use MO-242; the stack presents 2 or
  4 ranks with separate chip selects and per-rank ODT associations.
- Support (mechanical) balls exist in some variations - they are not
  signals.

## Supplies and signaling

| Rail | Nominal | Feeds |
| --- | --- | --- |
| VDD | 1.8 V | core |
| VDDQ | 1.8 V | output drivers (isolated from VDD noise by design intent) |
| VDDL | 1.8 V | DLL |
| VREF | VDDQ / 2 | input comparator reference (SSTL_1.8) |
| VTT | 0.9 V nominal | bus termination rail (board side) |

- SSTL_1.8: inputs are compared against VREF; tracking between VREF and
  VDDQ/2 must hold within 300 mV during ramp and tightly in operation.
- Address/command and data busses are source-terminated point-to-point or
  short-stub topologies with VTT pull-ups at the far end (plus ODT on the
  data group).
- CK/CK# is differential and must be kept crossing cleanly; tCH/tCL duty
  window is 0.45-0.55 tCK (0.48-0.52 on the tighter 667/800 bins).
- The spec allows spread-spectrum clocking within a bounded down-spread
  band; the DLL tracks it within limits.

## Speed bins

| Grade | tCK range (CL bin) | Typical CL-tRCD-tRP |
| --- | --- | --- |
| DDR2-400 | 5.0-8.0 ns | 3-3-3, 4-4-4 |
| DDR2-533 | 3.75-8.0 ns | 3-3-3, 4-4-4 |
| DDR2-667 | 3.0-8.0 ns | 4-4-4, 5-5-5 |
| DDR2-800 | 2.5-8.0 ns | 4-4-4, 5-5-5, 6-6-6 |

All bins share the same core analog floors (tRCD/tRP/tRAS scale with the
bin numbers in ns), which is why higher-speed parts need more clocks for
the same nanoseconds - and why a controller should store timings in ns
and convert to clocks at configuration time.

## Capacitance (loading budget)

Ballpark from the spec tables: CK inputs 1-2 pF, other inputs 1-2 pF,
DQ/DQS group 2.5-4 pF. These set how many devices a CK/address tree can
drive before a register or buffer is required - the reason registered
DIMMs exist.

**Source:** JESD79-2F sections 2.1-2.3, 6 (Tables 17, 39, 41)
