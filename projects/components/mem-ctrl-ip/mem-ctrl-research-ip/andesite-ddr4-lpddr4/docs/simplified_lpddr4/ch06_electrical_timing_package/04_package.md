# Package and Electrical Notes

A light pass: what matters when connecting an LPDDR4 device, skipping
the full ballout grids (spec sec 2 has many package variants).

## Packages and channels

- LPDDR4 is dual-channel per die: two independent x16 channels (x8 byte
  mode selectable), each with its own CA bus, CK, CKE, CS, ODT and
  refresh schedule. Package variants pair, drop, or stack channels:
  quad-channel PoP FBGA (272-ball), two-channel discrete (200/203/254-
  ball classes), single-channel ePoP/MCP (144-ball), and wide x64
  discrete packages for non-mobile density.
- 8 banks per channel, flat; densities per channel 1 Gb to 16 Gb (die
  totals to 32 Gb dual channel).
- Pins beyond LPDDR3: RESET_n (dedicated - reset is a pin, not an MRW),
  ODT(CA) per channel (CA-bus termination is new), DMI per byte lane
  (mask + DBI flag), and ZQ.

## Supplies and signaling

| Rail | Nominal | Feeds |
| --- | --- | --- |
| VDD1 | 1.8 V | core/array |
| VDD2 | 1.1 V | core logic |
| VDDQ | 1.1 V (0.6 V on 4X parts) | I/O buffers |

LVSTL-class low-voltage signaling, unterminated by design; the CA bus
gets its first termination option via ODT(CA) (MR-controlled). DQ ODT
is asynchronous per MR, and DBI plus masked write do the power and
partial-write jobs without a termination rail.

## Speed grades

Data rates 533 to 4267 Mb/s per channel (tCK 3.75 ns down to ~0.468 ns
per channel pair of Table 88 columns); the programmed RL/WL pair must be
re-selected when the clock moves - which is what the frequency set
points (FSP) exist for: two pre-programmed MR sets the controller
switches between instead of retraining from scratch.

## Characterization

IDD tables and pin capacitances live in the spec's later sections;
consult them for power delivery (dual-channel simultaneous refresh is
the worst case). Nothing there changes scheduling.

**Source:** JESD209-4E sections 2, 6.1, 4.3 (Table 88), 4.29
