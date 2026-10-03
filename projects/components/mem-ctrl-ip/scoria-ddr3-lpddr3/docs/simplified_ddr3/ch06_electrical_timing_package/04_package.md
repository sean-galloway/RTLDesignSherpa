# Package and Electrical Notes

A light pass: what matters when connecting a DDR3 device, deliberately
skipping the full ballout grids (consult the spec figures for those).

## Packages

- Monolithic parts use FBGA per JEDEC MO-207: dedicated ballouts for x4
  (sec 2.1), x8 (sec 2.2) and x16 (sec 2.3) organizations. Unused grid
  positions are no-connect mechanical support balls; whether they are
  populated depends on the vendor's package size, so land patterns should
  assume the maximum allowed package.
- Dual-die and quad-die stacked packages present 2 or 4 ranks behind one
  channel: each rank gets its own chip select and ODT association, and
  shares the address/command and data busses.
- New pins versus DDR2: RESET# (full-chip reset, active low) and the ZQ
  calibration reference pin (bonds to an external 240 ohm resistor).

## Supplies and signaling

| Rail | Nominal | Feeds |
| --- | --- | --- |
| VDD | 1.5 V +/- 0.075 | core and DLL (DDR3 drops DDR2's separate VDDL) |
| VDDQ | 1.5 V +/- 0.075 | output drivers |
| VREFCA | 0.5 x VDD | command/address input reference |
| VREFDQ | 0.5 x VDDQ | data input reference |
| VTT | 0.75 V nominal | board-side termination rail for the CA bus |

- SSTL_15 signaling: single-ended inputs compare against the VREF rails;
  CK/CK#, DQS/DQS# run differential.
- The CA bus is source-terminated point-to-point or short-stub with VTT
  pull-ups; the DQ group leans on ODT instead (Chapter 5).
- Case temperature: 0-85 C standard operation; parts rated for the
  extended range run 85-95 C at half tREFI with the SRT/ASR mode bits set
  (MR2).

## Speed bins

| Grade | CL-nRCD-nRP bins | tRCD/tRP (ns) |
| --- | --- | --- |
| DDR3-800 | D: 5-5-5, E: 6-6-6 | 12.5 / 15 |
| DDR3-1066 | E: 6-6-6, F: 7-7-7, G: 8-8-8 | 11.25 / 13.125 / 15 |
| DDR3-1333 | F: 7-7-7, G: 8-8-8, H: 9-9-9, J: 10-10-10 (opt) | 10.5 / 12 / 13.5 / 15 |
| DDR3-1600 | G: 8-8-8, H: 9-9-9, J: 10-10-10, K: 11-11-11 (opt) | 10 / 11.25 / 12.5 / 13.75 |
| DDR3-1866 / 2133 | per Tables 66-67 | 13.125+ / see sec 13.2 |

Every grade carries its own tCK(avg) window per supported CL setting
(Tables 62-67): roughly 3.3 ns at the slow end (DLL-off floor 8 ns) down
to 1.25 ns at DDR3-1600 and above. All bins share the same core analog
floors (tRCD/tRP/tRAS in ns), which is why higher-speed parts need more
clocks for the same nanoseconds - and why a controller should store
timings in ns and convert to clocks at configuration time.

## Characterization

Section 10 defines the IDD/IDDQ measurement conditions (the familiar
current-state table per operation); section 11 gives pin capacitance
budgets. Neither changes how the device is scheduled; consult them when
sizing the power delivery rather than the scheduler.

**Source:** JESD79-3F sections 2, 6, 12.3 (Tables 62-67)
