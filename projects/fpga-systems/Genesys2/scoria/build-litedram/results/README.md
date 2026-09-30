# Genesys 2 LiteDRAM DDR3 board proof -- results

`bios_boot_memtest.log` is the first hardware evidence for the scoria DDR3
target. It contains **no scoria RTL**: the LiteDRAM core plus its VexRiscv BIOS
answer one question on their own, so that a later scoria failure has a
denominator instead of being one unknown among four.

## Verdict

**Memtest OK.** Board, pins, K7DDRPHY and DRAM are sound.

## What the board reports about itself

```
SDRAM:   1.0GiB 32-bit @ 800MT/s (CL-6 CWL-5)
CPU:     VexRiscv @ 100MHz
BUS:     wishbone 32-bit data/32-bit addr
```

That is the scoria design point confirmed by hardware rather than by datasheet:
1 GiB from 2 x MT41J256M16, 32-bit, DDR3-800 at 1:4 gearing. **CL-6 / CWL-5 is
a live calibrated value**, which makes it a real check on
`scoria_mode_register`'s CL and CWL decode rather than a spec reading. DDR3 does
not tie CWL = CL-1, and here it does not: 6 and 5 happen to differ by one, which
is a coincidence at this bin and must not be leaned on.

## The calibration tuple

This is the reusable part -- the equivalent of the DDR2 campaign's
`wrlat 1, rden 6, rddata_delay 7, bitslip0/tap8`, and the reason that hunt was
tractable at all. Four byte modules, m0..m3, which is the 32-bit bus:

| Stage | Result |
|---|---|
| tCK equivalent | 32 taps |
| Cmd/Clk delay | 15 taps (scan `1111111000000001`) |
| Write latency | m0..m3 all **6** |
| Write DQ-DQS | all modules **03 +-03** |
| Read leveling | bitslip **b02** on all modules; delays **08/09/11/11 +-06** |

Signal integrity reads healthy: every module resolves to one bitslip with a
+-6-tap window, and the b03 alternative sits a full cycle away rather than
overlapping. A narrow or ambiguous window here is what a marginal board looks
like, and this is neither.

## The speed numbers are NOT controller bandwidth

```
Write speed: 61.5 MiB/s
 Read speed: 62.3 MiB/s
```

Theoretical peak for this design point is **3200 MB/s** (32-bit at 800 MT/s),
so these are ~2% of peak -- and that is expected, not a finding. The BIOS
memspeed runs on the **VexRiscv over a 32-bit Wishbone bus**, not on the 64-bit
AXI user port, and a soft CPU issuing word accesses is nothing like the
characterization engine. Do not quote these as a LiteDRAM bandwidth result or
compare them against scoria numbers.

A flat ~2% of peak was a genuine defect on the DDR2 campaign, so the
resemblance is worth naming explicitly: there, the traffic source was the char
engine and 2% meant arbiter starvation. Here the traffic source is a
100 MHz soft core and 2% means the core is the limit. The measurement that can
be compared with scoria is the AXI user port driven by the shared
`char_engine_block`, which is the sibling `build-scoria` build's job.

## Reproducing

```
make -C build-litedram program      # 7 s over JTAG, serial 200300B818A0
# then at the litex> prompt on /dev/ttyUSB0 @115200:
reboot
```

The Genesys 2 UART is a **separate FT232R** (serial `AU05X8RM`), not an
interface of the JTAG FT2232, so both cables must be enumerated or there is no
port at all whatever the bitstream does.
