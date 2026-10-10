<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# The Target Design Point

## Named as of v0.5

Sean, 2026-09-30: "Assume k7ddrphy on genesys2 if it helps." It helps
considerably — it converts most of this specification's build-time parameters
from open to fixed, and it gives every future bandwidth number a denominator.

The board decision for *verification* is unchanged: scoria is verified against a
DFI bus functional model in simulation. What follows is the **target** the
parameters are chosen for, not a claim that a bitstream exists.

| Item | Value | Source |
|---|---|---|
| Board | Digilent Genesys 2 | already on the bench for STREAM and RAPIDS |
| FPGA | Xilinx Kintex-7 | board |
| PHY | `s7ddrphy.K7DDRPHY`, `memtype="DDR3"`, `nphases=4` | litex-boards `digilent_genesys2` |
| DRAM | 2 x MT41J256M16, 32-bit bus | platform: 32 DQ, 4 DQS pairs, 4 DM |
| Geometry | 8 banks, 32768 rows, 1024 columns | LiteDRAM `MT41J256M16` |
| Address pins | 15 address, 3 bank | platform; matches 2^15 rows and 2^3 banks |
| System clock | 75 MHz | owner restatement 2026-10-10 — 100 MHz was never the target (scoria BUG-003, closed) |
| Gear ratio | 1:4 | `MT41J256M16(sys_clk_freq, "1:4")` |
| DRAM clock | 400 MHz | PHY PLL output from the 200 MHz board oscillator; not derived from sys |
| Data rate | 800 MT/s -- **DDR3-800** | 2 x CK |
| **Theoretical peak** | **3200 MB/s** | 800 MT/s x 32 bit / 8 |

: Table 2.4: The target design point

**For comparison, pumice's peak is 600 MB/s** (300 MT/s on a 16-bit bus). scoria's
target is 5.3x that, from a wider bus and a higher rate — worth stating plainly
because it changes what the front end has to sustain, not just what the DRAM can
do.

**Important — 3200 MB/s is the denominator.** The house rule is that a bandwidth
table carries the measured figure *and* the theoretical maximum. For scoria on
this target the maximum is 3200 MB/s, and a percentage quoted without it is not
a result. pumice learned this twice: once by publishing percentages that were
understated 2x because the byte counter was per-phase, and once by quoting a
figure with no peak beside it.

## What this fixes

Build-time parameters that earlier editions left open now have values:

| Parameter | Value | Why it is forced |
|---|---|---|
| `DFI_RATE` | **4** | must equal the PHY's `nphases`, which is 4. Not a choice, and a mismatch is a functional break that presents as data corruption |
| `NUM_BANKS` | 8 | DDR3 geometry |
| row width | 15 | 32768 rows. pumice's package already pads the row field to 18 bits "DDR3 forward-compat", so this fits with headroom |
| column width | 10 | 1024 columns |
| DQ width | 32 | board wiring, 2 devices in parallel |
| `NUM_RANKS` | 1 | single rank per device, both in parallel on one chip select |

: Table 2.5: Build-time parameters fixed by the target

**`DFI_RATE = 4` is the happy accident worth noting:** pumice also runs four DFI
phases, so the inherited DFI datapath — the async-FIFO CDC, the bubble-free
pipeline, the per-phase `_pN` signalling — transfers at the same gear ratio it
was built and measured at. Had the target been 1:2, the datapath would still
work but none of pumice's phase-level measurements would carry over.

## The JEDEC timings for this part and bin

From LiteDRAM's `MT41J256M16` definition, DDR3-800 speed bin. These are the
values the CSRs are initialized to; they remain **runtime** registers.

| Parameter | Value |
|---|---|
| `tREFI` | 7812.5 ns (64 ms / 8192) |
| `tRP`, `tRCD`, `tWR` | 13.1 ns each |
| `tRAS` | 37.5 ns |
| `tRFC` | 139 ns |
| `tFAW` | 50 ns |
| `tRRD` | max(6 nCK, 10 ns) |
| `tWTR` | max(4 nCK, 7.5 ns) |
| `tCCD` | 4 nCK |
| `tZQCS` | max(64 nCK, 80 ns) |

: Table 2.6: DDR3-800 timings for MT41J256M16

**Note:** several are stated as max(nCK, ns), which is JEDEC's form and the
reason the CSR derivation must take the larger of the two after converting at
the operating frequency. pumice's timing derivation was corrected once for
exactly this — a formula that matched one measured point but took the wrong
branch elsewhere.

At CK = 400 MHz (2.5 ns), the write-leveling windows of Chapter 3.3 become
concrete: `tWLMRD` 40 nCK = 100 ns minimum, `tWLDQSEN` 25 nCK = 62.5 ns.

## What is still open

Nothing in the specification. Two things remain *choices to be made during
implementation* rather than open questions:

- **`tWLMRD`'s maximum**, which is scoria's to define as a timeout (Chapter 6).
  With CK at 2.5 ns a generous bound is easy to pick; the requirement is that it
  exists and reports distinctly, not that it be tight.
- **A bitstream, and timing closure at 75 MHz.** The board build flow now
  exists — board top, harness, passing lint — but no bitstream has been built.
  The first out-of-context synthesis (2026-10-01, scoria BUG-003) measured
  WNS -2.022 ns reg-to-reg against a 10 ns constraint (fmax 83.2 MHz). Against
  the restated 75 MHz design point (13.33 ns) that same measurement is
  approximately **+1.3 ns of positive slack** — the design point is met as the
  RTL stands. The owner restated the clock on 2026-10-10 (100 MHz was never
  the target; BUG-003 closed on that restatement). The OOC evidence itself is
  unchanged and belongs to the bug; what a real board build adds is
  floorplanning, congestion, and the correctly-constrained `dfi_clk` domain —
  a bitstream at 75 MHz remains the open item.
