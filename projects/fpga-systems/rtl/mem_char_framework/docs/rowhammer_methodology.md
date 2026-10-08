# Rowhammer characterization methodology

> **Scope and safety.** This document is a design-verification and
> characterization methodology. It exists to answer one question on hardware
> we own: does this DRAM device, behind this controller, show bit flips when
> two adjacent rows are activated hard within a refresh window? Run it on
> your own boards, in your own lab, against devices you bought. Rowhammer is
> also an attack primitive — what follows is deliberately not a production
> feature, ships nothing into the controller's datapath, and must not be
> pointed at hardware you do not own or have written permission to stress.

The framework got its rowhammer legs in commit `9ce4cd1da`: both pattern
generators grew `cfg_hammer_en`, a 2-bit `data_mode` with a FILL source, and
the read engine grew `o_err_bits`, a saturating popcount of mismatched bits.
This chapter is the host-side half — the recipe, the register programming,
and the accounting that turns a flip count into a defensible statement about
the device. `ChargenDriver.rowhammer()` in `dv/tbclasses/chargen_driver.py`
implements the recipe end to end; the text here is the contract it follows.

## What the hardware gives you

Three mechanisms, and nothing else — the recipe is built from exactly these:

- **`hammer_en`** (`AXI_ATTR[17]`): the address-generator index becomes the
  transaction counter's LSB, so addresses alternate `base` / `base+stride_0`
  per transaction. One writer with `hammer_en=1` is two aggressor rows being
  ping-ponged. `stride_0` is reused as the aggressor-pair offset; no new
  stride port exists, and none is needed.
- **`data_mode = 2` (FILL)** (`AXI_ATTR[16:15]`): every beat is
  `cfg_fill_pattern` replicated across the data bus, on both the write and
  the read (the read engine regenerates the same expectation). CRC valid is
  gated low in this mode — integrity is the per-beat compare, not the CRC.
- **`o_err_bits`** (`RD_GENg_ERR_BITS`, bits 31:0): accumulated popcount of
  `actual ^ expected` across the run, saturating at all-ones. This is the
  bit-flip quantifier; `BEATS_MISM` tells you *that* beats were wrong, and
  err_bits tells you *how wrong*.

One trap worth naming up front: FILL is one constant per run. You cannot put
0s on one aggressor and 1s on the other inside a single hammer pass — the
campaign gets that shape by alternating `cfg_fill_pattern` between
0x00000000 and 0xFFFFFFFF on successive passes or successive victims. More
on this in the recipe.

## The double-sided recipe

Pick a victim row `V`. The aggressors are its two immediate neighbours in
the same bank, `V−1` and `V+1`. The classic result is that the victim
sandwiched between two hammered rows flips at a fraction of the activation
count a single aggressor needs, so that's where the methodology starts.

The geometry, in the byte-address map the host programmed into the
controller:

- **Aggressor base** = `V − row_pitch` (the row below the victim).
- **`stride_0`** = `2 × row_pitch` — the ping-pong steps over the victim
  entirely, so the pair is `V−1`, `V+1`, `V−1`, ...
- **`row_pitch`** = the byte stride between consecutive rows of one bank.
  On the NexysA7 ROW_MAJOR map that's `Geometry.row_stride_same_bank` —
  page bytes (2 KB for the MT47H64M16) shifted past the bank field, 16 KB.
  It is a property of the address map, not of the device alone; compute it
  from the map you programmed, and pass it to the driver rather than
  hardcoding it.
- **BL1** (`burst_len = 1`): one AXI beat per transaction, so one ACT per
  transaction at close-page policy. Longer bursts would amortize the ACT
  across beats and quietly halve your disturb rate — the whole point of the
  exercise is activations, not bandwidth. (In a build that overrides
  `BURST_LEN_MULTIPLE` past 1, the quantum replaces BL1; the framework's
  default is 1, so a single-beat burst is legal here. The perf suites'
  whole-burst rule is about meaningful bandwidth numbers, not about this.)
- **`hammer_txns` even**: the ping-pong spends one transaction per
  aggressor. An odd count activates one side once more and skews the
  disturb; the driver refuses it.
- **Data**: `data_mode = 2`, `cfg_fill_pattern` = the aggressor fill.
  Campaigns alternate 0x00000000 and 0xFFFFFFFF between passes — the two
  fills exercise opposite coupling polarities, and a run that only ever
  hammers one fill can miss flips the other fill would have shown.
- **`wrap_mask_0 = 0`**: no wrap. With the mask zeroed, `dma_address_gen`
  applies no offset mask, so index 0 lands on base and index 1 on
  `base + stride_0` exactly. A nonzero mask here is a silent geometry bug.

Setup, before the hammer, all through ordinary write passes:

1. Fill the victim row with `victim_pattern` (default 0xFFFFFFFF).
2. Fill the aggressor rows if the campaign wants a specific image in place
   when the hammer starts. Note the hammer rewrites both aggressors with
   `cfg_fill_pattern` on every activation — the setup fill controls what the
   aggressors hold *during* the pass, not after it.

Then two phases, writer then reader on the same generator index:

1. **Hammer.** Writer `g`, `hammer_en = 1`, base/stride/BL1 as above,
   `txn_count = hammer_txns`, FILL with the aggressor pattern. Launch with
   GO, wait done, check the writer didn't latch a BRESP error.
2. **Readback.** Reader `g`, `hammer_en = 0`, base = `V`, `stride_0` = one
   beat, `txn_count = row_pitch / beat_bytes` so the whole row is walked,
   FILL expecting `victim_pattern`. The reader's err_bits is the result: a
   bit the hammer flipped counts exactly once, no matter which beat it
   arrived in.

## Register programming

Values below are the recipe; `g` is the generator index. Status registers
are readback, not programmed.

| Register | Field | Bits | Value | Why |
|----------|-------|------|-------|-----|
| `WR_GENg_START_ADDR` | `addr` | 31:0 | `V − row_pitch` | aggressor below the victim |
| `WR_GENg_STRIDE_0` | `stride` | 23:0 | `2 × row_pitch` | ping-pong pair offset; must fit 24 signed bits |
| `WR_GENg_STRIDE_1` | `stride` | 23:0 | 0 | one address dimension only |
| `WR_GENg_WRAP_MASK_0` | `mask` | 31:0 | 0 | no wrap — any nonzero mask breaks the geometry |
| `WR_GENg_WRAP_MASK_1` | `mask` | 31:0 | 0 | unused |
| `WR_GENg_BLEN_TXN` | `burst_len` | 7:0 | 1 | BL1: 1 ACT per transaction |
| `WR_GENg_BLEN_TXN` | `txn_count` | 23:8 | `hammer_txns` (even) | total activations across the pair |
| `WR_GENg_BLEN_TXN` | `gap` | 27:24 | 0 | pace at full rate; sweep `gap` only to probe the controller |
| `WR_GENg_AXI_ATTR` | `axi_id` | 7:0 | `g` | one id per generator, per the house convention |
| `WR_GENg_AXI_ATTR` | `id_mode` | 9:8 | 0 (FIXED) | |
| `WR_GENg_AXI_ATTR` | `axi_size` | 12:10 | 3 | 8-byte beats on the 64-bit bus |
| `WR_GENg_AXI_ATTR` | `axi_burst` | 14:13 | 1 (INCR) | |
| `WR_GENg_AXI_ATTR` | `data_mode` | 16:15 | 2 (FILL) | constant aggressor fill |
| `WR_GENg_AXI_ATTR` | `hammer_en` | 17 | 1 | the ping-pong itself |
| `WR_GENg_AXI_ATTR` | `max_outstanding` | 23:18 | 0 | as built; outstanding doesn't change the ACT count |
| `WR_GENg_LFSR_SEED`, `WR_GENg_HASH_SEED0..2` | `seed` | 31:0 | 0 | inert in FILL mode; write them anyway so no stale seed leaks |
| `WR_GENg_FILL_PATTERN` | `pattern` | 31:0 | 0x00000000 / 0xFFFFFFFF | alternated between passes or victims |
| `RD_GENg_START_ADDR` | `addr` | 31:0 | `V` | victim readback base |
| `RD_GENg_STRIDE_0` | `stride` | 23:0 | `1 << axi_size` | walk the row one beat per transaction |
| `RD_GENg_WRAP_MASK_0/1` | `mask` | 31:0 | 0 | no wrap |
| `RD_GENg_BLEN_TXN` | `burst_len` | 7:0 | 1 | BL1 beats |
| `RD_GENg_BLEN_TXN` | `txn_count` | 23:8 | `row_pitch / beat_bytes` | the whole victim row |
| `RD_GENg_AXI_ATTR` | `data_mode` | 16:15 | 2 (FILL) | expect `victim_pattern` |
| `RD_GENg_AXI_ATTR` | `hammer_en` | 17 | 0 | ordinary walk |
| `RD_GENg_FILL_PATTERN` | `pattern` | 31:0 | `victim_pattern` | the expected victim image |
| `GO` | `wr_gog` / `rd_gog` | g / 8+g | 1 (pulse) | one write per phase; stage first, launch together |
| `RD_GENg_ERR_BITS` | `beats` | 31:0 | read | the observable: flipped-bit popcount, saturated |
| `RD_GENg_BEATS_MISM` | `beats` | 31:0 | read | beats that differed at all |
| `RD_GENg_STATUS` | `done`/`data_error`/... | 4:0 | read | done plus sticky per-beat flags |

The driver writes every config field on every program call — `hammer_en` and
`FILL_PATTERN` included — because a run that inherits `hammer_en=1` from the
previous scenario looks like a controller bug for a day.

## The observable, and its limits

`err_bits` is a saturating counter. A long campaign that saturates it has
spent its resolution — you know "at least 2^32−1 flipped bits" and nothing
more. Two habits keep the number meaningful:

- Read `ERR_BITS` per pass (the recipe does), and if it saturates, re-run
  the victim readback in windows — split the row walk into chunks and sum
  per-chunk err_bits, keeping each chunk under the ceiling.
- Cross-check with `BEATS_MISM`. err_bits ≫ 32 × BEATS_MISM says many bits
  per beat flipped; err_bits ≈ BEATS_MISM says scattered single-bit upsets.
  The two distributions point at different physics.

Also remember what err_bits is *not*: it compares against the FILL
expectation, so a victim that was never filled correctly in setup reads as
"flipped" everywhere. The setup fill is part of the measurement, not a
preliminary.

## Refresh-window accounting

The disturb only matters relative to how often the victim's cells get
refreshed, so every published number in a campaign report should carry the
refresh accounting with it. The pieces, at `f_mc = 100 MHz`:

| Quantity | Formula | NexysA7 example (DDR2) |
|----------|---------|------------------------|
| tREFI in cycles | `tREFI × f_mc` | 7.8 µs → 780 cycles |
| ACT ceiling per tREFI, one bank | `tREFI_cycles / tRC_cycles` | 780 / 5 ≈ 156 (tRC = 45 ns class) |
| ACTs per aggressor per tREFI at ceiling | ceiling / 2 | ≈ 78 |
| Refreshes per tREFW | `tREFW / tREFI` | 8192 (MT47H64M16, tREFW = 64 ms) |
| Refresh time stolen per tREFW | refreshes × tRFC | 8192 × tRFC |
| LPDDR2 frame | — | tREFI 7.8 µs, tREFW 32 ms at ≤ 85 °C (16 ms derated, tREFI 3.9 µs) |

Three consequences shape how you run and how you read the result.

**You are tRC-limited, not bandwidth-limited.** A BL1 same-bank stream costs
ACT + CAS + PRE per transaction; back-to-back ACTs to one bank can't come
closer than tRC. If the measured err_bits vs `hammer_txns` curve has a knee
below the tRC-implied ceiling, the controller is the limiter (scheduling,
refresh collisions, bank-group effects), not the device — say so in the
report rather than attributing it to the DRAM.

**Refresh doesn't pause for the hammer.** The device gets its
`tREFW / tREFI` refreshes regardless, and pumice's refresh controller will
postpone up to 8 refreshes under sustained demand — which a saturated
hammer bank supplies constantly. The practical effect: the refresh backlog
builds to the 8-deep ceiling while the hammer runs, so a given row's
refresh can slip by up to 8 × tREFI — the victim's cells age longer than
nominal exactly when they're being disturbed. That's the realistic worst
case and a legitimate test condition, but it must be stated with the
results. To isolate the disturb from the retention stretch, pin
tREFI short through the controller's refresh CSR so the window can't
float, and say which mode the numbers came from.

**The dose is per refresh window.** Published double-sided thresholds on
susceptible parts sit in the tens-to-hundreds of thousands of activations
per aggressor within a refresh window; nobody has published a trustworthy
number for your exact part and controller, which is the point of running
this. Report activations per aggressor per tREFI alongside err_bits — a flip
count without the activation rate is anecdote.

A null result is a result. DDR2 and LPDDR2 at these geometries are not
expected to flip as readily as the DDR3/4 parts the classic papers used; "no
flips at the tRC ceiling across the window" is what you want to be able to
say about your controller's refresh discipline, and this methodology can say
it honestly.

## Single-sided variant

One aggressor instead of two: base = `V + row_pitch`, `stride_0 = 0`,
`hammer_en = 1` kept on (the index toggles, both addresses are the same
row). Everything else — BL1, FILL, even `hammer_txns`, the readback —
unchanged. Single-sided needs a much higher activation count to flip, so
it's the cheaper probe to run first when you're mapping whether the device
responds at all, and it's the only option at the device edges where `V−1`
doesn't exist. Use it at the top edge (`V + row_pitch` past the last valid
row) with `double_sided=False`; the driver bounds both cases.

## Where this feeds: PARA and TASK-009

The deferred per-bank-refresh PARA work (`vault/Tasks/scoria-ddr3-lpddr3/
task/deferred/TASK-009.md`) is unblocked by exactly two things: a bitstream,
and a rowhammer test methodology. This document is the second half of that
condition. PARA — probabilistic adjacent-row refresh — needs an
aggressor/adjacency tracker in the scheduler (its own design, explicitly
out of scope here) and a way to judge whether it works. The err_bits curve
this methodology produces is that judge: run the campaign, record flips vs
activation count with PARA off, repeat with it on, and the same observable
decides whether the mitigation earned its area.

The refresh accounting above is also why PARA pairs naturally with per-bank
refresh. pumice's refresh controller already carries the LPDDR2 REFpb rotor
(`refpb_mode`, per-bank interval); a hammer campaign saturates one bank
while seven sit quiet, and all-bank refresh spends most of its budget on
the quiet ones. Refreshing the hammered bank more often — per-bank or
PARA-targeted — spends the budget where the activations are. The methodology
here doesn't implement any of that; it produces the measurement that tells
you whether you need it.
