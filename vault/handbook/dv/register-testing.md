---
title: Register testing comes first
summary: Walk every register of every endpoint before anything else is trusted - in sim, and again on the board before any functional bring-up. If the registers do not work, nothing above them can.
---

# Register testing comes first

**Rule: walk the registers before you program anything, and again on silicon
before any functional bring-up.** Not after the first coverage run, not when
something looks wrong. First.

Registers are the only way software configures hardware. Every functional
result, every coverage number, every board measurement rests on writes having
landed where they claim. When that assumption breaks, nothing above it means
anything -- and the failure is silent, because a broken register path still
accepts writes and still returns values.

## What "walk" means

`RegisterMap.walk()` in `bin/TBClasses/apb/register_map.py`. The map already
knows every name, address, reset default and per-field `sw` attribute, so the
check lives in the base class -- one implementation, not one per testbench and
one per host tool. The caller supplies only the accessors, which is what lets
the SAME check run in cocotb and over UART on the board:

```python
fails = reg_map.walk(read=bridge.read, write=bridge.write)   # board
fails = reg_map.walk(read=tb.read_apb,  write=tb.write_apb)  # sim
```

Per register it checks:

- **reachable** -- no bus-error sentinel
- **reset value on the SW-OWNED bits only**
- **writable fields take a write and read back**, masked to those fields
- **read-only registers do not move** when written
- **volatile read-only registers are detected, not accused** -- sample twice
  before writing; a free-running counter changes by itself and the write test
  cannot say anything about it

## Four things the walk must get right, or it lies

1. **SW-owned bits only, from FIELD attributes.** The RDL `default` is the reset
   value of a STORAGE element. A field marked `sw='r'` mirrors hardware and has
   no storage, so its "default" describes nothing -- `CHANNEL_IDLE` reading
   `0xF` at reset is CORRECT (all four channels are idle). Comparing the whole
   word reported 9 defects that were all working hardware.
2. **Field level, never register level.** `CHANNEL_IDLE` is `sw='rw'` at
   register level while every field inside it is `sw='r'`. A register-level
   check is wrong in both directions.
3. **Patterns above 0xF.** A field silently narrowed to 4 bits passes any test
   that only writes small numbers -- which is how a 16-bit timeout squashed to
   4 bits survived review in twelve wrappers.
4. **Detect the no-response sentinel by value.** `0xDEADBEEF` has bits 0,2,3,6
   set and satisfies most "is bit N set?" tests, so an unreachable register can
   masquerade as a working one.

## Why FIRST, and why on the board too

Two failures from one bring-up, both invisible to everything else:

- **`obs_apb` / `slvmon_apb` were 1-bit buses.** Nets used in a port map before
  declaration became implicit 1-bit wires, so a 32-bit APB address and data path
  reached silicon one bit wide. Verilator resolves the later declaration and
  every cosim passed; Vivado only warned. Every board experiment that configured
  the observer or the slave monitors was therefore meaningless -- for weeks --
  and nothing said so, because writes "succeeded" and reads returned something.
  A register walk finds this in seconds. Reasoning about monitor behaviour does
  not.
- **A 12-bit APB window with registers at 0x1000+.** Addresses truncated back
  into the functional block: `RDMON_ENABLE 0x10E0 -> 0x0E0` (unmapped) and
  `WRMON_ENABLE 0x1100 -> 0x100`, which is `GLOBAL_CTRL`. The test was writing
  the DMA's global control register while believing it configured a monitor.

Neither is findable by staring at RTL, and both invalidate everything measured
afterwards. Ten minutes of walking beats days of inference.

## The walk is DESTRUCTIVE -- which is another reason to run it first

It restores RDL defaults, and reset defaults are the safe-but-silent state, not
the working state. On the STREAM monitors the default is `PKT_MASK=0xFFFF` --
drop every packet type -- so a coverage run straight afterwards showed 0/8
tuples and looked like a dead design. Reprogramming restored 5/8.

Run it first, or reprogram after. Never interleave it with functional runs.

## Scope: every component that has registers

Each of these needs the walk in its own test suite, and in its board bring-up
before anything else runs:

| Component | Regmap |
|---|---|
| STREAM | `dmas/stream/rtl/stream_regmap.py` (139 regs, 86 of them monitor) |
| RAPIDS-beats | `dmas/rapids/rtl/*_regmap.py` |
| pumice (DDR2/LPDDR2) | `memory-controllers/pumice-ddr2-lpddr2/regs/generated/` |
| observer + slave monitors | `misc/rtl/regs/generated/` (`obs_regs`, `slvmon_regs`) |
| retro legacy blocks | `retro_legacy_blocks/rtl/{hpet,pic_8259,pit_8254,rtc}/` |
| board harnesses | e.g. `Genesys2/stream/rtl/harness_csr_regmap.py` |

Reference implementations:

- **sim:** `dmas/stream/dv/tests/top/test_stream_top_regs.py` -- both monitor
  configurations, and the monitors-absent case is an `xfail` gate for
  [[STREAM-MONREGS]] rather than a silent gap
- **board:** `Genesys2/stream/build-mon/host/host_reg_walk.py` -- four endpoints,
  258 registers, bases taken from the address modules that own them and never
  re-typed ([[registers-by-name]])

A walk that finds nothing is not wasted: it converts "the registers are probably
fine" into a number, and that number is what every later result depends on.

Related: [[registers-by-name]], [[silent-fallbacks]], [[bfm-usage]].
