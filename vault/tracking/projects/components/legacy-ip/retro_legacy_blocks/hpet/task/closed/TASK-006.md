# TASK-006: make the HPET register interface match the published spec

**Priority:** P1
**Status:** CLOSED 2026-09-28. Owner's directive: "Hpet must follow the standard
spec." Implemented, regenerated, tested and documented; see "Outcome".
**Owner:** done

**Why:** the block's register interface diverges from the IA-PC HPET
specification in offsets, capability-field bit positions, and per-timer
configuration semantics. A driver written to the spec would misread the
capability register almost entirely and would write the wrong per-timer control
bits. Found 2026-09-28 while scoping TASK-003, whose legacy-replacement routing
is DEFINED as overriding `INT_ROUTE_CNF` -- a field we do not implement, so
TASK-003 cannot be spec-correct until this lands. **TASK-006 blocks TASK-003.**

**Sources.** Bit positions and offsets confirmed from TWO independent public
headers that agree exactly: QEMU `include/hw/timer/hpet.h` and FreeBSD
`sys/dev/acpica/acpi_hpet.h`. Linux `include/linux/hpet.h` corroborates the
capability masks and `struct hpet` corroborates the offsets.

## Target map

| Register | Spec offset | Ours today |
|---|---|---|
| `GCAP_ID` (lo) | 0x000 | 0x000 (ok) |
| `GCAP_ID` (hi) = `COUNTER_CLK_PERIOD` | **0x004** | **absent** |
| `GEN_CONF` | **0x010** | 0x004 |
| `GINTR_STA` | **0x020** | 0x008 |
| `MAIN_CNT` lo/hi | **0x0F0/0x0F4** | 0x010/0x014 |
| `TIMn_CONF` | 0x100+0x20n (ok) | same |
| `TIMn_INT_ROUTE_CAP` | +0x04 | absent |
| `TIMn_COMP` lo/hi | **+0x08/+0x0C** | +0x04/+0x08 |
| `TIMn_FSB_VAL/ADDR` | +0x10/+0x14 | absent |

Address span is UNCHANGED: the FSB registers fit inside each timer's existing
0x20 stride, so the top stays 0x100 + 8*0x20 = 0x200. `HPET_REGS_SIZE` is
already 'h200 and `MIN_ADDR_WIDTH` already 9 -- no cpuif widening needed.

## GCAP_ID field positions

| Field | Spec | Ours |
|---|---|---|
| `REV_ID` | 7:0 | 23:16 |
| `NUM_TIM_CAP` | 12:8 | 12:8 (ok) |
| `COUNT_SIZE_CAP` | 13 | 7 |
| `LEG_RT_CAP` | 15 | 5 |
| `VENDOR_ID` | 31:16 (16-bit) | 31:24 (8-bit) |

Widening `VENDOR_ID` to 16 bits retires a documented wart: today a PCI-style
vendor reads back as its low byte only.

## TIMn_CONF -- the largest change

Spec (`0x002` INT_TYPE, `0x004` INT_ENB, `0x008` TYPE, `0x010` PER_INT_CAP RO,
`0x020` SIZE_CAP RO, `0x040` VAL_SET, `0x100` 32MODE, `0x3e00` INT_ROUTE_CNF
shift 9, `0x4000` FSB_EN, `0x8000` FSB_INT_DEL_CAP RO, `INT_ROUTE_CAP` 63:32 RO).

FOUR of our five writable bits sit where the spec assigns a different meaning,
and two of those spec positions are READ-ONLY capability bits:

| Ours | Spec at that bit | Resolution |
|---|---|---|
| `timer_enable[2]` | `INT_ENB_CNF` | **DROPPED** (below) |
| `timer_int_enable[3]` | `TYPE_CNF` (periodic) | moves to bit 2 |
| `timer_type[4]` | `PER_INT_CAP` (RO) | moves to bit 3 |
| `timer_size[5]` | `SIZE_CAP` (RO) | becomes `32MODE_CNF` bit 8, INVERTED |
| `timer_value_set[6]` | `VAL_SET_CNF` | unchanged (ok) |

`32MODE_CNF` is inverted from `timer_size`: spec 1 = force 32-bit; ours 1 =
64-bit. Internally `timer_size = ~32mode` while `SIZE_CAP = 1`.

New RO capability bits: `PER_INT_CAP = 1` (periodic is implemented),
`SIZE_CAP = 1` (64-bit counter), `FSB_INT_DEL_CAP = 0` (no FSB delivery).

## timer_enable is DROPPED -- owner's decision, and its consequence

The spec has NO per-timer run enable; a timer compares whenever the main
counter runs and `INT_ENB_CNF` gates only the interrupt. Owner chose pure spec
(2026-09-28).

**The consequence must be recorded because it changes a documented contract.**
`hpet_core` has `w_timer_running = timer_enable & hpet_enable` (line 406) and
`w_comp_write_rearm = w_timer_comp_write & ~w_timer_running` (407) -- armed-latch
set condition A3. With `timer_enable` gone, "stopped" means `!hpet_enable`
alone, so the contract *"a comparator write on a STOPPED timer always re-arms"*
becomes *"halt the whole HPET, or use VAL_SET_CNF, before reprogramming a
comparator"*. `w_timer_catchup` (486) also gates on `w_timer_running`. The
torn-64-bit-write protection at hpet_core.sv:100-106 depends on the same guard
and must survive the rework.

## COUNTER_CLK_PERIOD

**It is not a separate register: it is `GCAP_ID[63:32]`**, the HIGH half of the
64-bit capability register, which at 32-bit access width lands at offset 0x004.
So the LO/HI pairing applies to GCAP_ID too, and the owner's "004 is the clk
period" and the spec are the same statement.

RO, femtoseconds, fed by a new parameter. The counter ticks on
`CDC_ENABLE[0] ? hpet_clk : pclk`, so the value MUST track the cell:
10_000_000 fs (10 ns) for CDC cells, 20_000_000 fs (20 ns) for non-CDC, matching
the TB's `CORE_CLOCK_PERIOD`. Passing one fixed value would make the register lie
in exactly the cells whose tests predict timing from it.

**Bounds, worth an elaboration-time guard:** the spec caps the period at
0x05F5E100 = 100_000_000 fs = 100 ns, i.e. a 10 MHz MINIMUM counter frequency,
and zero is invalid -- FreeBSD's driver rejects a zero period outright. Software
derives frequency as 1e15 / period. Both our values are legal.

## Blast radius (hand-maintained only; build/log artifacts excluded)

RDL; `hpet_regs.sv`/`_pkg.sv` (regenerated); `hpet_config_regs.sv` (its
hardcoded `ADDR_HPET_STATUS = 9'h008` must become 0x020 or HPET_STATUS writes
land nowhere silently); `hpet_core.sv`; `apb4_hpet.sv`; `hpet_regmap.py`
(regenerated); `hpet_helper.py` (writes by NAME -- needs no change); `hpet_tb.py`
+ 3 suites (21 `TIMER_ENABLE` uses, all inside `timer_config` words, plus
`_configure_one_shot`); `dv/testplans/apb4_hpet_testplan.yaml`; 6 MAS pages
stating offsets + `ch05_registers/01_register_map.md` tables; wavedrom
`hpet_registers.json`/`.html`; 7 graphviz/dot sources; `rlb_top_tb.py` (probes
HPET at 0x000 -- stays valid).

`test_register_access` reads HPET_ID but asserts no fields, so the bit move
breaks no existing assertion. New tests must ADD spec-layout assertions.

**Completion Criteria:**
- [x] Offsets match the spec, including COUNTER_CLK_PERIOD at 0x004
- [x] GCAP_ID fields at spec positions; VENDOR_ID 16 bits
- [x] TIMn_CONF at spec positions, with PER_INT_CAP/SIZE_CAP read-only
- [x] `INT_ROUTE_CNF` and `INT_ROUTE_CAP` implemented (unblocks TASK-003)
- [x] `timer_enable` gone; re-arm contract reworked and re-documented
- [x] Regenerated via `bin/peakrdl_generate.py` (Rule #0)
- [x] Full regression green at REG_LEVEL=full; 18/18 with the suite one test LARGER
- [x] Docs synced in the same pass, including the MAS offset tables

## Why the wrong LEG_RT_CAP bit DISABLES legacy mode, not just mis-documents it

Real drivers gate on the capability bit. FreeBSD's `acpi_hpet.c` does

    if ((sc->caps & HPET_CAP_LEG_RT) == 0)
        sc->legacy_route = 0;

With `leg_rt_cap` at bit 5 instead of 15, a spec-conforming driver reads the
capability as ABSENT and refuses to use legacy replacement at all. So the bit
position is not cosmetic: it silently disables the feature TASK-003 exists to
build. The same driver writes the route as `t->caps |= (t->irq << 9)`, i.e.
`INT_ROUTE_CNF` at shift 9 is genuinely written by software and must be
functional rather than decorative.

## Explicit NON-GOAL: reserved-read behaviour

An undeclared offset inside the HPET window returns PSLVERR today. Traced:
`hpet_regs`' `s_cpuif_rd_err`/`s_cpuif_wr_err` feed `peakrdl_to_cmdrsp`'s
`regblk_rd_err`/`regblk_wr_err`, which drives `rsp_pslverr`. The spec says reads
of reserved space return 0, so this is a deviation -- but it is PRE-EXISTING and
unchanged by this task, and no test covers it either way.

The new map is sparser than the old one (58 four-byte holes in the global window
versus the same 58 today, since 0x018-0x0FC are ALREADY undeclared), so leaving
holes changes nothing about this behaviour. Declaring 58 reserved registers to
make them read as 0 is a separate decision; file it if it matters. Recorded here
so the next reader does not mistake it for something this task introduced.

**Dependencies:** none. **Blocks:** RLB/hpet TASK-003.

---

## Outcome (measured 2026-09-28)

**Regression: 18 passed / 0 failed** at `REG_LEVEL=full` after `clean-all`, and
the suite is one test BIGGER than the 18-passed baseline (basic 4/4 -> 5/5).
Basic 5/5 in 20 runs, medium 18/18 in 14, full 4/4 in 8.

`test_spec_register_layout` (new, basic suite) PASSED 20 times and asserts the
fields that MOVED -- not `num_tim_cap`, the one field whose position did not
change and which the pre-existing `test_register_access` already covered:

    HPET_ID = 0x80862101  vendor=0x8086 leg_rt=0 cnt_size=1 num_tim=1 rev=0x01
    HPET_ID = 0x10222202  vendor=0x1022 leg_rt=0 cnt_size=1 num_tim=2 rev=0x02
    HPET_ID = 0xABCD2710  vendor=0xABCD leg_rt=0 cnt_size=1 num_tim=7 rev=0x10
    HPET_PERIOD = 10000000 fs on CDC cells, 20000000 fs on non-CDC -- each
                  matching the clock the counter actually ticks on
    TIMER0 TN_CONF = 0x00000034  per_int_cap=1 size_cap=1 fsb_int_del_cap=0

It also proves the RO capability bits do not stick under a 0xFFFFFFFF write,
and that `TIMER_INT_ROUTE_CAP` reads 0 while no routing exists.

Other gates: `check_rdl_regen.py` rc=0 (hpet appears twice in its manifest --
the two .sv files and `hpet_regmap.py`, which needed a SECOND invocation with
`--regmap-output`; `--copy-rtl` alone left it stale). Verilator delta vs HEAD is
+2 MULTIDRIVEN and +1 UNUSEDPARAM, all inside the GENERATED regblock and package
(two new fields -> two more `field_combo` blocks; `COUNTER_CLK_PERIOD_FS` joins
the seven localparams already unread there). Links ratchet unchanged.

## Three self-inflicted regressions, and the single habit behind them

Worth recording because the shape repeated, not the symptom:

1. **Renamed `get_timer_reserved_addr`, missed its one caller** in
   `get_register_name` -- which runs on EVERY register access, so all 18 cells
   died on an identical `AttributeError`. I had swept the constants and field
   names but never the METHOD name. A mechanical used-vs-defined check over
   `HPETRegisterMap.*` plus `cls.*` (22 used, 39 defined) catches this in
   seconds and now runs before every regression.

2. **Dropping `timer_enable` changed a CONTRACT, and 17 sites depended on the
   old behaviour without ever naming it.** They wrote `TN_CONF = 0x00000000`
   meaning "stop this timer"; after the change that stops nothing, because
   `w_comp_write_rearm` gates on `~hpet_enable` alone. THREE then wrote a
   comparator expecting the A3 re-arm. Only ONE asserted and failed; the other
   two passed while no longer testing what their comments claimed. **A grep for
   `timer_enable` found none of them.** Fixed by halting `HPET_CONFIG` around
   each reprogram -- the pattern one test already used correctly.

3. **My own new test left a periodic timer armed.** Its 0xFFFFFFFF RO probe sets
   INT_ENB and TYPE, arming TIMER0 against the comparator the previous test left
   behind, on a running counter -- and `TN_CONF = 0` no longer disarms it. The
   stray fire landed after the last deassert, so the scoreboard's
   `len(asserts) != len(deasserts)` check failed exactly the three NON-CDC gate
   cells, where the 20 ns pclk places it there. CDC cells passed by luck. Fixed
   by halting the counter for the whole test (it only reads registers) and
   quiescing every timer at the end.

The habit: I swept the IDENTIFIER instead of the CALL SITES THAT DEPEND ON THE
BEHAVIOUR. For a contract change, write down what the old contract let callers
assume, then search for that PATTERN -- a two-line window scan ("wrote 0 to a
config register, then wrote a comparator") found all 17 sites and classified
them. And treat the still-PASSING sites as the hazard: a loud failure gets
fixed, a silent no-op reports green for years.

## Known deviation left in place, deliberately

An undeclared offset inside the HPET window returns PSLVERR, where the spec says
reserved reads return 0. Pre-existing, untouched here, and unchanged by the new
map (0x018-0x0FC were already undeclared). Recorded as a non-goal above.
