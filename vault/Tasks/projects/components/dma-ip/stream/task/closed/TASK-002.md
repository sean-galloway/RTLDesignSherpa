# TASK-002: gate the monitor regfile on a parameter (present + decoded)

> **Was `STREAM-MONREGS` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-24.

`USE_MON_REGS` now exists, defaults to `USE_AXI_MONITORS`, and does both halves
the title asks for: the monitor config outputs are strapped off, and the MON
window returns an error instead of answering.

## What was actually wrong

`stream_regs.rdl` instantiates the monitor regfile unconditionally (`MON @
0x1000`) while `USE_AXI_MONITORS` decides whether the monitors it configures
exist. With monitors off the registers still accepted writes and read back the
written value, driving nothing. A host arms `RDMON_TIMEOUT`, reads it back
correctly, and concludes the monitor is configured. There is no monitor.

Live on **two** shipping bitstreams, not one: `build-perf/Makefile:45` and
`build-obs/Makefile:57` both `export USE_AXI_MONITORS ?= 0`, and both
synthesized TCLs bake `USE_AXI_MONITORS=0` into the generics. The entry said
build-perf; it understated the reach by one build.

## What was done

**Half A — strap the config off** (`stream_config_block.sv`). A new
`parameter bit USE_MON_REGS = 1'b1` gates all **51** `cfg_*mon_*` assigns --
17 each across `cfg_desc_mon`, `cfg_rdeng_mon`, `cfg_wreng_mon`. Typed zeros
taken from this module's own PORT widths (18x `1'b0`, 6x `32'h0`, 27x `16'h0`),
NOT from RAPIDS: RAPIDS' `err_select` is `4'h0` while STREAM's is `[15:0]`, so
copying its literal would have planted a width mismatch.

**Half B — gate the decode** (`stream_top_ch8.sv`). A guard between the CDC and
the PeakRDL adapter returns an error response for `paddr[12]` (MON @ 0x1000,
APB_ADDR_WIDTH 13) when `USE_MON_REGS=0`. The address map is unchanged; only
the answer is.

Two constraints shaped it:
- **It cannot live in the regblock.** Generated `stream_regs` ties
  `cpuif_wr_err` to `'0` (:4817), so a MON WRITE can never be reported as
  failed from inside it. `cpuif_rd_err` only carries `readback_err`.
- **It cannot live in the .rdl.** PeakRDL has no conditional-instantiation
  construct. So the RDL is untouched and nothing was regenerated.

Shape follows the retired `cmdrsp_router` (deleted in `45fa4972e`, recovered
from git to copy rather than reinvent): combinational decode, selection
registered at command-accept and cleared at response-accept, response muxed on
the REGISTERED select so a stale response cannot leak. Safe because the
upstream is strictly one-outstanding -- `apb4_slave.sv:158` says so outright
("a command is issued on the IDLE->BUSY edge and its response is consumed in
BUSY") and `apb4_slave_cdc` wraps that same FSM behind its two CDC FIFOs, so
both `CDC_ENABLE` paths inherit it.

## Where the RAPIDS instruction did not fit

The entry said to follow RAPIDS rather than invent a second pattern. RAPIDS
supplies the parameter half only: `rapids_config_block.sv:45` straps its cfg
outputs off, but RAPIDS deliberately does NOT gate its decode -- its `.rdl`
says the monitor block can be dropped "without changing the base address map".
That is the very behaviour this task calls the defect, so the naming and
strap-off shape were followed and the decode guard added. RAPIDS therefore has
the same misleading readback; filed as rapids ISSUE-003 for the owner to rule
on, since holding the map stable across builds is a real and deliberate value.

## Proof it works (A/B, one variable)

`dv/tests/top/test_stream_top_mon_gate.py` -- the negative direction the entry
asked for. It asserts through the BFM packet's `pslverr` because
`StreamCoreTB.read_reg` returns `prdata` and **discards** the `pslverr` beside
it, so `read_reg` structurally cannot report an error response.

| build | result | wall clock |
|---|---|---|
| guard active (`USE_MON_REGS` defaulted from `USE_AXI_MONITORS=0`) | **1 passed** | 97.48 s |
| guard inert (`USE_MON_REGS=1`, monitors still absent) | **1 failed** | 103.23 s |

The mutation failed on all nine checks -- three registers x {WRITE without
PSLVERR, READ without PSLVERR, read back what was written} -- including
`DAXMON_ENABLE READ BACK the value just written (0x1)`, which is this task's
defect reproduced verbatim. `pytest-rerunfailures` retried 3x, same failure, so
it is not flaky. The build directory was deleted before the mutation run: a
reused `sim_build` would have kept the old guard compiled in and shown a false
"mutation did not bite".

The test carries its own vacuity guard. `cocotb_bus` gates OPTIONAL signals on
a case-SENSITIVE `hasattr`, and this DUT's ports are lowercase
(`s_apb_pslverr`); CocoTBFramework's `_match_optional_case` rebinds them, but if
that regresses, `pslverr` reads 0 forever and every check passes while checking
nothing. The test asserts `is_signal_present('PSLVERR')` first. It also runs a
non-MON positive control (`GLOBAL_CTRL`, 0x100, bit 12 clear) before AND after
the blocked accesses -- the "after" catches the failure this guard could
plausibly introduce, which is apbx-xbar's APBX-002: a decode miss that leaves
`cmd_ready` low forever and wedges the bus.

Lint is unchanged from a pre-edit baseline: 79 sources, RC=0, 0 errors, 187
warnings (135 MULTIDRIVEN + 52 WIDTHEXPAND) before and after.

## Corrections to this entry as filed

- **The `APB_ADDR_WIDTH` note was stale.** It said the MON window needs 13 bits
  and "at the 12-bit default every monitor register returns 0xDEADBEEF". The
  default is ALREADY 13 (`stream_top_ch8.sv:61`); that had been fixed.
- **The 0xDEADBEEF framing was wrong, and it matters.** Nothing in this DUT's
  closure drives that value -- it appears only as an `LFSR_SEED` in
  `rtl/amba/shared` and as `axi4_subtractive_slave`'s READ_FILL. The real
  12-bit mechanism was address TRUNCATION: `RDMON_ENABLE 0x10E0 -> 0x0E0`
  (unmapped) and `WRMON_ENABLE 0x1100 -> 0x100`, which is `GLOBAL_CTRL` -- a
  MON write silently landing on the DMA's global control register. That is a
  worse failure than the sentinel it was described as.

## Left undone, deliberately

- `test_stream_top_mon_cfg.py` treats `0xDEADBEEF` as a no-response sentinel.
  Nothing can drive it, so that branch is dead code -- an assertion that cannot
  fire. Recorded in [[TASK-003]]. (Its sibling in `test_stream_top_regs.py` was
  the SAME defect but was NOT left undone -- see the correction below.)
- 52 pre-existing `WIDTHEXPAND` warnings on this same monitor config path
  (`cfg_desc_mon_err_select`: 16-bit port against a 4-bit wire at the top; the
  masks: 16-bit ports against 8-bit wires). Untouched by this work and
  unchanged in count, but they are a real width mismatch on the signals this
  task is about.

---

## Correction, same day: this task had a regression gate and I did not run it

The entry above was written and pushed before I discovered that
`dv/tests/top/test_stream_top_regs.py` already carried a gate for this exact
task:

```python
@pytest.mark.xfail(strict=False,
    reason="STREAM-MONREGS: the monitor regfile is instantiated unconditionally
            (stream_regs.rdl:758), so it answers even when USE_AXI_MONITORS=0.
            This test is the regression gate for gating it.")
def test_stream_top_regs_monitors_absent(...)
```

`STREAM-MONREGS` is this task's pre-rename ID. A test written to flip when this
fix landed, and I shipped the fix without ever running it. A grep for
`TASK-002` would not have found it; only the old ID appears in the code.

**It did not flip, and that was the more serious half.** Its predicate was
`got != 0xDEADBEEF`, and nothing in this DUT's closure drives that value, so
after the fix it still scored all 86 MON registers as "still responding" and
stayed XFAIL -- a gate structurally unable to observe the fix it guarded. With
`strict=False` an XPASS would have reported as passed too, so the suite was
green either way and nothing surfaced it. My "Left undone" bullet called this a
dead branch for [[TASK-003]]; that understated it. It was this task's own gate.

**Fixed here, not deferred:**
- `StreamCoreTB` gained `last_rsp_pslverr`, captured in BOTH
  `read_apb_register` and `write_apb_register`. The APB master already recorded
  the flag (`transaction.fields['pslverr']`) and this TB discarded it, which is
  why `read_reg` could not tell "answered 0" from "refused". Additive: an
  attribute, not a changed return type, so all 8 call sites are untouched.
  `write_apb_register`'s docstring also claimed to return an `APBPacket`; it
  never has, and now says so.
- All three sentinel predicates in `test_stream_top_regs.py` moved onto the real
  error response; `NO_RESPONSE = 0xDEADBEEF` deleted.
- The `xfail` removed. The gate now PASSES.
- A vacuity guard added: the checks rest on PSLVERR having BOUND, and
  `cocotb_bus` gates optional signals on a case-SENSITIVE `hasattr` while this
  DUT's ports are lowercase. If `_match_optional_case` ever regresses the flag
  reads 0 forever -- monitors-absent would fail loudly, but monitors-present
  would SILENTLY stop detecting unreachable registers, the same blind spot the
  sentinel had.
- The summary line reported only the write/readback phase, which `gate` skips,
  so a passing gate run logged "0 write/readback checks, 0 read-only registers,
  0 failures" -- a green run stating it verified nothing. It now counts the
  reset sweep and the MON-absence walk, and ASSERTS the total is non-zero.

**Measured, both cells, one parameter apart:**

| cell | before this correction | after |
|---|---|---|
| `monitors_absent` (USE_AXI_MONITORS=0) | XFAIL | **PASSED** |
| `monitors_present` (USE_AXI_MONITORS=1) | PASSED | **PASSED** |

Complementary evidence rather than a bare pass: the same 86 MON registers are
read in both builds -- all 86 refused with PSLVERR when the monitors are absent,
0 refused when they are present.

Lesson recorded as [[feedback_find_the_existing_gate]]: before closing a task,
grep the suite for its ID, old and new.
