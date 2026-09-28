# TASK-033: the v2/v3 power and mode-register deferrals, and the one assumption hiding among them

**Priority:** P3 -- deferred scope, not defects. Nothing here is wrong today;
it is work the RTL says out loud it has not done.
**Status:** DEFERRED 2026-09-28 -- parked pending the DDR3/LPDDR3 project
(`scoria`). Sean: several of these are likely to be taken up there rather than
retrofitted here, and the ones that are not become dead comments to delete. The
named condition for unparking: scoria's design-requirements pass reaching the
power / mode-register surface, at which point each row below is either inherited
by scoria, implemented in pumice because scoria needs pumice to have it, or
removed from the RTL comment.
**Owner:** TBD
**Filed:** after a sweep for untracked TODO/FIXME markers found 9, of which 6 are
real deferred scope, 2 were stale docstrings (corrected in the same commit as
this filing) and 1 was not a TODO at all.

Filed because an empty tracker was being read as "no known work". These markers
were the counter-example: scope that only existed in source comments, where
nobody planning the next release would see it.

## The deferrals, as the RTL states them

| where | deferred |
|---|---|
| `rtl/fub/dfi_signal_pack.sv:14` | phase staggering -- per-phase output timing, e.g. delaying phase 1 by half a DFI cycle for double-data-rate command issue |
| `rtl/fub/dfi_signal_pack.sv:116` | `dfi_dram_clk_disable_o` is hard-tied `'0`; needs a power-state machine |
| `rtl/fub/mode_register.sv:25` | `mr_req_o` tied 0 -- no hot MR updates through the scheduler. Lands when the APB CSR slave offers a write-during-traffic path and the quiet-point handshake exists |
| `rtl/fub/mode_register.sv:89` | multi-rank assumes matching MR values across ranks; mixed MR per rank unsupported |
| `rtl/fub/mode_register.sv:116` | LPDDR2 BL16 clips to BL8; widening `bl_o` to [4:0] and updating its 3 downstream consumers is the fix |
| `rtl/fub/powerdown_ctrl.sv:23` | Deep Power Down entry (`enable_dpd_i`, LPDDR2 only); per-rank powerdown (currently all ranks together); `dfi_init_complete` interlock |

## Two of these are more than a list item

**Deep Power Down is blocked on a tie-off, and each file defers to the other.**
`powerdown_ctrl` says DPD "needs `dfi_dram_clk_disable_o` cooperation from
dfi_signal_pack"; `dfi_signal_pack` holds that line at `'0` pending "a
power-state machine". Neither is wrong on its own and neither can move alone --
so DPD is not two independent TODOs, it is one piece of work spanning two files,
and it will stay deferred as long as it is filed as two.

**`powerdown_ctrl` records an unverified assumption, not missing work:**

> `dfi_init_complete` interlock -- currently trusts the scheduler to not grant
> before init completes.

That is the only entry here that could be WRONG TODAY rather than absent. If the
scheduler ever granted a powerdown request before init completed, the controller
would power down a DRAM that had not been initialised, and nothing in the RTL
stops it -- the guarantee lives in another module's behaviour. It is also the
cheapest to settle: it needs a test that tries to grant early and asserts the
request is refused, not an implementation.

**Note on DPD's reachability:** it is LPDDR2-only, and there is no LPDDR2 FPGA
board (Sean, 2026-09-28), so DPD can never be validated on silicon here. That is
an argument for keeping it deferred, not for implementing it blind.

## Done when

Each row is either implemented, or has its own item with a reason, or is deleted
from the RTL comment because it is not going to happen. A TODO that survives
three release cycles unexamined is not a plan.

If it is unparked, suggested order -- cheapest and most load-bearing first.
Note that item 1 does NOT depend on scoria and could be done at any time; it is
a test against an assumption that is live in pumice today:

1. The `dfi_init_complete` interlock -- prove it or fix it. A test, not a feature.
2. LPDDR2 BL16 (`bl_o` widening) -- self-contained, and the only one with a
   JEDEC-conformance argument behind it.
3. DPD as ONE item spanning both files, if it is wanted at all given no board.
4. Hot MR updates and per-rank MR -- both wait on the CSR write-during-traffic
   path, so they are one piece of work too.
5. Phase staggering -- no consumer has asked for it.
