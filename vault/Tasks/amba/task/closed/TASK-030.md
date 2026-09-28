# TASK-030: EXAMPLES — CLOSED 2026-08-27: resolved by deletion, plus the residue it left

> Migrated 2026-09-27 from `vault/Tasks/amba/closed.md` as **AMBA-INTEG** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** CLOSED (option 1, "Retire", taken -- see the decision list in the
original text below)

The RTL was deleted in `01d1c3e6` ("removed old integ_* code that was used for
bfm development"), which took BOTH `rtl/integ_amba/` and `rtl/integ_common/`.
Sean asked whether it was already gone; it was -- but the deletion left residue
in four places, and no tooling flagged any of it (deletion 2026-08-19, found 2026-08-27):

  * `bin/filelists.toml` still declared both areas, pointing at directories
    that no longer existed;
  * `docs/markdown/rtl-integ-amba/` and `rtl-integ-common/` -- two whole doc
    books, 11 pages total, documenting deleted modules;
  * `docs/markdown/index.md` linked both books in two places, one of them
    still saying "2 modules -- currently not building, see
    AMBA-INTEG-EXAMPLES";
  * `docs/DOCUMENTATION_INDEX.md` listed integration examples as repo
    structure item 3.
  The review pipeline was still bundling both books, so a future qc round
  would have spent units reviewing docs for code that does not exist.

ROOT CAUSE, and the reason this is worth reading: `filelist_registry.py
--check` PASSED the whole time. `rglob("*.sv")` on a missing directory yields
nothing, so a dead area reports "[OK] 0 modules, 0 uncovered" and passes
forever. That is the SAME blind-spot class this registry was built to close,
one level up -- the original task said "a module can hide by having too little,
not just by being wrong"; it turns out an AREA can hide by not existing.
Fixed: --check now fails on an rtl_root that is not a directory, mutation-
verified with an injected ghost area (FAIL, exit 1) and the clean tree still
PASS.

Original analysis kept below for the record.

### Original filing (2026-07-26), kept for the decision list

*This was a second `## AMBA-INTEG-EXAMPLES` heading in `open.md`, directly under the CLOSED one. The closed block refers to "the original text below", so the two were one entry that a duplicate heading split in half -- and the split is why the tracker counted this task as both closed and open. Rejoined 2026-09-14.*
**Status:** open 2026-07-26
**Priority:** P2 (nothing depends on them, but `make verilator` at rtl/ is RED)

`rtl/integ_amba/examples/apb4_peripheral_subsystem.sv` (340 lines) and
`apbx_xbar_monitored.sv` (364) do not elaborate: **51 Verilator errors**, all
PINNOTFOUND. They instantiate `apb4_monitor` with an interface it no longer has.

| the examples pass | `apb4_monitor` actually takes |
|---|---|
| `pclk`, `presetn` | `aclk`, `aresetn` |
| `psel`, `penable`, `pwrite`, `paddr`, `pwdata`, `pready`, `prdata`, `pslverr` | `cmd_valid`/`cmd_ready` + `cmd_pwrite`/`cmd_paddr`/`cmd_pwdata`/`cmd_pstrb`/`cmd_pprot`, and `rsp_valid`/`rsp_ready` + `rsp_prdata`/`rsp_pslverr` |

Both files are **unchanged since the initial commit (2025-11-01)**; `apb4_monitor`
was redesigned underneath them. They are its ONLY consumers anywhere in the tree
— no test, no project, no doc references either file.

### Why nobody noticed for nine months

`rtl/integ_amba` had modules but no filelists, no registration and no Makefile,
so it was invisible to `--check` (unregistered) **and** to `--blindspots` (the
orphan scan looks for `.f` files no area covers, and an area with no `.f` at all
has nothing to find). A module can hide by having too little, not just by being
wrong. Registering it (`0c822bd5`) is what surfaced this.

### The shape of the fix

The APB family splits cleanly, and the examples are on the wrong side of it:

- **Bridges** — `apb4_master{,_cg,_stub}`, `apb4_slave{,_cg,_cdc,_cdc_cg,_stub}`
  and the 8 `apb5_*` equivalents — carry BOTH raw APB (`s_apb_PSEL`, ARM
  uppercase) and `cmd_*`/`rsp_*`.
- **Observers** — `apb4_monitor`, `apb5_monitor`, `apb_monitor_addr_check` —
  are cmd/rsp only. That is deliberate: it makes a monitor
  protocol-version-agnostic, since APB4 and APB5 bridges hand it the same shape.
- The monitor is a **sibling, not a submodule**: no bridge instantiates it. You
  tap the bridge's handshake.

So the correct structure is to insert a bridge and tap it:

    raw APB ──> apb4_slave ──cmd/rsp──> fabric
                     └── tap cmd_*/rsp_* ──> apb4_monitor ──> monbus

`apbx_xbar_thin` was raw-APB on both sides (lowercase
`s_apb_psel`/`m_apb_psel`), which is why `apbx_xbar_monitored` had raw APB in
hand and fed it straight to a monitor that stopped accepting it.

### Decide first, then do

1. **Retire** — delete both and the area. They demonstrate an API that is gone
   and nothing uses them. Cheapest and honest.
2. **Rewrite** against the bridge-tap structure above. Worth it only if a worked
   `apb4_monitor` integration example is wanted — there is none anywhere else in
   the repo today, which is arguably the entire point of `rtl/integ_amba`.

If rewriting: lint-clean is the floor, and add a smoke test under
`val/integ_amba/` taking its sources from
`rtl/integ_amba/filelists/<module>.f`. Without a test they rot again exactly as
they did — nine months, undetected, because nothing ever compiled them.

**Do not just delete the area registration to make the sweep green.** The
registration is what found this; reverting it re-hides the problem.

---
