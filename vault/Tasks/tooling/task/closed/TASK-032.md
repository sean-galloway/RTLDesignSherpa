# TASK-032: un-waive IMPLICIT in the fpga lint gate + tie off amber direct-host pins

**Status:** CLOSED 2026-10-15 (commit 3afff8165). Filed and
completed in the same session, from the owner's green light on the tooling
follow-up floated at amber BUG-003 closure.
**Priority:** P2
**Filed from:** amber BUG-003 (Genesys 2 read hang, `uart_arvalid`/`uart_arready`
used but never declared in `amber_pair_harness.sv`). The two existing gates
both missed it: Verilator lint waived the whole IMPLICIT class
(`-Wno-IMPLICIT` in `make/fpga_flow.mk` LINT_WAIVERS), and
`bin/check_sv_decl_order.py` only flags signals that ARE declared but used
before their declaration — a never-declared identifier never enters its
signal dict, so the use-scan never looks for it.

What changed:

- `make/fpga_flow.mk`: `-Wno-IMPLICIT` removed from `LINT_WAIVERS`, with a
  comment recording why (Vivado scopes implicit nets per module, Verilator
  merges same-named ones → sims lint clean while synthesis ties the channel
  off; Verilator runs without `-Wno-fatal` so an IMPLICIT warning is now a
  hard lint failure).
- `projects/fpga-systems/Genesys2/cache-ip/amber/rtl/amber_pair_genesys2_top.sv`:
  the `amber_pair_harness` instantiation now ties the direct-host AXIL inputs
  to zero and leaves its outputs explicitly open (board top always services
  the host over UART; the direct-host path is sim/cocotb-only via
  `USE_DIRECT_HOST=1`).

Blast-radius measurement before landing the gate change: every fpga flow
that has a `lint` target (17 of 20 Makefiles including `fpga_flow.mk`) was
re-linted with IMPLICIT unwaived in parallel — **zero** `%Warning-IMPLICIT`
anywhere. The three non-passing flows fail for pre-existing, unrelated
reasons (scoria ×2: a `lint-decl-order` finding that fails under the default
waivers too; NexysA7 top-level Makefile: no `lint` target).

Gate teeth proven with a scratch module reproducing the BUG-003 shape
(undeclared identifier used only as a port-connection actual): new waiver
set → `%Warning-IMPLICIT` → rc=1 (fatal); old waiver set → rc=0 silent pass.
That silent pass is exactly how the bug shipped past every simulation.

Verification after landing:

- `make -C projects/fpga-systems/Genesys2/cache-ip/amber/build-bringup lint`
  → rc=0 (both `lint-decl-order` and Verilator lint, post tie-off, under the
  new default waiver set).
- Board state re-confirmed beforehand: `run_smoke.py --port /dev/ttyUSB1`
  → ALL PASS (20000/20000 per injector, err_flag=0, reads returning data) on
  the BUG-003-fixed functional bitstream.

Not done (deliberately): the pre-existing scoria `lint-decl-order` finding
and the missing NexysA7 `lint` target are separate items, out of scope here.
PINMISSING stays waived (documented integration choice for optional status
outputs).
