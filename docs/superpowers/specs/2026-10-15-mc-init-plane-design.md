# mc_init_plane — common init plane for granite & pumice

Date: 2026-10-15
Status: design approved by owner (scope: extract plane + close gaps)
Applies to: `projects/components/mem-ctrl-ip/` (common-ip, product-ip/granite-ddr2-lpddr2, research-ip/pumice-ddr2-lpddr2)

## Goal

Elevate DRAM initialization from a hidden child of `mc_scheduler_plane` into a
first-class common plane, `mc_init_plane`, and close the LPDDR2 init gaps in
the same pass. Everything lands in `common-ip` (plus CSR wiring in both
products), so work done for granite translates directly to pumice — both cores
instantiate the identical plane.

## Why

- The plane architecture (axi / storage / scheduler / training / dfi) has no
  init plane; init is buried in the scheduler plane's `HAS_INIT_SEQUENCER`
  generate even though it is an end-to-end concern (JEDEC sequence, MR shadow,
  DFI PHY handshake).
- The scheduler plane already exposes an external init port
  (`init_cmd_valid/op/bank/row_i`, `init_done_i`) — added for scoria, which
  already runs `HAS_INIT_SEQUENCER=0, HAS_MODE_REGISTER=0` with its own
  sequencer. Granite/pumice tie that port off today.
- LPDDR2 init MR1/MR2/MR3 OP values are hardcoded localparams while the DDR2
  path's MRs are CSR-backed — LPDDR2 cannot use the "sweep MR values to
  defeat a scrambled A-lane mapping" escape hatch the DDR2 path has.
- Init has no fub/macro-level DV: no directed sequencer test, no
  `init_restart` test, no init-error injection, no runtime-ZQ / DQ-cal test
  (TASK-042 / GAP G-16 verification gap).

## Non-goals (YAGNI)

- No CA training, no per-boot read-leveling integration (PHY/host-side flow,
  unchanged).
- No CSR hot-update path for MRs (the `mc_xddr2_mode_register` doc already
  marks it future; `mr_seq_we` remains the only writer).
- No change to andesite/scoria. Observation only: andesite's scheduler-plane
  wrapper takes the `HAS_INIT_SEQUENCER` default (=1, the xddr2-gen
  sequencer); that predates this change and is a separate question for the
  andesite lane.
- No board re-run required: default behavior is bit-identical.

## Design

### 1. `mc_xddr2_init_sequencer` (fub change)

- Replace localparams `LPDDR2_MR1_OP/MR2_OP/MR3_OP` with input ports
  `lp_mr1_op_i[7:0]`, `lp_mr2_op_i[7:0]`, `lp_mr3_op_i[7:0]`.
  JEDEC-fixed items (MR63 OP, MR10 OP=0xFF, MR indices) stay localparam.
- Add `init_state_o[4:0]` — registered FSM state mirror for bring-up
  telemetry (debugging init stalls, e.g. PHY `init_complete` never returns).
- Everything else unchanged (both JEDEC chains, waits, restart pulse detect).

### 2. `mc_init_plane` (new common-ip macro)

`common-ip/rtl/macro/mc_init_plane.sv` + filelist
`common-ip/rtl/filelists/macro/mc_init_plane.f`.

Contents: `mc_xddr2_init_sequencer` + `mc_xddr2_mode_register` (the two
children currently inside the scheduler plane's generates). Params:
`NUM_RANKS, NUM_BANKS, ROW_WIDTH`.

Ports:
- clk/rst: `mc_clk`, `mc_rst_n`
- config in: `memtype_i`; init timing CSRs `t_init_wait_i`, `t_dll_wait_i`,
  `t_mrd_wait_i`, `t_rp_wait_i`, `t_rfc_wait_i`; `mr0_i..mr3_i`;
  `lp_mr1_op_i..lp_mr3_op_i`; `init_restart_i`
- DFI handshake: `dfi_init_start_o`, `dfi_init_complete_i` (plane drives the
  DFI directly; cores stop routing this through the scheduler plane)
- command injection out (to scheduler plane external init port):
  `init_cmd_valid_o`, `init_cmd_op_o`, `init_cmd_bank_o`, `init_cmd_row_o`
- status: `init_busy_o`, `init_done_o`, `init_state_o[4:0]`, `cl_o`,
  `cwl_o`, `bl_o` (decoded from the mode-register shadow)

### 3. Scheduler plane

No RTL removal. The `HAS_INIT_SEQUENCER` / `HAS_MODE_REGISTER` generates
stay (andesite path = default 1; scoria = 0). Granite and pumice cores flip
both params to 0 and feed the external init port from `u_init_plane`;
`cl_o/cwl_o/bl_o` come from the init plane instead.

### 4. Cores

`granite_core.sv` and `pumice_core.sv`:
- instantiate `u_init_plane`;
- scheduler plane: `.HAS_INIT_SEQUENCER(1'b0), .HAS_MODE_REGISTER(1'b0)`;
- DFI init handshake wired init-plane → dfi-plane directly;
- +3 input ports `lp_mr1_op_i/lp_mr2_op_i/lp_mr3_op_i`;
- `cl_o/cwl_o/bl_o` outputs now driven from the init plane.

### 5. CSR

Add to **both** `product-ip/granite-ddr2-lpddr2/regs/granite_csr.rdl` and
`research-ip/pumice-ddr2-lpddr2/rtl/macro/pumice_csr.rdl`:

- `LP_MR1_OP` (8-bit, reset 0x23), `LP_MR2_OP` (8-bit, reset 0x01),
  `LP_MR3_OP` (8-bit, reset 0x02) — JEDEC defaults, so out-of-reset behavior
  is bit-identical to today.

Registers are appended at the end of the addrmap (following the map's
existing offset convention) so no existing register address changes. Regenerate with
`bin/peakrdl_generate.py`; `bin/check_rdl_regen.py` must pass. Wire
`hwif_out.LP_MR{1,2,3}_OP.value` to the core ports in `granite_top_geared.sv`
and `pumice_top.sv`. Regenerated regmap/header artifacts are committed.

### 6. DV (common-ip)

New tests (repo pytest flow, verilator only, per AGENTS.md):

- `common-ip/dv/tests/fub/test_mc_xddr2_init_sequencer.py` (new dir):
  - DDR2 chain: exact command order (PREA, EMR2, EMR3, EMR1, MR0|DLL_RST,
    PREA, REF, REF, MR0, OCD-def, OCD-exit) with shadow writes and
    inter-command waits (short CSR waits);
  - LPDDR2 chain: MRW63/10/1/2/3, `{MA,OP}` row packing, shadows only on
    MR1/2/3, OP data follows the new CSR ports (sweep values);
  - `init_restart` pulse re-runs the chain with current CSR values;
  - negative control: `dfi_init_complete` held low → parked in S_DFI_INIT, no
    commands, `init_state_o` shows it;
  - `init_state_o` telemetry values per phase.
- `common-ip/dv/tests/macro/test_mc_init_plane.py`: both chains at the plane
  boundary; CL/BL decode after DDR2 init (MR0=0x433 default → CL3, BL8);
  MR shadow readback via the plane's cl/cwl/bl outputs.
- `common-ip/dv/tests/macro/test_mc_training_plane.py` (TASK-042/G-16
  verification): runtime ZQ interval expiry → ZQCS (short interval) / ZQCL
  (long interval) request on the `trn_cmd` channel, grant, completion,
  overdue counter behavior with defer; DQ cal start → MRR32/MRR40 command
  issue, `cal_data` return path, busy/done/err; both gated
  `memtype==LPDDR2`.

### 7. Regression nets (must pass before commit)

- New: all tests in §6.
- Existing: `product-ip/granite-ddr2-lpddr2/dv/tests/top/` (core, geared,
  bankfifo-debug), `common-ip/dv/tests/macro/test_mc_store_arbiter_contract.py`,
  `research-ip/pumice-ddr2-lpddr2/dv/tests/top/` suites,
  `ddr2_char_framework/dv/tests/test_granite_char_uart.py` (uart smoke),
  harness lint (`make lint` in the NexysA7 granite target area).

### 8. Docs

- `common-ip/docs/common_has/ch02_architecture/01_plane_stack.md` — init
  plane added to the stack diagram/section.
- New `common-ip/docs/common_mas/` chapter for `mc_init_plane` (ports, child
  fubs, sequences, register surface).
- `product-ip/granite-ddr2-lpddr2/config/product_config.md` — stack list
  updated (init plane).
- Pumice HAS (`06_what_moved_to_common.md`, init-sequences chapter) — init
  plane + LP MR CSRs.
- Register-map docs for both products (three new CSRs; note that init-timing
  CSR values are MC-frequency-dependent — the standing HAS note).
- `vault/Tasks/.../TASK-042.md` — status note: runtime-ZQ RTL already common;
  macro-level verification test added here; board exercise still open.

## Risks

- **Address map churn**: mitigated by appending new registers (§5).
- **Bit-identical default**: LP OP resets equal the old localparams; DDR2 path
  untouched; scoria/andesite wrappers untouched. Regression nets in §7 catch
  any drift.
- **init_state_o encoding** is the raw FSM enum (5-bit) — documented as
  telemetry, not a stable ABI.
