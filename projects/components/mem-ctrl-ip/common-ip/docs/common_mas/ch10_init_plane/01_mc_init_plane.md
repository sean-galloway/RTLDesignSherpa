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

# `mc_init_plane` — DRAM Initialization Plane

> Filed as MAS chapter 10 (appended) to keep chapters 2–9's paths stable for
> the ~50 inbound doc links; in command-flow order the init plane sits
> between the storage plane and the scheduler plane — see the family HAS
> [plane stack](../../common_has/ch02_architecture/01_plane_stack.md), which
> is the binding statement of the architecture.

Extracted from `mc_scheduler_plane` on 2026-10-15 (spec:
`docs/superpowers/specs/2026-10-15-mc-init-plane-design.md`). Both xDDR2
rocks — granite (product) and pumice (research) — instantiate this plane
identically, so init work on one translates directly to the other. Scoria's
wrapper continues to use the scheduler plane's legacy internal-init mode
with its own rock-side sequencer; andesite is untouched.

## Responsibility

Own the DRAM bring-up concern end to end:

1. **JEDEC initialization sequencing** (`mc_xddr2_init_sequencer`) — the full
   DDR2 chain and the LPDDR2 MRW chain, issued to the DRAM (not shadowed),
   with CSR-backed inter-command waits.
2. **Mode-register shadow + live decode** (`mc_xddr2_mode_register`) — the
   per-rank MR image, written by the sequencer during bring-up, decoded to
   CL/CWL/BL for the rest of the controller.
3. **DFI PHY init handshake** — `dfi_init_start_o` / `dfi_init_complete_i`
   crossed to the DFI plane; the FSM parks in `S_DFI_INIT` until the PHY
   reports done.
4. **Init command injection** — the plane's `init_cmd_*` outputs feed the
   scheduler plane's external-init port; the pick core forwards them to the
   command formatter while `!init_done`, so init commands reach the DRAM
   unarbitrated.
5. **Bring-up telemetry** — `init_busy_o` and `init_state_o[4:0]`.

Explicitly not owned: scheduling, refresh, the CSR/APB hot-update path for
mode registers (future; `mr_seq_we` remains the only writer), and any
training/search logic (the training plane's job).

## Parameters and ports

| Parameter | Default | Meaning |
|---|---|---|
| `NUM_RANKS` | 1 | rank count (mode-register shadow banks) |
| `NUM_BANKS` | 8 | bank count (MR-index width on the MRS bank port) |
| `ROW_WIDTH` | 14 | row/MR-data width (`BKW = $clog2(NUM_BANKS)`) |

| Port | Dir | Width | Meaning |
|---|---|---|---|
| `mc_clk`, `mc_rst_n` | in | 1 | controller clock / active-low reset |
| `memtype_i` | in | `memtype_e` | DDR2 vs LPDDR2 chain select (sampled at the S_DFI_INIT exit and on restart) |
| `t_init_wait_i`, `t_dll_wait_i` | in | 16 | CKE/tINIT settle; DLL lock (tZQINIT on the LPDDR2 chain) |
| `t_mrd_wait_i`, `t_rp_wait_i`, `t_rfc_wait_i` | in | 8 | tMRD / tRP / tRFC post-command waits |
| `mr0_i` … `mr3_i` | in | 16 | DDR2 MR base values (CSR `MR0..MR3.VAL`) |
| `lp_mr1_op_i`, `lp_mr2_op_i`, `lp_mr3_op_i` | in | 8 | LPDDR2 MRW OP data (CSR `LP_MR1/2/3_OP`, JEDEC-default resets 0x23/0x01/0x02) |
| `init_restart_i` | in | 1 | rising-edge re-runs the chain with current CSR values (`CTRL.init_force_restart`) |
| `dfi_init_start_o` / `dfi_init_complete_i` | out/in | 1 | PHY init handshake (plane drives the DFI directly) |
| `init_cmd_valid_o`, `init_cmd_op_o`, `init_cmd_bank_o`, `init_cmd_row_o` | out | 1 / 5 / BKW / ROW_WIDTH | command injection into the scheduler plane external-init port |
| `init_busy_o`, `init_done_o` | out | 1 | FSM status |
| `init_state_o` | out | 5 | raw FSM state mirror — telemetry, not a stable ABI |
| `cl_o`, `cwl_o`, `bl_o` | out | 4 | live decode of the MR shadow (CL/CWL/BL) |

## The two JEDEC sequences

**DDR2** (waits in MC cycles; mirrors LiteDRAM's `get_ddr2_phy_init_sequence`,
proven on the Nexys A7): PREA → EMR2 → EMR3 → EMR1 → MR0+DLL_RESET → PREA →
REF → REF → MR0 (DLL reset cleared) → EMR+OCD-default → EMR+OCD-exit → done.
The MR shadow is written on EMR2/3/1, both MR0 loads, and the OCD-exit EMR;
the transient OCD-default load writes no shadow. MR0 is the CSR base
`mr0_i`; the first load ORs in the DLL-reset bit (0x100), the OCD-default
load ORs A[9:7]=111 (0x380).

**LPDDR2** (JESD209-2F §3.4/§3.5): MRW(MR63) Reset → MRW(MR10) ZQ Init →
MRW(MR1) BL/nWR → MRW(MR2) RL/WL → MRW(MR3) DS → done. The MR index (MA) and
data (OP) pack into the row request as `{MA[5:0], OP[7:0]}` (a 3-bit bank
port cannot reach MR10/63); the command formatter unpacks it for the CA MRW
word. Only MR1/2/3 update the shadow (as `{8'd0, OP}`); MR63/MR10 issue but
are not shadowed. The OP data is CSR-backed (`lp_mr*_op_i`) so software can
retune at bring-up — and sweep the values to defeat a scrambled CA/A-lane
board mapping, the same escape hatch the DDR2 `MRx.VAL` registers provide.

`init_state_o` encoding (raw FSM enum): S_RESET=0, S_DFI_INIT=1, S_PREA1=2,
S_EMR3=3, S_EMR2=4, S_EMR1=5, S_MR0_DLL=6, S_PREA2=7, S_REF1=8, S_REF2=9,
S_MR0=10, S_OCD_DEF=11, S_OCD_EXIT=12, S_WAIT=13, S_DONE=14, S_L_RESET=15,
S_L_ZQ=16, S_L_MR1=17, S_L_MR2=18, S_L_MR3=19.

## Configuration surface

The plane consumes no parameters beyond geometry; every timing and MR value
is a CSR port. Both rocks expose:

| CSR | Offset | Reset | Notes |
|---|---|---|---|
| `INIT_TIMING0` | 0x058 | t_init 512 / t_dll 256 | MC cycles — **these values are MC-frequency-dependent; re-derive them when the controller clock changes** |
| `INIT_TIMING1` | 0x05C | t_mrd 8 / t_rp 8 / t_rfc 16 | same frequency caution |
| `MR0..MR3.VAL` | 0x020–0x02C | MR0 = 0x433 | DDR2 base values |
| `LP_MR1_OP` | 0x180 | 0x23 | LPDDR2 MR1 OP (nWR/WC/BT/BL) |
| `LP_MR2_OP` | 0x184 | 0x01 | LPDDR2 MR2 OP (RL/WL) |
| `LP_MR3_OP` | 0x188 | 0x02 | LPDDR2 MR3 OP (drive strength) |
| `CTRL.init_force_restart` | 0x000 | 0 | rising edge re-runs the chain |

## Verification

- `common-ip/dv/tests/fub/test_mc_xddr2_init_sequencer.py` — directed: both
  chains (order/shadows/waits), LP OP sweep, restart level/memtype behavior,
  `dfi_init_complete` never/glitch negatives, state telemetry.
- `common-ip/dv/tests/macro/test_mc_init_plane.py` — both chains at the
  plane boundary + CL/BL decode.
- Integration: granite `test_granite_core` / `test_granite_top_geared`,
  pumice `test_pumice_top.py` (incl. `lp_mr_op_csr_sweep_lpddr2`, which
  sweeps the LP CSRs and verifies the values in the decoded CA MRW stream
  via `init_force_restart`).
