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

# The Dormant Pair (`scoria_powerdown_ctrl` + `scoria_dfi_signal_pack`)

**Module:** `scoria_powerdown_ctrl.sv`, `scoria_dfi_signal_pack.sv`
**Location:** `rtl/fub/`
**Category:** power-down / DFI pack
**Parent:** `— (dormant)`
**Status:** RETAINED DORMANT — nothing in the tree instantiates either block, deliberately

---

## Purpose

Both source files carry the same header: **RETAINED DORMANT — nothing in the tree instantiates this, deliberately**. They are kept as files because scoria's DDR3 design point does not need them, but a future LPDDR3 build does. This page documents what each block contains and why deleting them would be premature.

A grep across the scoria tree for instantiation patterns (`scoria_powerdown_ctrl #(` , `scoria_dfi_signal_pack #(` , `u_powerdown`, `u_dfi_signal_pack`) returns no matches. The only references are the module definitions themselves, their individual filelists, and the master `scoria_all.f` lint closure, which lists them explicitly for compile coverage.

## Parameters

| Parameter | Module | Default | Meaning |
|---|---|---|---|
| `NUM_BANKS` | `scoria_powerdown_ctrl` | 8 | banks per rank (unused today) |
| `CS_WIDTH` | `scoria_powerdown_ctrl` | `NUM_RANKS` | chip-select width |
| `NUM_RANKS` | `scoria_dfi_signal_pack` | 1 | rank count |
| `DFI_RATE` | `scoria_dfi_signal_pack` | 2 | DFI clock ratio |
| `DFI_ADDR_WIDTH` | `scoria_dfi_signal_pack` | 14 | per-phase address width |
| `DFI_BANK_WIDTH` | `scoria_dfi_signal_pack` | 3 | per-phase bank width |
| `DFI_DATA_WIDTH` | `scoria_dfi_signal_pack` | 64 | write-data width |

: Table 2.26.1: Dormant pair parameters

## Interface

### `scoria_powerdown_ctrl`

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mc_clk` | in | 1 | controller clock |
| `mc_rst_n` | in | 1 | active-low reset |
| `idle_threshold_i` | in | 16 | cycles of idle before arming |
| `enable_pde_i` | in | 1 | precharge power-down enable |
| `enable_sref_i` | in | 1 | self-refresh enable; takes priority over PDE |
| `controller_idle_i` | in | 1 | scheduler idle indication |
| `pdn_req_o` | out | 1 | power-down request to scheduler |
| `pdn_kind_o` | out | 1 | 0 = PDE, 1 = SR |
| `pdn_grant_i` | in | 1 | scheduler grant |
| `sref_active_o` | out | 1 | high while in self-refresh |
| `dfi_cke_o` | out | `CS_WIDTH` | CKE output; low in `S_ASLEEP` |
| `obs_state_o` | out | 3 | FSM state observability |
| `obs_idle_cnt_o` | out | 16 | idle-cycle counter |
| `obs_grants_pde_o` | out | 16 | PDE grants since reset |
| `obs_grants_sr_o` | out | 16 | SR grants since reset |

: Table 2.26.2: `scoria_powerdown_ctrl` ports

### `scoria_dfi_signal_pack`

| Signal | Direction | Width | Description |
|---|---|---|---|
| `mc_clk` | in | 1 | controller clock |
| `mc_rst_n` | in | 1 | active-low reset |
| `i_address`, `i_bank`, `i_cas_n`, `i_ras_n`, `i_we_n`, `i_cs_n`, `i_cke`, `i_odt` | in | various | pre-pack command inputs |
| `i_wrdata`, `i_wrdata_en`, `i_wrdata_mask`, `i_rddata_en` | in | various | pre-pack data inputs |
| `dfi_address_o`, `dfi_bank_o`, `dfi_cas_n_o`, `dfi_ras_n_o`, `dfi_we_n_o` | out | various | packed command bus |
| `dfi_cs_n_o`, `dfi_cke_o`, `dfi_odt_o` | out | `DFI_CS_BUS_W` | packed control outputs |
| `dfi_wrdata_o`, `dfi_wrdata_en_o`, `dfi_wrdata_mask_o`, `dfi_rddata_en_o` | out | various | packed data outputs |
| `dfi_dram_clk_disable_o` | out | `DFI_CS_BUS_W` | DRAM clock disable; the block's unique function |

: Table 2.26.3: `scoria_dfi_signal_pack` ports

## Microarchitecture internals

### `scoria_powerdown_ctrl`

The block has a four-state FSM:

```text
S_AWAKE  — CKE high, normal operation
S_ARMING — counting idle cycles toward entry
S_REQ    — pdn_req_o high, awaiting pdn_grant_i
S_ASLEEP — CKE low, in PDE or SR
```

Entry arms when `controller_idle_i` is true and either `enable_pde_i` or `enable_sref_i` is set. Self-refresh has priority over precharge power-down. On grant, the FSM moves to `S_ASLEEP` and drives `dfi_cke_o` low. It wakes on `!controller_idle_i`. The exit timing (`tXSDLL`, `tXSR`) is enforced by the scheduler, not this block.

The header also carries a v3 TODO list: deep-power-down entry, per-rank power-down, and a `dfi_init_complete` interlock.

### `scoria_dfi_signal_pack`

This is a one-cycle registered pipeline stage on the DFI bus. Its reset values produce a safe NOP: `cs_n = 1`, `ras_n = cas_n = we_n = 1`, `cke = 0`, `odt = 0`, write/read enable = 0, `wrdata_mask = 1`, and `dfi_dram_clk_disable = 0`. In normal operation it simply latches inputs; `dfi_dram_clk_disable_o` is held at 0 with a TODO for power-state integration.

The block owns `dfi_dram_clk_disable`. That signal is the reason it is retained: every other DFI signal scoria uses is already phase-multiplied by construction and does not need a separate pack stage, but deep power-down does need the clock-disable control.

### The four gaps

| Level | State today |
|---|---|
| `powerdown_ctrl` / `dfi_signal_pack` | not instantiated |
| `scoria_top` / `scoria_dfi_layer` | no `dfi_cke` or `dfi_dram_clk_disable` port |
| `scoria_dfi_cmd_formatter` | `OP_SREFE` / `OP_SREFX` / `OP_DPDE` fall to the `default:` arm and are driven as NOP |
| `scoria_cmd_arbiter` | never picks any of those three ops |

: Table 2.26.4: Why the dormant pair is not wired in the DDR3 design point

## FSM policy

`scoria_powerdown_ctrl` has a real FSM because power-down entry is a sequential lifecycle: detect idle, arm, request, sleep, wake. `scoria_dfi_signal_pack` has no FSM — it is a pure flop pipeline.

## Timing

Neither block contributes to the active DDR3 timing path because neither is instantiated. If they were wired, `powerdown_ctrl` would add a request-to-sleep latency of `idle_threshold_i` cycles plus scheduler grant latency, and `dfi_signal_pack` would add one cycle of registered delay on every DFI output.

## Notes

- **The DDR3 parity argument:** LiteDRAM's generated DDR3 core for the Genesys 2 board has no power-down or self-refresh engine. Its only `CKE` references resolve to a CSR bit that software raises during init and leaves high. scoria holding CKE high forever is therefore parity with a controller that passes memtest on this hardware, not a shortfall.
- **That argument does not transfer to LPDDR3:** Self-refresh is a mobile DRAM's normal idle state, and LPDDR3 adds Deep Power Down, which DDR3 does not have. DPD requires stopping the DRAM clock, which is exactly `dfi_dram_clk_disable_o`. The pair is load-bearing for LPDDR3, which is why both files stay.
- **Retention trap:** Keeping dormant code in the lint closure is only safe because the files are not instantiated. If someone adds an instance, all four gaps in Table 2.26.4 must be closed at the same time or the feature will silently issue NOPs.
- **TODO inheritance:** The v3 TODOs in `powerdown_ctrl` and v2 TODOs in `dfi_signal_pack` are preserved verbatim. They name the dependencies that an LPDDR3 integration would have to address.
