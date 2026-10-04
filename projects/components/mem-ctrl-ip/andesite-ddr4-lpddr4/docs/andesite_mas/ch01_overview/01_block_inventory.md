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

# Block Inventory

The MAS documents the changed and new blocks below, one page per chapter in
`ch02_blocks/`. Each page follows the house FUB-page skeleton: header
metadata, purpose, parameters, interface, microarchitecture internals, FSM
policy, timing, and notes — the skeleton the bch MAS established and the
pumice MAS before it. Markings are copied from the HAS, not re-derived; a
marking here that disagrees with the HAS is a defect here.

| Block | Marking | MAS page | HAS pointer |
|---|---|---|---|
| `dfi_cmd_formatter` (+ NEW LPDDR4 CA submodule) | MODIFIED / NEW | [ch02_blocks/01_cmd_formatter.md](../ch02_blocks/01_cmd_formatter.md) | Ch 3.2, 3.6 |
| `init_sequencer` | MODIFIED | [ch02_blocks/02_init_sequencer.md](../ch02_blocks/02_init_sequencer.md) | Ch 3.2 |
| `mode_register` | MODIFIED | [ch02_blocks/03_mode_register.md](../ch02_blocks/03_mode_register.md) | Ch 3.2 |
| `addr_mapper` | MODIFIED | [ch02_blocks/04_addr_mapper.md](../ch02_blocks/04_addr_mapper.md) | Ch 3.1 |
| `mem_cmd_scheduler` + `cmd_arbiter` | MODIFIED | [ch02_blocks/05_scheduler.md](../ch02_blocks/05_scheduler.md) | Ch 3.1 |
| `refresh_ctrl` | MODIFIED | [ch02_blocks/06_refresh_ctrl.md](../ch02_blocks/06_refresh_ctrl.md) | Ch 3.4 |
| `zq_ctrl` (+ NEW LPDDR4 MPC submodule) | INHERITED / NEW | [ch02_blocks/07_zq_ctrl.md](../ch02_blocks/07_zq_ctrl.md) | Ch 3.2 |
| `odt_ctrl` | NEW | [ch02_blocks/08_odt_ctrl.md](../ch02_blocks/08_odt_ctrl.md) | Ch 3.5 |
| training interfaces (`wrlvl_ifc`, `rdlvl_ifc`, `ca_train_ifc`) | MODIFIED / NEW | [ch02_blocks/09_training.md](../ch02_blocks/09_training.md) | Ch 3.3 |
| DFI datapath (`dfi_cmd_path`, `dfi_rd_aligner`, `dfi_wr_serializer`, `dfi_layer`) | MODIFIED | [ch02_blocks/10_dfi_datapath.md](../ch02_blocks/10_dfi_datapath.md) | Ch 3.5, 4.1 |

: Table 1.1: MAS block inventory — the changed and new blocks, one page each

Ten pages, matching the ten areas the HAS's Chapter 3 argues: the command
encoding, init, mode registers, address mapping, scheduling, refresh, ZQ,
ODT, training, and the DFI datapath. The kmap book's citations point into
these pages' mechanism sections; where a page names an encoding or a decode
equation, that line is an anchor.

## Referenced, not rewritten: the inherited set

The inherited-unchanged blocks are not MAS pages. Each is specified by
scoria's book and its RTL header, and this MAS states where and why:

| scoria module | Marking | Where its specification lives | Why not rewritten here |
|---|---|---|---|
| `scoria_top`, `scoria_top_geared`, `scoria_core`, `scoria_axi4_ifc` | INHERITED | scoria HAS Ch 2.3 / 4.2 and the `rtl/top/` + `rtl/macro/` headers | structure and host side unchanged; andesite's deltas do not reach them |
| `bank_timer` / `bank_timers`, `page_policy`, `rd_cmd_cam`, `wr_data_cam` | INHERITED | scoria HAS Ch 2.3 and the `rtl/fub/` headers | the scheduling *mechanism* is unchanged; only what the arbiter asks of it (the L/S pairs) is new, and that belongs to the scheduler page |
| `rd_intake`, `wr_intake`, `wr_splitter`, `rd_return_ring`, `axi_burst_chopper` | INHERITED | scoria HAS Ch 2.3 / 4.2 | the host-side front end is untouched by this generation |
| `dfi_cdc` | INHERITED | scoria HAS Ch 2.3 / 4.1 | the CDC shape transfers to DFI 4.0 unchanged (HAS Ch 4.1) |
| `cmd_history_checker` | INHERITED | scoria HAS Ch 2.3 | mechanism inherited; its DDR4 spacing-parameter growth is named on the scheduler page, where the parameters are defined |
| `powerdown_ctrl`, `dfi_signal_pack` | DORMANT | andesite HAS Ch 3.1 | carried dormant with the waking condition named there; a dormant block has no mechanism news to specify |

: Table 1.2: The inheritance list — referenced to scoria's books, with the where and the why

The rule both tables enforce: the MAS expands the HAS's changed/new blocks;
it does not re-derive, re-mark, or silently restate anything the HAS and
scoria's books already settle.
