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

# `pumice_axi4_ifc` (AXI4 front-end macro)

**Module:** `pumice_axi4_ifc.sv`
**Location:** `rtl/macro/`
**Category:** Layer-1 macro (the AXI front-end of `pumice_core`)
**FUBs bundled:** burst splitters + 2 intakes + 2 CAMs

## Purpose

"Host AXI4 to CAM-cached DRAM requests." The first of the three core layers.
It bolts the shared AXI burst splitters onto dumb 1:1 intakes, holds the
write-data CAM (write buffer + snarf source) and the read-command CAM (read
reorder buffer), presents the host AXI4 face, and exposes the scheduler
lookup/oldest/commit/issue ports and the DFI wr-commit-data / rd-return ports
outward to the other two layers.

```
host AXI4 -> [wr/rd splitter] -> pumice_wr_intake -> pumice_wr_data_cam
                              -> pumice_rd_intake -> pumice_rd_cmd_cam
```

Runs entirely on `aclk`. This replaces the old `axi_frontend_macro`
(`axi_intake` / `addr_mapper` / `wr_cmd_cam` / `rd_cmd_cam` / `wr2rd_forward`) --
those names are retired.

## FUBs

| FUB                    | Role                                                                                              |
|------------------------|---------------------------------------------------------------------------------------------------|
| `axi_master_wr_splitter` / `axi_master_rd_splitter` | Shared AMBA IP; split each host burst at DRAM-burst-byte boundaries (`ALIGN_MASK = BL*(DRAM_BEAT_WIDTH/8) - 1`), one DRAM burst per split command |
| `pumice_wr_intake`     | `axi4_slave_wr` + AW-meta FIFO + wr-data FIFO + `addr_mapper`; emits `(bank,row,col,id)` push plus a wr-data stream; consumes commit-done for B response |
| `pumice_rd_intake`     | `axi4_slave_rd` + `addr_mapper` + snarf probe; emits `(bank,row,col,id)` push; probes the write CAM and, on a snarf hit, streams the R response from the write CAM SRAM; otherwise consumes the drained DFI return |
| `pumice_wr_data_cam`   | Write CAM keyed on (bank,row) + write-data SRAM; fill / commit-drain / snarf movers; oldest + N_SCHED_LU lookup + commit ports; commit-data out to the DFI write path |
| `pumice_rd_cmd_cam`    | Read CAM keyed on (bank,row) + read-return SRAM; return-fill / drain movers; oldest + N_SCHED_LU lookup + issue ports; DFI-return in, drain out to the rd intake |

Address decode (`addr_mapper`) is driven by `bank_lsb_i` / `hash_en_i` /
`hash_seed_i` (the `ADDR_MAP` CSR); there is no scheme selector. See section 4
of this MAS for the address-map field semantics.

## External Boundaries

- **Upstream:** the host AXI4 slave port (SoC-facing).
- **To `pumice_mem_cmd_scheduler`:** for each CAM, the `oldest_*` snapshot,
  the `N_SCHED_LU` parallel `sched_lu_*` lookup ports (`valid/bank/row` in,
  `hit/slot/col/id/age` out), and the write `commit` / read `issue` handshakes.
  The scheduler drives these on `aclk`.
- **To `pumice_dfi_layer`:** write commit-data out (`wr_cm_rd_*`:
  `valid/ready/data/strb/last`) to the DFI write serializer; read DFI return in
  (`rd_dfi_ret_*`: `valid/ready/data/resp/last`) from the DFI read aligner.
- **Internal:** the read intake's snarf probe hits `pumice_wr_data_cam`
  directly (`snarf_probe_*` -> `snarf_hit`/`snarf_rd_*`); the write CAM's
  `commit_done_*` retires the AW-meta FIFO entry in `pumice_wr_intake` to emit
  the B response.

The `busy_o` output is the OR of the four sub-block busy flags.

## De-FSM'd CAMs

Both CAMs store burst data in an SRAM and read it back with a streaming engine
that is FIFO-fed / oldest-pick beat-counter driven -- there is no active/slot
state machine. The `r_fdone` fill-complete flag gates when a slot is
schedulable (and, on the write side, snarfable). The write CAM's snarf mover is
the sole read-your-write forwarding path; there is no separate forwarder.

## Tests

FUB-level unit tests exist for each intake and each CAM
(`dv/tests/fub/`), and a wrapper-level test drives `pumice_axi4_ifc` through the
AXI4 BFMs (`AXI4MasterWrite`/`AXI4MasterRead` + `AXI4Sequence`). Drive AXI
traffic through the BFMs -- never hand-poke `s_axi_*`.
