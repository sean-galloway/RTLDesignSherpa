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

# Module Hierarchy

The controller is decomposed into **five layers under `pumice_core`**:
`mc_axi4_layer`, `mc_storage_layer`, `pumice_scheduler_layer`,
`pumice_training_layer`, and `mc_dfi_2p1_layer`. The first, second, and fifth
are shared common-ip layers; `pumice_scheduler_layer` and
`pumice_training_layer` are thin pumice-specific wrappers around the common
`mc_scheduler_layer` core and `mc_training_layer` shell. Each FUB is
independently verified at the unit level; each layer is verified as an
integration ("macro") unit. See [FUB Breakdown](05_fub_breakdown.md) for the
per-FUB role descriptions and [Chapter 3](../ch03_architecture/) for the
behavioral details.

## Hierarchy Tree

![Module Hierarchy](../assets/mermaid/02_module_hierarchy.png)

**Source:** [02_module_hierarchy.mmd](../assets/mermaid/02_module_hierarchy.mmd)

## Layered Organization

```
SoC level
└── pumice_top_geared            ← OPTIONAL host-width wrapper
    │                              (axi4_dwidth_converter_wr/_rd when HOST != DW)
    └── pumice_top               ← instantiated by the SoC
        ├── pumice_csr           ← PeakRDL passthrough cpuif register block
        └── pumice_core          ← the controller proper
            ├── mc_axi4_layer            ← common-ip; host AXI + descriptor push
            ├── mc_storage_layer         ← common-ip; wr/rd CAMs + bank image
            ├── pumice_scheduler_layer   ← thin wrapper around common mc_scheduler_layer
            ├── pumice_training_layer    ← thin wrapper around common mc_training_layer
            └── mc_dfi_2p1_layer         ← common-ip; single CDC + DFI v2.1 datapath
```

The single controller-to-PHY clock crossing for the datapaths lives inside
`mc_dfi_2p1_layer` (common-ip async FIFOs only). The training layer owns one
small sideband crossing of its own (`cal_expect` down, captured MRR data up)
for the read aligner's calibration capture — see
[Training](../ch03_architecture/09_training.md). The host AXI interface, CAMs,
and command scheduler all run on `aclk`; the DFI command path, write serializer,
and read aligner run on `dfi_clk`.

## Layer Groupings

| Layer / macro | Ownership | FUBs |
|---|---|---|
| `mc_axi4_layer` | common-ip | AXI4 slave intakes, shallow FIFOs, burst chop/split, final coalescing, read-data return endpoint ([common_mas ch02](../../../../../common-ip/docs/common_mas/ch02_axi4_layer/01_mc_axi4_layer.md)) |
| `mc_storage_layer` | common-ip | wr/rd CAMs, read snooping, per-bank open-row image ([common_mas ch03](../../../../../common-ip/docs/common_mas/ch03_storage_layer/01_mc_storage_layer.md)) |
| `pumice_scheduler_layer` | pumice wrapper | `mc_scheduler_layer` core ([common_mas ch04](../../../../../common-ip/docs/common_mas/ch04_scheduler_layer/01_mc_scheduler_layer.md)); rock children `init_sequencer`, `mode_register`, `refresh_ctrl`, `pumice_page_policy`, `pumice_cmd_history_checker` |
| `pumice_training_layer` | pumice wrapper | `mc_training_layer` shell ([common_mas ch05](../../../../../common-ip/docs/common_mas/ch05_training_layer/01_mc_training_layer.md)); rock children `pumice_zq_ctrl`, `pumice_lp_cal` |
| `mc_dfi_2p1_layer` | common-ip | single CDC, command formatter/pipeline, write serializer, read aligner ([common_mas ch07](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_layer/01_mc_dfi_2p1_layer.md)) |
| `pumice_core` | pumice | wraps the five layers above |

Also present in the tree but not in the default top build: `page_predictor`
and `powerdown_ctrl` (referenced / optional; verify against the filelists in
`rtl/filelists/`).

Chapter 3 follows the layer ordering (one section per architectural layer,
with module names hyperlinked to their MAS chapters).

## Memtype-Conditional Logic

Memtype (DDR2 vs LPDDR2) is a runtime CSR selection (`PHY_TIMING.memtype`),
not an elaboration parameter. The memtype-dependent logic lives in:

- **`mc_dfi_2p1_layer`** — its command formatter contains a memtype branch:
  DDR2 drives ras/cas/we; LPDDR2 packs the 10-bit JESD209-2F CA-bus command
  (two edges) onto `dfi_address` ([common_mas ch07](../../../../../common-ip/docs/common_mas/ch07_dfi_2p1_layer/01_mc_dfi_2p1_layer.md)).
- **`init_sequencer`** (rock child inside `pumice_scheduler_layer`) — runs the
  DDR2 or LPDDR2 JEDEC MR/init sequence.
- **`mode_register`** (rock child inside `pumice_scheduler_layer`) — CL / CWL /
  BL / AL decode differs by memtype.
- **`pumice_training_layer`** — both FUBs gate on `memtype == MEMTYPE_LPDDR2`;
  DDR2 has no ZQ pin and no MRR, so the layer is inert for DDR2 builds.

Both memtypes pass the full simulation suite.

## Clock-Domain Crossings

The datapath clock-domain crossing is exactly one: the CDC inside
`mc_dfi_2p1_layer`, built from asynchronous gaxi FIFOs. One FIFO word is one
DFI cycle, so the command / write-data / read-data datapaths are bubble-free.
Everything up to the CDC is on `aclk`; everything past it is on `dfi_clk`.

The training layer adds one narrow sideband crossing (`sync_pulse` /
`cdc_synchronizer`, not FIFOs): `cal_expect` down to `dfi_clk` to arm the read
aligner's calibration capture, and the captured MRR beat back up to `aclk`.
It carries no datapath traffic — see Chapter 3.9.

## What Changed vs the Earlier Architecture

The controller was rearchitected from an earlier FSM-based, elaboration-time
decomposition into a three-layer, CSR-driven design. Until 2026-10-09 that
design was implemented with pumice-local layers
(`pumice_axi4_layer`, `pumice_scheduler_layer`, `pumice_dfi_layer`) and did
not separate the CAM pool into a distinct storage layer. The 2026-10-09
Phase-2 common-IP campaign extracted the shared memory-controller logic into
`common-ip` (`mc_axi4_layer`, `mc_storage_layer`, `mc_scheduler_layer`,
`mc_training_layer`, and `mc_dfi_2p1_layer`); pumice retained thin rock
wrappers (`pumice_scheduler_layer`, `pumice_training_layer`) for its
generation-specific children. See the family architecture in
[common_has](../../../../../common-ip/docs/common_has/ch02_architecture/01_layer_stack.md).

Notable changes across both transitions:

- **Retired**: `txn_queue`, `bank_machine`, `xbank_timers`, `cmd_encoder`,
  `odt_ctrl`, `scheme selector`, the `*_macro`-as-architecture names,
  `axi_intake`/`axi_frontend`, and the pumice-local layer names
  `pumice_axi4_layer` and `pumice_dfi_layer`.
- **Replaced by / moved to common-ip**: the two CAMs
  (`mc_wr_data_cam` + `mc_rd_cmd_cam`, now in `mc_storage_layer`),
  FSM-free `bank_timer` (stamped by `mc_scheduler_layer`), `global_timers`,
  `dfi_cmd_formatter` (+ `dfi_signal_pack`, now in `mc_dfi_2p1_layer`), and
  the single `ADDR_MAP.bank_lsb` knob.
- **Introduced**: the distinct `mc_storage_layer`, the common single-CDC
  `mc_dfi_2p1_layer`, the common `mc_training_layer` shell, the PeakRDL
  `pumice_csr` block (configuration by name), and the optional
  `pumice_top_geared` host-width wrapper.
