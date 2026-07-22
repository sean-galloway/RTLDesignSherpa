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

# DFI Layer and Host-Width Gearing (`pumice_dfi_layer` + `pumice_top_geared`)

**Module:** `pumice_dfi_layer.sv` (macro) / `pumice_top_geared.sv` (top wrapper)
**Location:** `rtl/macro/` and `rtl/top/`
**Category:** Macro / Top wrapper
**Status:** Implemented (single-CDC DFI datapath; formal-IP host-width gearing wrapper)

> **Replaces the retired `gear_dfi_fub`.** The original chapter described a
> phase-packing FUB (`gear_dfi_fub` / `dfi_signal_pack`) that spread a single MC
> command and burst-of-`N` data beats into per-phase DFI slots. That
> phase-packing role is real but small — it lives inside `dfi_signal_pack` and
> the DFI-layer sub-FUBs. This chapter now covers the two live, distinct concepts
> that carry the word "gearing" in pumice, and it keeps them separate:
>
> 1. **The DFI layer** (`pumice_dfi_layer`) — the single controller/PHY
>    clock-domain crossing plus the DFI-clock command/write/read datapath. This
>    is where the internal `DW`-wide word is split into `DFI_RATE` DRAM beats.
> 2. **Host-width gearing** (`pumice_top_geared`) — an OPTIONAL top wrapper that
>    lets a host SoC use any AXI data width, inserting the repo's formally
>    verified AXI data-width converters between the host and the fixed-width core.
>
> These are orthogonal: (1) is about DRAM-beat phasing on the PHY side; (2) is
> about AXI beat width on the host side.

---

## Concept 1 — The DFI Layer (`pumice_dfi_layer`)

### Purpose

`pumice_dfi_layer` presents the controller-clock command/wrdata/rddata streams on
one side and the DFI 2.1 pin bus on the other. It holds the **single**
controller/PHY clock-domain crossing and the DFI-clock-side datapath. Its
internal datapath unit is the DFI word (`dfi_wrdata` width = all `DFI_RATE`
phases): one FIFO word equals one DFI cycle, which keeps the datapath bubble-free.

Two clock domains:

- **`ctl_clk`** — command from the scheduler, write data from the WR CAM, read
  data to the RD CAM, and the `init_start` / `init_complete` handshake.
- **`dfi_clk`** — the DFI command bus, `dfi_wrdata`/en/mask, `dfi_rddata`/en/
  valid, and `dfi_init_start`/complete.

### Internal structure (verified against the RTL)

`pumice_dfi_layer` instantiates exactly four sub-FUBs:

| Sub-FUB                    | Domain    | Role                                                             |
|----------------------------|-----------|-----------------------------------------------------------------|
| `pumice_dfi_cdc`           | ctl↔dfi   | The **single** clock crossing — async gaxi FIFOs only (cmd, wrdata, rddata, plus init-start/complete bit crossings) |
| `pumice_dfi_cmd_path`      | dfi_clk   | cmd FIFO → DFI command bus + `wr_fire`/`rd_fire` strobes; instantiates `dfi_cmd_formatter` (§2.14) and `dfi_signal_pack` |
| `pumice_dfi_wr_serializer` | dfi_clk   | wrdata FIFO → `dfi_wrdata` at `t_phy_wrlat`                       |
| `pumice_dfi_rd_aligner`    | dfi_clk   | `dfi_rddata` → rddata FIFO at `t_rddata_en`                      |

The CDC (`pumice_dfi_cdc`) is the only place the domains meet; everything
downstream of it runs entirely in `dfi_clk`. The command path emits `wr_fire_o` /
`rd_fire_o` strobes that time the serializer and aligner relative to the issued
command.

### Key parameters

| Parameter          | Default | Effect                                                          |
|--------------------|---------|-----------------------------------------------------------------|
| `NUM_RANKS`        | 1       | CS/rank fan-out                                                 |
| `NUM_BANKS`        | 8       | Bank-field width                                               |
| `ROW_WIDTH`        | 14      | Row / DFI address width                                        |
| `COL_WIDTH`        | 10      | Column width                                                   |
| `DFI_RATE`         | 2       | DRAM beats per DFI word (phase count)                          |
| `DRAM_BEAT_WIDTH`  | 64      | One DRAM beat's data width                                     |
| `BL`               | 8       | DRAM beats per burst; `BL_WORDS = BL / DFI_RATE` DFI words/burst |
| `CMD/WD/RD_FIFO_DEPTH` | 8/16/16 | CDC FIFO depths                                             |
| `N_FLOP_CROSS`     | 2       | Synchronizer flop stages in the async FIFOs                    |

Derived DFI geometry: `DFI_DATA_WIDTH = DRAM_BEAT_WIDTH * DFI_RATE`,
`DFI_STRB_WIDTH = DFI_DATA_WIDTH/8`, `DFI_EN_WIDTH = DFI_VALID_WIDTH = DFI_RATE`.
The FIFO payloads pack the command (`CMD_DW`), `{last,strb,data}` for writes
(`WD_DW`), and `{last,resp,data}` for reads (`RD_DW`).

### DFI-clock runtime knobs

| Signal          | Width | Description                                             |
|-----------------|-------|---------------------------------------------------------|
| `memtype_i`     | enum  | DDR2 / LPDDR2 selector for the command path              |
| `rd_phase_i`    | PHW   | DFI sub-phase carrying the READ command (see §2.14)      |
| `wr_phase_i`    | PHW   | DFI sub-phase carrying the WRITE command                 |
| `t_phy_wrlat_i` | [7:0] | PHY write latency — when the serializer launches wrdata (CSR reset 0; Nexys A7 tuple programs 1) |
| `t_rddata_en_i` | [7:0] | When the aligner strobes `dfi_rddata_en` (valid = en + PHY read_latency); board tuple 6 |

These are the PHY-integration knobs surfaced through the CSR (`DFI_PHASE`,
`DFI_TIMING`); they carry the PHY-specific latencies rather than baking them into
the datapath, which is what let on-board bring-up dial in `t_rddata_en` / phase
placement without an RTL change.

---

## Concept 2 — Host-Width Gearing (`pumice_top_geared`)

### Purpose

The controller core is fixed at its natural width `DW = DRAM_BEAT_WIDTH *
DFI_RATE` (default 128): one AXI beat == one DFI word == `DFI_RATE` DRAM beats,
and one AXI burst (`BL/DFI_RATE` beats) == one DRAM burst (`BL` beats).
`pumice_top_geared` wraps `pumice_top` with a **free** `HOST_AXI_DATA_WIDTH`,
inserting the repo's formally verified data-width converters
(`axi4_dwidth_converter_wr` / `_rd`) between a host-width AXI slave and the
fixed-`DW` core.

This is the family-wide gearing path (DDR2/DDR3/DDR4/LPDDR2), reusing proven +
formal IP rather than re-verifying a bespoke gearbox inside the freshly
stabilized controller datapath.

> **The old coupling is gone.** Do not describe the retired "AXI_DATA_WIDTH ==
> DRAM_BEAT_WIDTH" constraint. Internal geometry is `DW = DRAM_BEAT_WIDTH *
> DFI_RATE`; the DW→phase split happens inside the DFI layer / `dfi_signal_pack`,
> and the host AXI width is decoupled from it by this wrapper.

### GEAR-1 bypass (bit-identical)

When `HOST_AXI_DATA_WIDTH == DW`, a `generate` selects the `g_direct` branch: the
host AXI signals are wired straight through to the core with no converter and no
added latency. Existing `DW`-width builds are therefore bit-identical whether they
instantiate `pumice_top` directly or through `pumice_top_geared`.

### Geared branch

When `HOST_AXI_DATA_WIDTH != DW`, the `g_conv` branch instantiates the two
formal converters:

```systemverilog
axi4_dwidth_converter_wr #(.S_AXI_DATA_WIDTH(HOST_AXI_DATA_WIDTH), .M_AXI_DATA_WIDTH(DW), ...)
axi4_dwidth_converter_rd #(.S_AXI_DATA_WIDTH(HOST_AXI_DATA_WIDTH), .M_AXI_DATA_WIDTH(DW), ...)
```

The host slave ports (`s_axi_*` at `HOST_AXI_DATA_WIDTH`) feed the converters; the
converters' master ports (the internal `c_*` nets at `DW`) feed `pumice_top`. The
CSR cpuif and the DFI pin bus pass straight through the wrapper unmodified.

**Burst geometry.** The core still requires one AXI burst == one DRAM burst at its
`DW` side (`(awlen+1) * DFI_RATE == BL`). The host issues bursts at host width; the
converter translates them to `DW`-width bursts of that geometry. Host burst sizing
is the host's contract (the same spirit as the core's ragged-burst check).
Verified for host widths in {64, 128, 256}. Full scope in
`docs/AXI_DRAM_GEARING_SCOPE.md`.

### Key parameters

| Parameter              | Default | Effect                                                   |
|------------------------|---------|----------------------------------------------------------|
| `HOST_AXI_DATA_WIDTH`  | 128     | Host AXI data width (free); == `DW` triggers the bypass  |
| `DW` (derived)         | `DRAM_BEAT_WIDTH * DFI_RATE` | Fixed core width                          |
| core geometry params   | —       | `AXI_ID_WIDTH`, `AXI_ADDR_WIDTH`, `NUM_RANKS`, `NUM_BANKS`, `ROW_WIDTH`, `COL_WIDTH`, `DFI_RATE`, `DRAM_BEAT_WIDTH`, `BL`, ... mirror `pumice_top` |

---

## Narrow-Device (x16) Support — the Two Width Granularities

A distinction that is separate from both concepts above but which the DFI layer
must respect: the **pumice DRAM beat** (`DRAM_BEAT_WIDTH`, one DFI phase's data)
is not necessarily the **physical DRAM device word** (`DRAM_DEVICE_WIDTH`, the DQ
width — e.g. 16 for an x16 device). When a beat is wider than the device (a
32-bit beat over an x16 device packs `K = DRAM_BEAT_WIDTH / DRAM_DEVICE_WIDTH = 2`
physical DDR words), three parts of the pipeline must reason in **device-word**
units. Getting this wrong is invisible in a DFI-level behavioral sim but corrupts
real silicon — the Nexys A7 x16 bring-up hit all three:

1. **Burst length (beats per command).** A JEDEC BL from MR0 (`bl_o`, BL4/BL8) is
   in physical device beats; the core scales it to pumice-beat units before
   feeding the burst-split and serializer, else an x16 BL4 is over-counted and the
   controller drives/captures an extra DFI cycle.
2. **Column address stride.** DRAM columns are device-word granular, so
   `addr_mapper`'s `BYTE_OFFSET_WIDTH` must be `log2(DRAM_DEVICE_WIDTH/8)`, not
   `log2(DRAM_BEAT_WIDTH/8)`; using the beat width makes a split burst's chunk
   overwrite the previous chunk's tail (a ~50% read scramble on silicon).
3. **Read-data / valid alignment.** A PHY may present read data ahead of, or on a
   different phase than, `rddata_valid`. This is handled at runtime by the
   `t_rddata_en` knob and the `DFI_PHASE` CSR (below) rather than baked-in
   latencies.

Default `DRAM_DEVICE_WIDTH = DRAM_BEAT_WIDTH` (K=1) makes all of the above
bit-identical to the wide-device behavior.

### `DFI_PHASE` CSR (rd_phase / wr_phase)

`dfi_cmd_formatter` places the READ command on `rd_phase` and the WRITE command on
`wr_phase` (defaults 0; all other commands on phase 0), runtime-settable via the
`DFI_PHASE` CSR through `pumice_dfi_layer`'s `rd_phase_i` / `wr_phase_i`. This
matches a PHY that consumes a per-command rdphase/wrphase off the DFI bus. The
LiteDRAM a7ddrphy instead takes the command on phase 0 and applies its rdphase
internally, so on that PHY `rd_phase` stays 0 — the CSR exists for PHYs that do
not.

---

## Interface Summary

### `pumice_dfi_layer` — controller side (`ctl_clk`)

| Signal          | Direction | Description                              |
|-----------------|-----------|------------------------------------------|
| `cmd_valid_i` / `cmd_ready_o` / `cmd_data_i[CMD_DW]` | in/out/in | Command stream from the scheduler |
| `wd_valid_i` / `wd_ready_o` / `wd_data_i[WD_DW]` | in/out/in | Write data from the WR CAM drain ({last,strb,data}) |
| `rd_valid_o` / `rd_ready_i` / `rd_data_o[RD_DW]` | out/in/out | Read data to the RD CAM ({last,resp,data}) |
| `init_start_i` / `init_complete_o` | in/out | Init handshake, controller side |

### `pumice_dfi_layer` — PHY side (`dfi_clk`)

DFI command bus (`dfi_address_o`, `dfi_bank_o`, `dfi_cas_n_o`, `dfi_ras_n_o`,
`dfi_we_n_o`, `dfi_cs_n_o`, `dfi_odt_o`), write data (`dfi_wrdata_o`,
`dfi_wrdata_en_o`, `dfi_wrdata_mask_o`), read data (`dfi_rddata_en_o`,
`dfi_rddata_i`, `dfi_rddata_valid_i`), and the DFI init handshake
(`dfi_init_start_o`, `dfi_init_complete_i`), plus the runtime knobs above.

### `pumice_top_geared`

Host AXI4 slave at `HOST_AXI_DATA_WIDTH`, PeakRDL cpuif passthrough
(`s_cpuif_*`), `init_done_o`, and the DFI 2.1 pin bus straight through. Internally
wires either directly (`g_direct`) or via the two converters (`g_conv`) to
`pumice_top` at `DW`.

---

## Verification Notes (cocotb test plan)

| Scenario                                                                          | What it proves                                  |
|-----------------------------------------------------------------------------------|-------------------------------------------------|
| Command/wrdata/rddata cross the CDC bubble-free at `DFI_RATE = 2`                  | Single-CDC datapath, one FIFO word = one DFI cycle |
| Write burst: `wr_fire` → serializer launches `dfi_wrdata` at `t_phy_wrlat`         | Write-latency alignment                          |
| Read burst: `rd_fire` → aligner strobes `dfi_rddata_en` at `t_rddata_en`           | Read-capture alignment                           |
| `rd_phase = 1`: RD command lands on DFI phase 1                                    | `DFI_PHASE` CSR routing                          |
| x16 device (K=2): BL4 uses one DFI cycle, columns stride by device words           | Two-granularity handling                         |
| `pumice_top_geared` with `HOST_AXI_DATA_WIDTH == DW`: `g_direct` bypass            | GEAR-1 bit-identical to bare `pumice_top`        |
| Host 64 → `DW` 128 via `axi4_dwidth_converter_wr/_rd`: burst geometry preserved    | Geared write/read path                           |
| Host 256 → `DW` 128: read data reassembled correctly at host width                 | Wide-host gearing                                |
| CSR cpuif and DFI pins identical whether geared or direct                          | Passthrough correctness                          |

---

## Open Questions / Future Work

- **Multi-command-per-cycle.** The command path places one issued command per DFI
  word today (multi-phase content passes through, but a single command occupies
  a word). Emitting multiple commands per DFI cycle is a scheduler-side feature;
  the bus widths are already in place.
- **`dfi_dram_clk_disable` / power-down.** `dfi_signal_pack` holds clk-disable at
  0; wiring the power-state machine through the DFI layer is future work.
- **Higher gear ratios.** `DFI_RATE = 4` (and DDR3+ higher ratios) scale the DFI
  geometry linearly; validate the CDC FIFO depths and serializer/aligner timing
  when the family controller targets them.
- **Host width coverage.** Gearing is verified for host ∈ {64, 128, 256}; add 512
  when a host SoC requires it. See `docs/AXI_DRAM_GEARING_SCOPE.md`.
