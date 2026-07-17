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

# STREAM Integration Status

**Date:** 2025-11-26
**Purpose:** Track APB configuration and top-level integration progress

---

## ✅ Completed Tasks

### 1. PeakRDL Register Generation with Passthrough Interface

**Files Generated:**
- `../../regs/generated/rtl/stream_regs.sv` (116KB, passthrough interface)
- `../../regs/generated/rtl/stream_regs_pkg.sv` (18KB)

**Source RDL:**
- `stream_regs.rdl` (stable, no v2 suffix)
- Addrmap name: `stream_regs` (not `stream_regs_v2`)
- Address range: 0x100-0x3FF (configuration registers)

**Generation Command:**
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/dmas/stream/rtl/macro
/mnt/data/github/rtldesignsherpa/venv/bin/peakrdl regblock stream_regs.rdl --cpuif passthrough -o ../../regs/generated/rtl/
```

**Interface Type: Passthrough (matching HPET pattern)**
- Discrete CPU interface signals (`s_cpuif_*`)
- Compatible with `peakrdl_to_cmdrsp` adapter
- Cleaner separation of APB protocol from register logic
- Reference: `projects/components/retro_legacy_blocks/rtl/hpet/hpet_config_regs.sv`

**Cleanup:**
- ✅ Deleted old `stream_regs_v2.sv` and `stream_regs_v2_pkg.sv`
- ✅ Regenerated with passthrough interface (not apb4)
- ✅ Updated `stream_config_block.sv` comment to reference `stream_regs`

---

### 2. CMD/RSP Router Module Created

**File:** `cmdrsp_router.sv`

**Purpose:** Routes CMD/RSP transactions based on address (operates at CMD/RSP protocol level, AFTER apb_slave_cdc):
- **0x000-0x03F** → `apbtodescr` (channel kick-off)
- **0x100-0x3FF** → `peakrdl_to_cmdrsp` (configuration registers)

**Features:**
- CMD/RSP slave input (from `apb_slave_cdc`)
- Two CMD/RSP master outputs (to `apbtodescr` and `peakrdl_to_cmdrsp`)
- Address-based routing with registered selection tracking
- Proper response routing with valid/ready handshaking
- Lints cleanly with Verilator

**Interface:**
```systemverilog
module cmdrsp_router #(
    parameter int ADDR_WIDTH = 12,
    parameter int DATA_WIDTH = 32
) (
    input  logic                    clk,
    input  logic                    rst_n,

    // CMD/RSP Slave (from apb_slave_cdc)
    input  logic                    s_cmd_valid,
    output logic                    s_cmd_ready,
    input  logic                    s_cmd_pwrite,
    input  logic [ADDR_WIDTH-1:0]   s_cmd_paddr,
    input  logic [DATA_WIDTH-1:0]   s_cmd_pwdata,
    output logic                    s_rsp_valid,
    input  logic                    s_rsp_ready,
    output logic [DATA_WIDTH-1:0]   s_rsp_prdata,
    output logic                    s_rsp_pslverr,

    // CMD/RSP Master 0: Descriptor kick-off (0x000-0x03F)
    output logic                    m0_cmd_valid,
    input  logic                    m0_cmd_ready,
    output logic                    m0_cmd_pwrite,
    output logic [ADDR_WIDTH-1:0]   m0_cmd_paddr,
    output logic [DATA_WIDTH-1:0]   m0_cmd_pwdata,
    input  logic                    m0_rsp_valid,
    output logic                    m0_rsp_ready,
    input  logic [DATA_WIDTH-1:0]   m0_rsp_prdata,
    input  logic                    m0_rsp_pslverr,

    // CMD/RSP Master 1: Configuration registers (0x100-0x3FF)
    output logic                    m1_cmd_valid,
    input  logic                    m1_cmd_ready,
    output logic                    m1_cmd_pwrite,
    output logic [ADDR_WIDTH-1:0]   m1_cmd_paddr,
    output logic [DATA_WIDTH-1:0]   m1_cmd_pwdata,
    input  logic                    m1_rsp_valid,
    output logic                    m1_rsp_ready,
    input  logic [DATA_WIDTH-1:0]   m1_rsp_prdata,
    input  logic                    m1_rsp_pslverr
);
```

---

## 🔧 Integration Architecture (Following HPET Pattern)

### Current Block Diagram

```
APB4 Input (external interface)
    ↓
apb_slave_cdc (APB → CMD/RSP, clock domain crossing)
    ↓
CMD/RSP Interface
    ↓
cmdrsp_router (address-based routing at CMD/RSP level)
    ├→ CMD/RSP Master 0 → apbtodescr (0x000-0x03F, channel kick-off)
    │                         ↓
    │                    [Descriptor Engines × 8]
    │
    └→ CMD/RSP Master 1 → peakrdl_to_cmdrsp (0x100-0x3FF, configuration path)
                             ↓
                         passthrough CPU interface (s_cpuif_*)
                             ↓
                         stream_regs (PeakRDL generated)
                             ↓
                         hwif_out (register struct)
                             ↓
                         stream_config_block (extracts & maps hwif to config signals)
                             ↓
                         [Configuration signals to stream_core/stream_core_mon]
```

### Address Map

| Range | Module | Protocol | Purpose |
|-------|--------|----------|---------|
| 0x000-0x03F | `apbtodescr` | CMD/RSP | Channel kick-off (write descriptor address) |
| 0x100-0x3FF | `stream_regs` | APB4 | Configuration registers (PeakRDL-generated) |

---

## 📋 Remaining Integration Tasks

### Task 3: ✅ COMPLETED - cmdrsp_router Created and Integrated into Filelist

**Status:** Completed on 2025-11-27

**What Was Done:**
1. Deleted incorrect `stream_apb_router.sv` (was operating at wrong protocol level)
2. Created `cmdrsp_router.sv` operating at CMD/RSP protocol level (correct!)
3. Updated filelist `stream_top_ch8.f` to reference cmdrsp_router
4. Updated INTEGRATION_STATUS.md to reflect correct architecture
5. Updated PEAKRDL_GENERATION.md with correct flow

**Files Modified:**
- `cmdrsp_router.sv` - ✅ Created (CMD/RSP router)
- `stream_top_ch8.f` - ✅ Updated to use cmdrsp_router
- `INTEGRATION_STATUS.md` - ✅ Updated with correct architecture
- `stream_apb_router.sv` - ✅ Deleted (incorrect design)

**Architecture:**
```
APB4 Input (external)
    ↓
apb_slave_cdc (APB → CMD/RSP, CDC)
    ↓
cmdrsp_router (CMD/RSP address routing)
    ├→ CMD/RSP Master 0 → apbtodescr (0x000-0x03F, channel kick-off)
    └→ CMD/RSP Master 1 → peakrdl_to_cmdrsp (0x100-0x3FF, configuration)
```

**Note:** cmdrsp_router correctly operates at CMD/RSP protocol level after apb_slave_cdc.

---

### Task 4: FUTURE - Update stream_top_ch8.sv with USE_AXI_MONITOR Parameter

**Current State:**
- Two separate files exist:
  - `stream_top_ch8.sv` (uses `stream_core_notie` - monitors disabled)
  - `stream_top_mon_ch8.sv` (uses `stream_core_mon` - monitors enabled)

**Required Changes:**
1. Merge into single `stream_top_ch8.sv` with parameter `USE_AXI_MONITOR`
2. Use generate block to instantiate either `stream_core` or `stream_core_mon`
3. Delete `stream_top_mon_ch8.sv` after merge
4. Update integration to use new `stream_apb_router` module

**Parameter:**
```systemverilog
module stream_top_ch8 #(
    parameter bit USE_AXI_MONITOR = 1'b0,  // 0=stream_core, 1=stream_core_mon
    parameter int NUM_CHANNELS = 8,
    parameter int DATA_WIDTH = 512,
    parameter int ADDR_WIDTH = 64,
    parameter int SRAM_DEPTH = 4096,
    parameter int APB_ADDR_WIDTH = 12,
    parameter int APB_DATA_WIDTH = 32
) (
    // ... ports ...
);

    // Generate block for core selection
    generate
        if (USE_AXI_MONITOR) begin : gen_mon
            stream_core_mon #(...) u_stream_core (
                // ... connections ...
            );
        end else begin : gen_notie
            stream_core #(...) u_stream_core (
                // ... connections ...
            );
        end
    endgenerate

endmodule
```

---

### Task 4: ⏳ PENDING - Integrate cmdrsp_router + peakrdl_to_cmdrsp + stream_regs into stream_top_ch8.sv

**Required Instantiation (Full Configuration Path):**

```systemverilog
// CMD/RSP Router: Routes CMD/RSP from apb_slave_cdc
cmdrsp_router #(
    .ADDR_WIDTH(APB_ADDR_WIDTH),
    .DATA_WIDTH(APB_DATA_WIDTH)
) u_cmdrsp_router (
    .clk         (aclk),
    .rst_n       (aresetn),

    // CMD/RSP slave (from apb_slave_cdc)
    .s_cmd_valid (cdc_cmd_valid),
    .s_cmd_ready (cdc_cmd_ready),
    .s_cmd_pwrite(cdc_cmd_pwrite),
    .s_cmd_paddr (cdc_cmd_paddr),
    .s_cmd_pwdata(cdc_cmd_pwdata),
    .s_rsp_valid (cdc_rsp_valid),
    .s_rsp_ready (cdc_rsp_ready),
    .s_rsp_prdata(cdc_rsp_prdata),
    .s_rsp_pslverr(cdc_rsp_pslverr),

    // CMD/RSP master 0: apbtodescr (0x000-0x03F)
    .m0_cmd_valid (apbtodescr_cmd_valid),
    .m0_cmd_ready (apbtodescr_cmd_ready),
    .m0_cmd_pwrite(apbtodescr_cmd_pwrite),
    .m0_cmd_paddr (apbtodescr_cmd_paddr),
    .m0_cmd_pwdata(apbtodescr_cmd_pwdata),
    .m0_rsp_valid (apbtodescr_rsp_valid),
    .m0_rsp_ready (apbtodescr_rsp_ready),
    .m0_rsp_prdata(apbtodescr_rsp_prdata),
    .m0_rsp_pslverr(apbtodescr_rsp_pslverr),

    // CMD/RSP master 1: peakrdl_to_cmdrsp (0x100-0x3FF)
    .m1_cmd_valid (peakrdl_cmd_valid),
    .m1_cmd_ready (peakrdl_cmd_ready),
    .m1_cmd_pwrite(peakrdl_cmd_pwrite),
    .m1_cmd_paddr (peakrdl_cmd_paddr),
    .m1_cmd_pwdata(peakrdl_cmd_pwdata),
    .m1_rsp_valid (peakrdl_rsp_valid),
    .m1_rsp_ready (peakrdl_rsp_ready),
    .m1_rsp_prdata(peakrdl_rsp_prdata),
    .m1_rsp_pslverr(peakrdl_rsp_pslverr)
);

// CMD/RSP to passthrough adapter
peakrdl_to_cmdrsp #(
    .ADDR_WIDTH(APB_ADDR_WIDTH),
    .DATA_WIDTH(APB_DATA_WIDTH)
) u_peakrdl_adapter (
    .aclk       (aclk),
    .aresetn    (aresetn),
    // CMD/RSP input (from cmdrsp_router m1)
    .cmd_valid  (peakrdl_cmd_valid),
    .cmd_ready  (peakrdl_cmd_ready),
    .cmd_pwrite (peakrdl_cmd_pwrite),
    .cmd_paddr  (peakrdl_cmd_paddr),
    .cmd_pwdata (peakrdl_cmd_pwdata),
    .rsp_valid  (peakrdl_rsp_valid),
    .rsp_ready  (peakrdl_rsp_ready),
    .rsp_prdata (peakrdl_rsp_prdata),
    .rsp_pslverr(peakrdl_rsp_pslverr),
    // Passthrough interface (to stream_regs)
    .regblk_req        (regblk_req),
    .regblk_req_is_wr  (regblk_req_is_wr),
    .regblk_addr       (regblk_addr),
    .regblk_wr_data    (regblk_wr_data),
    .regblk_wr_biten   (regblk_wr_biten),
    .regblk_req_stall_wr(regblk_req_stall_wr),
    .regblk_req_stall_rd(regblk_req_stall_rd),
    .regblk_rd_ack     (regblk_rd_ack),
    .regblk_rd_err     (regblk_rd_err),
    .regblk_rd_data    (regblk_rd_data),
    .regblk_wr_ack     (regblk_wr_ack),
    .regblk_wr_err     (regblk_wr_err)
);

// PeakRDL register block
stream_regs u_stream_regs (
    .clk    (aclk),
    .rst    (~aresetn),  // Active-high reset
    // Passthrough CPU interface
    .s_cpuif_req        (regblk_req),
    .s_cpuif_req_is_wr  (regblk_req_is_wr),
    .s_cpuif_addr       (regblk_addr[9:0]),
    .s_cpuif_wr_data    (regblk_wr_data),
    .s_cpuif_wr_biten   (regblk_wr_biten),
    .s_cpuif_req_stall_wr(regblk_req_stall_wr),
    .s_cpuif_req_stall_rd(regblk_req_stall_rd),
    .s_cpuif_rd_ack     (regblk_rd_ack),
    .s_cpuif_rd_err     (regblk_rd_err),
    .s_cpuif_rd_data    (regblk_rd_data),
    .s_cpuif_wr_ack     (regblk_wr_ack),
    .s_cpuif_wr_err     (regblk_wr_err),
    // Hardware interface
    .hwif_in            (hwif_in),
    .hwif_out           (hwif_out)
);
```

---

### Task 5: Update stream_config_block Instantiation

**Current:** Uses PeakRDL `hwif_out` struct
**Required:** Connect to regenerated `stream_regs_pkg` (not `stream_regs_v2_pkg`)

**Note:** `stream_config_block.sv` already uses correct signal names. Only the package reference in comments was updated.

---

### Task 6: Optional - Add apb_slave_cdc for Clock Domain Crossing

**If APB and AXI clocks are different:**

```systemverilog
apb_slave_cdc #(
    .ADDR_WIDTH(APB_ADDR_WIDTH),
    .DATA_WIDTH(APB_DATA_WIDTH)
) u_apb_cdc (
    // APB clock domain (input)
    .pclk       (pclk),
    .presetn    (presetn),
    .s_apb_*    (s_apb_*),  // From top-level ports

    // AXI clock domain (output)
    .aclk       (aclk),
    .aresetn    (aresetn),
    .m_apb_*    (cdc_apb_*)  // To stream_apb_router
);
```

**If clocks are the same:** Direct connection from top ports to `stream_apb_router`

---

## 📊 Module Status Summary

| Module | Status | Location | Notes |
|--------|--------|----------|-------|
| `stream_regs.sv` | ✅ Generated | `../../regs/generated/rtl/` | PeakRDL (passthrough interface) |
| `stream_regs_pkg.sv` | ✅ Generated | `../../regs/generated/rtl/` | Register types & hwif structs |
| `peakrdl_to_cmdrsp.sv` | ✅ Exists | `../../../converters/rtl/` | CMD/RSP → passthrough adapter |
| `cmdrsp_router.sv` | ✅ Created | `./` | CMD/RSP address router |
| `stream_config_block.sv` | ⏳ Update Needed | `./` | Extract hwif → config signals |
| `apbtodescr.sv` | ✅ Exists | `../fub/` | Channel kick-off |
| `apb_slave_cdc.sv` | ✅ Exists | `../../../converters/rtl/` | APB → CMD/RSP, CDC |
| `stream_top_ch8.sv` | ⏳ Update Needed | `./` | Add full config path integration |
| `stream_top_ch8.f` | ✅ Updated | `filelists/top/` | Includes cmdrsp_router + regs_pkg |
| `stream_top_mon_ch8.sv` | ⏳ Future | `./` | Merge with USE_AXI_MONITOR param |

**Architecture Decision:** Using passthrough interface (matching HPET pattern) for compatibility with `peakrdl_to_cmdrsp` adapter.

---

## 🎯 Next Steps (Priority Order)

1. **High Priority:** Merge `stream_top_ch8.sv` and `stream_top_mon_ch8.sv`
   - Add `USE_AXI_MONITOR` parameter
   - Use generate block for core selection
   - Delete `stream_top_mon_ch8.sv` after verification

2. **High Priority:** Integrate `stream_apb_router` into `stream_top_ch8.sv`
   - Replace existing address decode logic
   - Connect to `apbtodescr` and `stream_regs`

3. **Medium Priority:** Verify integration compiles
   - Lint with Verilator
   - Check all signal widths match
   - Ensure no dangling signals

4. **Low Priority:** Update tests to use new naming
   - Update any test references to `stream_regs_v2` → `stream_regs`
   - Verify parameter sweep still works with `USE_AXI_MONITOR`

5. **Optional:** Add `apb_slave_cdc` if needed
   - Only if APB and AXI clocks are different
   - Otherwise, direct connection is fine

---

## 🔍 Verification Checklist

- [x] PeakRDL files generated without v2 suffix
- [x] stream_regs generated with passthrough interface (matching HPET)
- [x] cmdrsp_router created (correct CMD/RSP protocol level)
- [x] stream_apb_router deleted (incorrect APB protocol level)
- [x] stream_config_block references updated
- [x] cmdrsp_router added to stream_top_ch8.f filelist
- [x] stream_top_ch8.f filelist updated
- [x] INTEGRATION_STATUS.md updated with correct architecture
- [x] PEAKRDL_GENERATION.md updated with passthrough pattern
- [ ] stream_config_block updated to extract hwif_out
- [ ] cmdrsp_router + peakrdl_to_cmdrsp + stream_regs integrated into stream_top_ch8.sv
- [ ] Compilation verification (run test to verify integration)
- [ ] stream_top_ch8 merged with USE_AXI_MONITOR parameter (future)
- [ ] Tests updated for new naming (if needed)
- [ ] Full validation with APB configuration

---

## 📁 File Locations

```
projects/components/dmas/stream/
├── rtl/
│   ├── macro/
│   │   └── stream_regs.rdl                    # Source RDL
│   ├── fub/
│   │   └── apbtodescr.sv                      # Channel kick-off
│   └── top/
│       ├── cmdrsp_router.sv                   # ✅ NEW: CMD/RSP router
│       ├── stream_config_block.sv             # ⏳ To be updated
│       ├── stream_top_ch8.sv                  # ⏳ To be updated
│       └── stream_top_mon_ch8.sv              # ⏳ Future: merge
│
└── regs/
    └── generated/
        └── rtl/
            ├── stream_regs.sv                 # ✅ Generated
            └── stream_regs_pkg.sv             # ✅ Generated
```

---

**Version:** 1.0
**Last Updated:** 2025-11-26
**Author:** Integration session tracking
