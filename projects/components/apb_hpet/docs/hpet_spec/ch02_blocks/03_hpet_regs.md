### HPET Registers - PeakRDL Generated Register File

#### Overview

The `hpet_regs` module is auto-generated from the SystemRDL specification (`rtl/peakrdl/hpet_regs.rdl`) using the PeakRDL toolchain. It implements the complete HPET register file with proper field access semantics (RO, RW, W1C), hardware interface integration, and CPU interface protocol handling.

**Single Source of Truth:** All register definitions, addresses, field widths, and access properties are specified in the SystemRDL file. The generated RTL is deterministic and regeneratable.

**Generation Command:**
```bash
cd projects/components/apb_hpet/rtl/peakrdl
peakrdl regblock hpet_regs.rdl --cpuif passthrough -o ../
```

**Generated Files:**
- `hpet_regs.sv` - Register implementation
- `hpet_regs_pkg.sv` - Package with structs and parameters

#### Module Interface

##### Parameters

No user-configurable parameters. All configuration is baked into the generated code from SystemRDL.

**Compile-Time Constants (from SystemRDL):**
```systemverilog
localparam VENDOR_ID = 1;         // From RDL: vendor_id field default
localparam REVISION_ID = 1;       // From RDL: revision_id field default
localparam NUM_TIMERS = 8;        // From RDL: TIMER[0:7] array size
```

**Note:** These values are fixed at generation time. To change them, modify `hpet_regs.rdl` and regenerate.

##### Clock and Reset

| Signal Name | Type | Width | Direction | Description |
|-------------|------|-------|-----------|-------------|
| **clk** | wire | 1 | Input | Register clock (pclk or hpet_clk based on CDC_ENABLE) |
| **rst** | wire | 1 | Input | **Active-high** reset (PeakRDL convention) |

**⚠️ Important:** PeakRDL uses active-high reset. The wrapper (`hpet_config_regs.sv`) inverts `rst_n` before connecting.

##### CPU Interface (Passthrough Protocol)

| Signal Name | Type | Width | Direction | Description |
|-------------|------|-------|-----------|-------------|
| **s_cpuif_req** | wire | 1 | Input | CPU request valid |
| **s_cpuif_req_is_wr** | wire | 1 | Input | Request is write (1) or read (0) |
| **s_cpuif_addr** | wire | 9 | Input | Address (byte-aligned, bits [8:0]) |
| **s_cpuif_wr_data** | wire | 32 | Input | Write data |
| **s_cpuif_wr_biten** | wire | 32 | Input | Write byte enable (bit-level) |
| **s_cpuif_req_stall_wr** | wire | 1 | Output | Stall write request (always 0 for HPET) |
| **s_cpuif_req_stall_rd** | wire | 1 | Output | Stall read request (always 0 for HPET) |
| **s_cpuif_rd_ack** | wire | 1 | Output | Read acknowledgment |
| **s_cpuif_rd_err** | wire | 1 | Output | Read error (decoding error) |
| **s_cpuif_rd_data** | wire | 32 | Output | Read data |
| **s_cpuif_wr_ack** | wire | 1 | Output | Write acknowledgment |
| **s_cpuif_wr_err** | wire | 1 | Output | Write error (always 0 for HPET) |

**Protocol Characteristics:**
- **Latency:** 1 cycle for both reads and writes
- **Stalls:** Never stall (HPET registers have single-cycle access)
- **Errors:** Read error on unmapped address, writes always succeed

##### Hardware Interface (Structs)

```systemverilog
input  hpet_regs_pkg::hpet_regs__in_t  hwif_in;   // From hardware to registers
output hpet_regs_pkg::hpet_regs__out_t hwif_out;  // From registers to hardware
```

**Structure Definitions (in hpet_regs_pkg.sv):**

The package defines comprehensive structs for all registers and fields. Key excerpts:

```systemverilog
package hpet_regs_pkg;

    // Hardware input struct (hardware -> registers)
    typedef struct packed {
        struct packed {
            logic [4:0] next;  // num_tim_cap field value
        } num_tim_cap;
    } HPET_ID__in_t;

    typedef struct packed {
        logic [7:0] next;   // Next value for status bits
        logic hwset;        // Hardware set pulse
    } timer_int_status__in_t;

    typedef struct packed {
        logic [31:0] next;  // Next counter value
    } counter_lo__in_t;

    // ... additional field structs ...

    // Complete input struct
    typedef struct packed {
        HPET_ID__in_t HPET_ID;
        timer_int_status__in_t HPET_STATUS.timer_int_status;
        counter_lo__in_t HPET_COUNTER_LO.counter_lo;
        counter_hi__in_t HPET_COUNTER_HI.counter_hi;
        // ... additional register fields ...
    } hpet_regs__in_t;

    // Hardware output struct (registers -> hardware)
    typedef struct packed {
        struct packed {
            logic value;     // Current field value
        } hpet_enable;
        struct packed {
            logic value;
        } legacy_replacement;
    } HPET_CONFIG__out_t;

    typedef struct packed {
        logic swmod;         // Software modified (write detected)
    } timer_int_status__out_t;

    typedef struct packed {
        logic [31:0] value;  // Current register value
        logic swmod;         // Software modified
    } counter_lo__out_t;

    // ... additional field structs ...

    // Complete output struct
    typedef struct packed {
        HPET_CONFIG__out_t HPET_CONFIG;
        timer_int_status__out_t HPET_STATUS.timer_int_status;
        counter_lo__out_t HPET_COUNTER_LO.counter_lo;
        counter_hi__out_t HPET_COUNTER_HI.counter_hi;
        TIMER__out_t TIMER[7:0];  // Timer array
        // ... additional registers ...
    } hpet_regs__out_t;

endpackage
```

#### Register Implementation

##### Address Decoding

PeakRDL generates a decoded register strobe struct:

```systemverilog
typedef struct {
    logic HPET_ID;
    logic HPET_CONFIG;
    logic HPET_STATUS;
    logic RESERVED_0C;
    logic HPET_COUNTER_LO;
    logic HPET_COUNTER_HI;
    struct {
        logic TIMER_CONFIG;
        logic TIMER_COMPARATOR_LO;
        logic TIMER_COMPARATOR_HI;
        logic RESERVED;
    } TIMER[8];
} decoded_reg_strb_t;

decoded_reg_strb_t decoded_reg_strb;
```

**Decoding Logic:**
```systemverilog
always_comb begin
    decoded_reg_strb.HPET_ID = cpuif_req_masked & (cpuif_addr == 9'h0);
    decoded_reg_strb.HPET_CONFIG = cpuif_req_masked & (cpuif_addr == 9'h4);
    decoded_reg_strb.HPET_STATUS = cpuif_req_masked & (cpuif_addr == 9'h8);
    decoded_reg_strb.RESERVED_0C = cpuif_req_masked & (cpuif_addr == 9'hc);
    decoded_reg_strb.HPET_COUNTER_LO = cpuif_req_masked & (cpuif_addr == 9'h10);
    decoded_reg_strb.HPET_COUNTER_HI = cpuif_req_masked & (cpuif_addr == 9'h14);

    for(int i0=0; i0<8; i0++) begin
        decoded_reg_strb.TIMER[i0].TIMER_CONFIG =
            cpuif_req_masked & (cpuif_addr == 9'h100 + (9)'(i0) * 9'h20);
        decoded_reg_strb.TIMER[i0].TIMER_COMPARATOR_LO =
            cpuif_req_masked & (cpuif_addr == 9'h104 + (9)'(i0) * 9'h20);
        decoded_reg_strb.TIMER[i0].TIMER_COMPARATOR_HI =
            cpuif_req_masked & (cpuif_addr == 9'h108 + (9)'(i0) * 9'h20);
        decoded_reg_strb.TIMER[i0].RESERVED =
            cpuif_req_masked & (cpuif_addr == 9'h10c + (9)'(i0) * 9'h20);
    end
end
```

##### Field Logic

Each field is implemented with:
- **Combo Logic:** Determines next value based on SW write, HW input, or current value
- **Sequential Logic:** Stores field value in flip-flops
- **Output Assignment:** Drives `hwif_out` struct

**Example - HPET_CONFIG.hpet_enable Field:**

```systemverilog
// Field: hpet_regs.HPET_CONFIG.hpet_enable
always_comb begin
    automatic logic [0:0] next_c;
    automatic logic load_next_c;

    next_c = field_storage.HPET_CONFIG.hpet_enable.value;  // Default: hold
    load_next_c = '0;

    if(decoded_reg_strb.HPET_CONFIG && decoded_req_is_wr) begin  // SW write
        next_c = (field_storage.HPET_CONFIG.hpet_enable.value & ~decoded_wr_biten[0:0]) |
                (decoded_wr_data[0:0] & decoded_wr_biten[0:0]);
        load_next_c = '1;
    end

    field_combo.HPET_CONFIG.hpet_enable.next = next_c;
    field_combo.HPET_CONFIG.hpet_enable.load_next = load_next_c;
end

always_ff @(posedge clk) begin
    if(rst) begin
        field_storage.HPET_CONFIG.hpet_enable.value <= 1'h0;  // Reset value
    end else begin
        if(field_combo.HPET_CONFIG.hpet_enable.load_next) begin
            field_storage.HPET_CONFIG.hpet_enable.value <= field_combo.HPET_CONFIG.hpet_enable.next;
        end
    end
end

assign hwif_out.HPET_CONFIG.hpet_enable.value = field_storage.HPET_CONFIG.hpet_enable.value;
```

**Example - HPET_STATUS.timer_int_status Field (W1C with HW set):**

```systemverilog
// Field: hpet_regs.HPET_STATUS.timer_int_status
always_comb begin
    automatic logic [7:0] next_c;
    automatic logic load_next_c;

    next_c = field_storage.HPET_STATUS.timer_int_status.value;
    load_next_c = '0;

    if(decoded_reg_strb.HPET_STATUS && decoded_req_is_wr) begin  // SW write 1 to clear
        next_c = field_storage.HPET_STATUS.timer_int_status.value &
                ~(decoded_wr_data[7:0] & decoded_wr_biten[7:0]);
        load_next_c = '1;

    end else if((field_storage.HPET_STATUS.timer_int_status.value == '0) &&
                (hwif_in.HPET_STATUS.timer_int_status.next != '0)) begin  // Multi-bit sticky
        next_c = hwif_in.HPET_STATUS.timer_int_status.next;
        load_next_c = '1;

    end else if(hwif_in.HPET_STATUS.timer_int_status.hwset) begin  // HW set
        next_c = '1;
        load_next_c = '1;
    end

    field_combo.HPET_STATUS.timer_int_status.next = next_c;
    field_combo.HPET_STATUS.timer_int_status.load_next = load_next_c;
end

always_ff @(posedge clk) begin
    if(field_combo.HPET_STATUS.timer_int_status.load_next) begin
        field_storage.HPET_STATUS.timer_int_status.value <= field_combo.HPET_STATUS.timer_int_status.next;
    end
end

// swmod signal: pulsed when software modifies field
assign hwif_out.HPET_STATUS.timer_int_status.swmod =
    decoded_reg_strb.HPET_STATUS && decoded_req_is_wr && |(decoded_wr_biten[7:0]);
```

**Example - HPET_COUNTER_LO Field (HW write with SW precedence):**

```systemverilog
// Field: hpet_regs.HPET_COUNTER_LO.counter_lo
always_comb begin
    automatic logic [31:0] next_c;
    automatic logic load_next_c;

    next_c = field_storage.HPET_COUNTER_LO.counter_lo.value;
    load_next_c = '0;

    if(decoded_reg_strb.HPET_COUNTER_LO && decoded_req_is_wr) begin  // SW write
        next_c = (field_storage.HPET_COUNTER_LO.counter_lo.value & ~decoded_wr_biten[31:0]) |
                (decoded_wr_data[31:0] & decoded_wr_biten[31:0]);
        load_next_c = '1;
    end else begin  // HW write (precedence=sw means HW writes unless SW writes)
        next_c = hwif_in.HPET_COUNTER_LO.counter_lo.next;
        load_next_c = '1;
    end

    field_combo.HPET_COUNTER_LO.counter_lo.next = next_c;
    field_combo.HPET_COUNTER_LO.counter_lo.load_next = load_next_c;
end

always_ff @(posedge clk) begin
    if(rst) begin
        field_storage.HPET_COUNTER_LO.counter_lo.value <= 32'h0;
    end else begin
        if(field_combo.HPET_COUNTER_LO.counter_lo.load_next) begin
            field_storage.HPET_COUNTER_LO.counter_lo.value <= field_combo.HPET_COUNTER_LO.counter_lo.next;
        end
    end
end

assign hwif_out.HPET_COUNTER_LO.counter_lo.value = field_storage.HPET_COUNTER_LO.counter_lo.value;
assign hwif_out.HPET_COUNTER_LO.counter_lo.swmod =
    decoded_reg_strb.HPET_COUNTER_LO && decoded_req_is_wr && |(decoded_wr_biten[31:0]);
```

##### Read Response Logic

PeakRDL generates readback arrays for all registers:

```systemverilog
// Assign readback values to a flattened array
logic [31:0] readback_array[38];

// Global registers
assign readback_array[0][4:0]   = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 5'h0 : '0;
assign readback_array[0][5:5]   = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 1'h1 : '0;
assign readback_array[0][12:8]  = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ?
                                  hwif_in.HPET_ID.num_tim_cap.next : '0;
assign readback_array[0][23:16] = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 8'h1 : '0;
assign readback_array[0][31:24] = (decoded_reg_strb.HPET_ID && !decoded_req_is_wr) ? 8'h1 : '0;

// Config/status registers
assign readback_array[1][0:0] = (decoded_reg_strb.HPET_CONFIG && !decoded_req_is_wr) ?
                                field_storage.HPET_CONFIG.hpet_enable.value : '0;
assign readback_array[2][7:0] = (decoded_reg_strb.HPET_STATUS && !decoded_req_is_wr) ?
                                field_storage.HPET_STATUS.timer_int_status.value : '0;

// Counter registers
assign readback_array[4][31:0] = (decoded_reg_strb.HPET_COUNTER_LO && !decoded_req_is_wr) ?
                                 field_storage.HPET_COUNTER_LO.counter_lo.value : '0;
assign readback_array[5][31:0] = (decoded_reg_strb.HPET_COUNTER_HI && !decoded_req_is_wr) ?
                                 field_storage.HPET_COUNTER_HI.counter_hi.value : '0;

// Per-timer registers
for(genvar i0=0; i0<8; i0++) begin
    assign readback_array[i0 * 4 + 6][2:2] = (decoded_reg_strb.TIMER[i0].TIMER_CONFIG && !decoded_req_is_wr) ?
                                             field_storage.TIMER[i0].TIMER_CONFIG.timer_enable.value : '0;
    // ... additional timer fields ...
end

// Reduce array via OR (only one element active at a time)
always_comb begin
    automatic logic [31:0] readback_data_var;
    readback_done = decoded_req & ~decoded_req_is_wr;
    readback_err = '0;
    readback_data_var = '0;
    for(int i=0; i<38; i++) readback_data_var |= readback_array[i];
    readback_data = readback_data_var;
end

assign cpuif_rd_ack = readback_done;
assign cpuif_rd_data = readback_data;
assign cpuif_rd_err = readback_err;
```

#### Field Access Semantics

##### Read-Only (RO)

**Characteristics:**
- Software reads return hardware-driven value
- Software writes are ignored (no effect)
- Hardware controls value via `hwif_in`

**Example: HPET_ID register**
```systemverilog
// RO fields: vendor_id, revision_id, num_tim_cap
// Software can read, but writes have no effect
```

##### Read-Write (RW)

**Characteristics:**
- Software can read and write
- Default next value is current value
- Software write updates value
- Reset value specified in RDL

**Example: HPET_CONFIG.hpet_enable**
```systemverilog
// RW field: Software can enable/disable HPET
// Reset value: 0 (disabled)
```

##### Write-1-to-Clear (W1C)

**Characteristics:**
- Software writes 1 to clear bit
- Software writes 0 have no effect
- Hardware can set bit via `hwif_in.hwset`
- Used for sticky interrupt flags

**Example: HPET_STATUS.timer_int_status**
```systemverilog
// W1C field: Software writes 1 to clear interrupt
// Hardware sets via hwif_in.HPET_STATUS.timer_int_status.hwset
```

##### Hardware Write with Software Precedence

**Characteristics:**
- Hardware continuously writes value via `hwif_in.next`
- Software write takes precedence
- Used for live counter readback

**Example: HPET_COUNTER_LO/HI**
```systemverilog
// hw=w, precedence=sw
// Hardware writes counter value every cycle
// Software write overrides hardware write
```

#### SystemRDL Specification

**Source File:** `rtl/peakrdl/hpet_regs.rdl`

**Key RDL Properties Used:**

```systemrdl
addrmap hpet_regs {
    name = "HPET Register Block";
    desc = "High Precision Event Timer registers";

    default regwidth = 32;       // All registers 32-bit
    default accesswidth = 32;    // Single-beat access

    // Read-only identification
    reg {
        field {
            hw = r;              // Hardware read-only
            sw = r;              // Software read-only
        } vendor_id[31:24] = 8'h01;

        field {
            hw = r; sw = r;
        } revision_id[23:16] = 8'h01;

        field {
            hw = w;              // Hardware controls value
            sw = r;              // Software can only read
        } num_tim_cap[12:8];

    } HPET_ID @ 0x000;

    // Read-write configuration
    reg {
        field {
            sw = rw;             // Software read-write
            hw = r;              // Hardware reads value
        } hpet_enable[0:0] = 1'b0;

        field {
            sw = rw; hw = r;
        } legacy_replacement[1:1] = 1'b0;

    } HPET_CONFIG @ 0x004;

    // Write-1-to-clear status
    reg {
        field {
            sw = w1c;            // Write 1 to clear
            hw = w;              // Hardware can set
            hwset;               // Hardware set signal available
        } timer_int_status[NUM_TIMERS-1:0];

    } HPET_STATUS @ 0x008;

    // Hardware-written counter with software override
    reg {
        field {
            sw = rw;             // Software can write
            hw = w;              // Hardware writes every cycle
            precedence = sw;     // Software write takes priority
        } counter_lo[31:0] = 32'h0;

    } HPET_COUNTER_LO @ 0x010;

    // Per-timer array
    regfile {
        reg {
            field { sw = rw; hw = r; } timer_enable[2:2] = 1'b0;
            field { sw = rw; hw = r; } timer_int_enable[3:3] = 1'b0;
            field { sw = rw; hw = r; } timer_type[4:4] = 1'b0;
            field { sw = rw; hw = r; } timer_size[5:5] = 1'b0;
            field { sw = rw; hw = r; } timer_value_set[6:6] = 1'b0;
        } TIMER_CONFIG @ 0x00;

        reg {
            field { sw = rw; hw = r; } timer_comp_lo[31:0] = 32'h0;
        } TIMER_COMPARATOR_LO @ 0x04;

        reg {
            field { sw = rw; hw = r; } timer_comp_hi[31:0] = 32'h0;
        } TIMER_COMPARATOR_HI @ 0x08;

    } TIMER[NUM_TIMERS] @ 0x100 += 0x20;  // 32-byte spacing
};
```

#### Regeneration Procedure

**When to Regenerate:**
1. Changing register addresses
2. Adding/removing fields
3. Modifying field access properties
4. Updating VENDOR_ID, REVISION_ID, or NUM_TIMERS

**Steps:**
```bash
cd projects/components/apb_hpet/rtl/peakrdl

# 1. Edit SystemRDL specification
vim hpet_regs.rdl

# 2. Generate RTL
peakrdl regblock hpet_regs.rdl --cpuif passthrough -o ../

# 3. Verify generated files
ls -l ../hpet_regs.sv ../hpet_regs_pkg.sv

# 4. Review changes (if in version control)
git diff ../hpet_regs.sv ../hpet_regs_pkg.sv

# 5. Run tests to verify
pytest projects/components/apb_hpet/dv/tests/ -v
```

**⚠️ Important:** Do not manually edit generated files! All changes must be made in `hpet_regs.rdl` and regenerated.

---

**Next:** [Chapter 2.4 - apb_hpet (Top Level)](04_apb_hpet_top.md)
