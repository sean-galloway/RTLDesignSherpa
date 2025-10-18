# GAXI Field Configuration Guide

**Last Updated:** 2025-10-11
**Difficulty:** Advanced
**Prerequisites:** [GAXI Multi-Field Integration Tutorial](gaxi_multi_field_integration.md)

---

## Overview

This guide covers advanced patterns for configuring and using multi-field GAXI buffers and FIFOs. Learn how to create domain-specific wrappers, handle variable field counts, implement field masking, and optimize for your specific use case.

---

## Table of Contents

1. [Field Configuration Patterns](#field-configuration-patterns)
2. [Variable Field Count Wrappers](#variable-field-count-wrappers)
3. [Field Masking and Enables](#field-masking-and-enables)
4. [Protocol-Specific Wrappers](#protocol-specific-wrappers)
5. [Advanced Packing Strategies](#advanced-packing-strategies)
6. [Performance Optimization](#performance-optimization)
7. [Debugging and Verification](#debugging-and-verification)

---

## Field Configuration Patterns

### Pattern 1: Fixed Field Count (2 Fields)

**Standard pattern used in testcode modules:**

```systemverilog
module gaxi_buffer_2field #(
    parameter int FIELD0_WIDTH = 32,
    parameter int FIELD1_WIDTH = 32
) (
    input  logic [FIELD0_WIDTH-1:0] wr_field0,
    input  logic [FIELD1_WIDTH-1:0] wr_field1,
    output logic [FIELD0_WIDTH-1:0] rd_field0,
    output logic [FIELD1_WIDTH-1:0] rd_field1
);
    localparam int TOTAL_WIDTH = FIELD0_WIDTH + FIELD1_WIDTH;

    gaxi_skid_buffer #(.DATA_WIDTH(TOTAL_WIDTH)) u_buf (
        .wr_data({wr_field1, wr_field0}),
        .rd_data({rd_field1, rd_field0})
    );
endmodule
```

### Pattern 2: Fixed Field Count (4 Fields)

**Example from testcode: addr + ctrl + data0 + data1**

```systemverilog
module gaxi_buffer_4field #(
    parameter int ADDR_WIDTH = 16,
    parameter int CTRL_WIDTH = 8,
    parameter int DATA_WIDTH = 32  // Used for data0 and data1
) (
    // Write interface
    input  logic [ADDR_WIDTH-1:0] wr_addr,
    input  logic [CTRL_WIDTH-1:0] wr_ctrl,
    input  logic [DATA_WIDTH-1:0] wr_data0,
    input  logic [DATA_WIDTH-1:0] wr_data1,
    // Read interface
    output logic [ADDR_WIDTH-1:0] rd_addr,
    output logic [CTRL_WIDTH-1:0] rd_ctrl,
    output logic [DATA_WIDTH-1:0] rd_data0,
    output logic [DATA_WIDTH-1:0] rd_data1
);
    localparam int TOTAL_WIDTH = ADDR_WIDTH + CTRL_WIDTH + DATA_WIDTH + DATA_WIDTH;

    gaxi_fifo_sync #(.DATA_WIDTH(TOTAL_WIDTH), .DEPTH(16)) u_fifo (
        .wr_data({wr_addr, wr_ctrl, wr_data1, wr_data0}),
        .rd_data({rd_addr, rd_ctrl, rd_data1, rd_data0})
    );
endmodule
```

### Pattern 3: Named Field Parameters

**More descriptive than generic widths:**

```systemverilog
module axi_descriptor_buffer #(
    parameter int ADDR_BITS   = 32,
    parameter int LENGTH_BITS = 16,
    parameter int FLAGS_BITS  = 8,
    parameter int TAG_BITS    = 16
) (
    input  logic [ADDR_BITS-1:0]   wr_mem_addr,
    input  logic [LENGTH_BITS-1:0] wr_xfer_length,
    input  logic [FLAGS_BITS-1:0]  wr_flags,
    input  logic [TAG_BITS-1:0]    wr_tag,

    output logic [ADDR_BITS-1:0]   rd_mem_addr,
    output logic [LENGTH_BITS-1:0] rd_xfer_length,
    output logic [FLAGS_BITS-1:0]  rd_flags,
    output logic [TAG_BITS-1:0]    rd_tag
);
    localparam int DESCRIPTOR_WIDTH = ADDR_BITS + LENGTH_BITS + FLAGS_BITS + TAG_BITS;

    gaxi_skid_buffer #(.DATA_WIDTH(DESCRIPTOR_WIDTH)) u_desc_buf (
        .wr_data({wr_mem_addr, wr_xfer_length, wr_flags, wr_tag}),
        .rd_data({rd_mem_addr, rd_xfer_length, rd_flags, rd_tag})
    );
endmodule
```

---

## Variable Field Count Wrappers

### Pattern 4: Parameterized Field Count

**Use SystemVerilog arrays for variable field counts:**

```systemverilog
module gaxi_buffer_n field #(
    parameter int NUM_FIELDS  = 4,
    parameter int FIELD_WIDTH = 32
) (
    input  logic                            axi_aclk,
    input  logic                            axi_aresetn,
    input  logic                            wr_valid,
    output logic                            wr_ready,
    input  logic [NUM_FIELDS-1:0][FIELD_WIDTH-1:0] wr_fields,

    output logic                            rd_valid,
    input  logic                            rd_ready,
    output logic [NUM_FIELDS-1:0][FIELD_WIDTH-1:0] rd_fields
);
    localparam int TOTAL_WIDTH = NUM_FIELDS * FIELD_WIDTH;

    logic [TOTAL_WIDTH-1:0] wr_data_packed, rd_data_packed;

    // Pack array into flat vector
    always_comb begin
        for (int i = 0; i < NUM_FIELDS; i++) begin
            wr_data_packed[i*FIELD_WIDTH +: FIELD_WIDTH] = wr_fields[i];
        end
    end

    // Unpack flat vector into array
    always_comb begin
        for (int i = 0; i < NUM_FIELDS; i++) begin
            rd_fields[i] = rd_data_packed[i*FIELD_WIDTH +: FIELD_WIDTH];
        end
    end

    gaxi_skid_buffer #(.DATA_WIDTH(TOTAL_WIDTH)) u_buf (
        .axi_aclk(axi_aclk),
        .axi_aresetn(axi_aresetn),
        .wr_valid(wr_valid),
        .wr_ready(wr_ready),
        .wr_data(wr_data_packed),
        .rd_valid(rd_valid),
        .rd_ready(rd_ready),
        .rd_data(rd_data_packed),
        .count(),
        .rd_count()
    );
endmodule
```

**Usage:**

```systemverilog
// 3-field buffer
gaxi_buffer_nfield #(
    .NUM_FIELDS(3),
    .FIELD_WIDTH(64)
) u_3field_buf (
    .wr_fields({field2, field1, field0}),
    .rd_fields({out_field2, out_field1, out_field0})
);

// 8-field buffer
gaxi_buffer_nfield #(
    .NUM_FIELDS(8),
    .FIELD_WIDTH(32)
) u_8field_buf (
    .wr_fields(input_array[7:0]),
    .rd_fields(output_array[7:0])
);
```

### Pattern 5: Variable Width Fields

**Different width for each field:**

```systemverilog
module gaxi_buffer_varwidth #(
    parameter int NUM_FIELDS = 3,
    parameter int FIELD_WIDTHS[NUM_FIELDS] = '{16, 32, 8}  // Array of widths
) (
    input  logic axi_aclk,
    input  logic axi_aresetn,
    input  logic wr_valid,
    output logic wr_ready,

    // Widest field determines interface width
    input  logic [31:0] wr_field0,  // 16 bits used
    input  logic [31:0] wr_field1,  // 32 bits used
    input  logic [31:0] wr_field2,  // 8 bits used

    output logic rd_valid,
    input  logic rd_ready,
    output logic [31:0] rd_field0,
    output logic [31:0] rd_field1,
    output logic [31:0] rd_field2
);
    // Calculate total width
    function automatic int sum_widths();
        int total = 0;
        for (int i = 0; i < NUM_FIELDS; i++)
            total += FIELD_WIDTHS[i];
        return total;
    endfunction

    localparam int TOTAL_WIDTH = sum_widths();  // 16+32+8 = 56

    gaxi_skid_buffer #(.DATA_WIDTH(TOTAL_WIDTH)) u_buf (
        .axi_aclk(axi_aclk),
        .axi_aresetn(axi_aresetn),
        .wr_valid(wr_valid),
        .wr_ready(wr_ready),
        .wr_data({wr_field2[7:0], wr_field1[31:0], wr_field0[15:0]}),
        .rd_valid(rd_valid),
        .rd_ready(rd_ready),
        .rd_data({rd_field2[7:0], rd_field1[31:0], rd_field0[15:0]}),
        .count(),
        .rd_count()
    );

    // Zero-extend unused bits
    assign rd_field0[31:16] = '0;
    assign rd_field2[31:8]  = '0;
endmodule
```

---

## Field Masking and Enables

### Pattern 6: Optional Fields with Enable Signals

**Useful for sparse data structures:**

```systemverilog
module gaxi_buffer_optional_fields (
    input  logic        axi_aclk,
    input  logic        axi_aresetn,
    input  logic        wr_valid,
    output logic        wr_ready,

    // Field data
    input  logic [15:0] wr_field0,
    input  logic [31:0] wr_field1,
    input  logic [7:0]  wr_field2,

    // Field enables
    input  logic        wr_field0_valid,
    input  logic        wr_field1_valid,
    input  logic        wr_field2_valid,

    output logic        rd_valid,
    input  logic        rd_ready,

    // Output fields
    output logic [15:0] rd_field0,
    output logic [31:0] rd_field1,
    output logic [7:0]  rd_field2,

    // Output enables
    output logic        rd_field0_valid,
    output logic        rd_field1_valid,
    output logic        rd_field2_valid
);
    // Include enable bits in packed data
    localparam int DATA_WIDTH = 16 + 32 + 8;
    localparam int ENABLE_WIDTH = 3;
    localparam int TOTAL_WIDTH = DATA_WIDTH + ENABLE_WIDTH;

    gaxi_fifo_sync #(.DATA_WIDTH(TOTAL_WIDTH), .DEPTH(8)) u_fifo (
        .axi_aclk(axi_aclk),
        .axi_aresetn(axi_aresetn),
        .wr_valid(wr_valid),
        .wr_ready(wr_ready),
        .wr_data({
            wr_field0_valid, wr_field1_valid, wr_field2_valid,
            wr_field2, wr_field1, wr_field0
        }),
        .rd_valid(rd_valid),
        .rd_ready(rd_ready),
        .rd_data({
            rd_field0_valid, rd_field1_valid, rd_field2_valid,
            rd_field2, rd_field1, rd_field0
        }),
        .count()
    );
endmodule
```

**Usage:**

```systemverilog
// Send sparse packet (only field1 valid)
.wr_valid(packet_ready),
.wr_field0('x),          // Don't care
.wr_field1(data_value),
.wr_field2('x),          // Don't care
.wr_field0_valid(1'b0),
.wr_field1_valid(1'b1),  // Only this field valid
.wr_field2_valid(1'b0)
```

### Pattern 7: Field Mask Register

**Enable/disable fields via configuration:**

```systemverilog
module gaxi_buffer_masked #(
    parameter int NUM_FIELDS  = 4,
    parameter int FIELD_WIDTH = 32
) (
    input  logic [NUM_FIELDS-1:0] field_enable_mask,  // Config register

    input  logic [NUM_FIELDS-1:0][FIELD_WIDTH-1:0] wr_fields,
    output logic [NUM_FIELDS-1:0][FIELD_WIDTH-1:0] rd_fields
);
    logic [NUM_FIELDS-1:0][FIELD_WIDTH-1:0] wr_fields_masked;

    // Mask disabled fields to 0
    always_comb begin
        for (int i = 0; i < NUM_FIELDS; i++) begin
            wr_fields_masked[i] = field_enable_mask[i] ? wr_fields[i] : '0;
        end
    end

    // Use masked fields in buffer
    gaxi_skid_buffer #(.DATA_WIDTH(NUM_FIELDS * FIELD_WIDTH)) u_buf (
        .wr_data(wr_fields_masked),
        .rd_data(rd_fields)
    );
endmodule
```

---

## Protocol-Specific Wrappers

### Pattern 8: AXI4 Descriptor Buffer

**Domain-specific wrapper for AXI4 DMA descriptors:**

```systemverilog
module axi4_descriptor_fifo #(
    parameter int DEPTH = 16
) (
    input  logic        axi_aclk,
    input  logic        axi_aresetn,

    // Write interface
    input  logic        wr_valid,
    output logic        wr_ready,

    // AXI4 descriptor fields
    input  logic [31:0] wr_awaddr,
    input  logic [7:0]  wr_awlen,
    input  logic [2:0]  wr_awsize,
    input  logic [1:0]  wr_awburst,
    input  logic [7:0]  wr_awid,

    // Read interface
    output logic        rd_valid,
    input  logic        rd_ready,

    output logic [31:0] rd_awaddr,
    output logic [7:0]  rd_awlen,
    output logic [2:0]  rd_awsize,
    output logic [1:0]  rd_awburst,
    output logic [7:0]  rd_awid
);
    // Calculate descriptor width
    localparam int DESC_WIDTH = 32 + 8 + 3 + 2 + 8;  // = 53 bits

    gaxi_fifo_sync #(
        .DATA_WIDTH(DESC_WIDTH),
        .DEPTH(DEPTH)
    ) u_desc_fifo (
        .axi_aclk(axi_aclk),
        .axi_aresetn(axi_aresetn),
        .wr_valid(wr_valid),
        .wr_ready(wr_ready),
        .wr_data({wr_awaddr, wr_awlen, wr_awsize, wr_awburst, wr_awid}),
        .rd_valid(rd_valid),
        .rd_ready(rd_ready),
        .rd_data({rd_awaddr, rd_awlen, rd_awsize, rd_awburst, rd_awid}),
        .count()
    );
endmodule
```

### Pattern 9: Network Packet Header Buffer

**Ethernet/IP header buffering:**

```systemverilog
module packet_header_fifo #(
    parameter int DEPTH = 32
) (
    input  logic        clk,
    input  logic        rst_n,

    // Write interface
    input  logic        wr_valid,
    output logic        wr_ready,

    // Ethernet + IP header fields
    input  logic [47:0] wr_dst_mac,
    input  logic [47:0] wr_src_mac,
    input  logic [15:0] wr_ethertype,
    input  logic [31:0] wr_src_ip,
    input  logic [31:0] wr_dst_ip,
    input  logic [15:0] wr_src_port,
    input  logic [15:0] wr_dst_port,
    input  logic [7:0]  wr_protocol,

    // Read interface
    output logic        rd_valid,
    input  logic        rd_ready,

    output logic [47:0] rd_dst_mac,
    output logic [47:0] rd_src_mac,
    output logic [15:0] rd_ethertype,
    output logic [31:0] rd_src_ip,
    output logic [31:0] rd_dst_ip,
    output logic [15:0] rd_src_port,
    output logic [15:0] rd_dst_port,
    output logic [7:0]  rd_protocol
);
    localparam int HDR_WIDTH = 48+48+16+32+32+16+16+8;  // 216 bits

    gaxi_fifo_sync #(
        .DATA_WIDTH(HDR_WIDTH),
        .DEPTH(DEPTH)
    ) u_hdr_fifo (
        .axi_aclk(clk),
        .axi_aresetn(rst_n),
        .wr_valid(wr_valid),
        .wr_ready(wr_ready),
        .wr_data({
            wr_dst_mac, wr_src_mac, wr_ethertype,
            wr_src_ip, wr_dst_ip,
            wr_src_port, wr_dst_port,
            wr_protocol
        }),
        .rd_valid(rd_valid),
        .rd_ready(rd_ready),
        .rd_data({
            rd_dst_mac, rd_src_mac, rd_ethertype,
            rd_src_ip, rd_dst_ip,
            rd_src_port, rd_dst_port,
            rd_protocol
        }),
        .count()
    );
endmodule
```

---

## Advanced Packing Strategies

### Strategy 1: Field Alignment

**Align fields to natural boundaries:**

```systemverilog
// Without alignment (packs tightly)
{field_a[11:0], field_b[19:0], field_c[15:0]}  // 48 bits total
// Bit positions: field_a[47:36], field_b[35:16], field_c[15:0]

// With alignment (easier to debug)
{4'b0, field_a[11:0], 12'b0, field_b[19:0], field_c[15:0]}  // 64 bits
// Bit positions: field_a[59:48], field_b[35:16], field_c[15:0]
// Trade-off: Uses more bits but aligned to nibble/byte boundaries
```

### Strategy 2: Priority-Based Ordering

**Place high-priority fields in MSBs:**

```systemverilog
module priority_ordered_buffer (
    input  logic [7:0]  critical_field,   // Highest priority
    input  logic [15:0] normal_field,
    input  logic [31:0] low_priority_field
);
    // Pack with critical field at MSB
    wire [55:0] packed = {
        critical_field,      // [55:48] - processed first
        normal_field,        // [47:32]
        low_priority_field   // [31:0]
    };
endmodule
```

### Strategy 3: Hierarchical Fields

**Nested structures:**

```systemverilog
typedef struct packed {
    logic [15:0] address;
    logic [7:0]  length;
} memory_command_t;

typedef struct packed {
    logic [1:0]  operation;  // READ, WRITE, RMW, ATOMIC
    logic [5:0]  flags;
    memory_command_t cmd;
} transaction_t;

module hierarchical_buffer (
    input  transaction_t wr_transaction,
    output transaction_t rd_transaction
);
    localparam int TRANS_WIDTH = $bits(transaction_t);  // Auto-calculate

    gaxi_skid_buffer #(.DATA_WIDTH(TRANS_WIDTH)) u_buf (
        .wr_data(wr_transaction),
        .rd_data(rd_transaction)
    );
endmodule
```

---

## Performance Optimization

### Optimization 1: Reduce Pack/Unpack Logic

**Use generate blocks for efficient packing:**

```systemverilog
module optimized_packing #(
    parameter int NUM_FIELDS  = 8,
    parameter int FIELD_WIDTH = 32
) (
    input  logic [NUM_FIELDS-1:0][FIELD_WIDTH-1:0] wr_fields,
    output logic [NUM_FIELDS-1:0][FIELD_WIDTH-1:0] rd_fields
);
    localparam int TOTAL_WIDTH = NUM_FIELDS * FIELD_WIDTH;
    logic [TOTAL_WIDTH-1:0] wr_flat, rd_flat;

    // Efficient packing using generate
    genvar i;
    generate
        for (i = 0; i < NUM_FIELDS; i++) begin : pack_gen
            assign wr_flat[i*FIELD_WIDTH +: FIELD_WIDTH] = wr_fields[i];
            assign rd_fields[i] = rd_flat[i*FIELD_WIDTH +: FIELD_WIDTH];
        end
    endgenerate

    gaxi_skid_buffer #(.DATA_WIDTH(TOTAL_WIDTH)) u_buf (
        .wr_data(wr_flat),
        .rd_data(rd_flat)
    );
endmodule
```

### Optimization 2: Minimize Field Count

**Combine related fields:**

```systemverilog
// ❌ BEFORE: Many small fields
input  logic [3:0] wr_opcode,
input  logic       wr_error,
input  logic       wr_last,
input  logic       wr_first,
input  logic       wr_valid_data,
// 8 total control signals

// ✅ AFTER: Single control field
input  logic [7:0] wr_control,
// [7:4] = opcode, [3] = error, [2] = last, [1] = first, [0] = valid_data
```

### Optimization 3: Use Appropriate Buffer Type

```systemverilog
// Timing closure only → Skid buffer (minimal resources)
gaxi_skid_buffer_multi #(.DEPTH(2)) u_timing_buf (...);

// Small packet buffer → Sync FIFO
gaxi_fifo_sync_multi #(.DEPTH(8)) u_small_fifo (...);

// Clock domain crossing → Async FIFO
gaxi_fifo_async_multi #(.DEPTH(16)) u_cdc_fifo (...);

// High-perf CDC → Async skid (more resources, better throughput)
gaxi_skid_buffer_async_multi #(.DEPTH(16)) u_perf_cdc (...);
```

---

## Debugging and Verification

### Debug Pattern 1: Field Observability

**Add assertions for field validity:**

```systemverilog
module debug_buffer #(
    parameter int ADDR_WIDTH = 16,
    parameter int DATA_WIDTH = 32
) (
    input logic [ADDR_WIDTH-1:0] wr_addr,
    input logic [DATA_WIDTH-1:0] wr_data,
    ...
);
    // Assertions for field ranges
    `ifdef SIMULATION
    always @(posedge axi_aclk) begin
        if (wr_valid && wr_ready) begin
            assert (wr_addr < 16'hFFFF) else
                $error("Address out of range: 0x%h", wr_addr);

            assert (wr_data != 32'hDEADDEAD) else
                $warning("Suspicious data pattern: 0x%h", wr_data);
        end
    end
    `endif

    // Normal buffer instantiation
    gaxi_skid_buffer_multi #(...) u_buf (...);
endmodule
```

### Debug Pattern 2: Field Tracing

**Add debug signals for waveform analysis:**

```systemverilog
module traced_buffer #(
    parameter int NUM_FIELDS = 4
) (
    ...
);
    // Debug: Expose internal packed data
    (* mark_debug = "true" *) logic [TOTAL_WIDTH-1:0] debug_wr_packed;
    (* mark_debug = "true" *) logic [TOTAL_WIDTH-1:0] debug_rd_packed;

    assign debug_wr_packed = {wr_field3, wr_field2, wr_field1, wr_field0};
    assign debug_rd_packed = {rd_field3, rd_field2, rd_field1, rd_field0};

    gaxi_fifo_sync #(.DATA_WIDTH(TOTAL_WIDTH)) u_fifo (
        .wr_data(debug_wr_packed),
        .rd_data(debug_rd_packed)
    );
endmodule
```

### Debug Pattern 3: Field Mismatch Detection

**Catch pack/unpack errors:**

```systemverilog
`ifdef SIMULATION
    // Check that pack/unpack is consistent
    logic [TOTAL_WIDTH-1:0] loopback_test;
    assign loopback_test = {wr_addr, wr_ctrl, wr_data1, wr_data0};

    logic [ADDR_WIDTH-1:0] check_addr;
    logic [CTRL_WIDTH-1:0] check_ctrl;
    logic [DATA_WIDTH-1:0] check_data0, check_data1;
    assign {check_addr, check_ctrl, check_data1, check_data0} = loopback_test;

    always @(posedge axi_aclk) begin
        if (wr_valid) begin
            assert (check_addr === wr_addr) else
                $error("Addr pack/unpack mismatch!");
            assert (check_ctrl === wr_ctrl) else
                $error("Ctrl pack/unpack mismatch!");
            assert (check_data0 === wr_data0) else
                $error("Data0 pack/unpack mismatch!");
            assert (check_data1 === wr_data1) else
                $error("Data1 pack/unpack mismatch!");
        end
    end
`endif
```

---

## Best Practices Summary

### ✅ DO

1. **Use descriptive field names** - `wr_transaction_id` not `wr_data0`
2. **Document bit positions** - Add comments showing field layout
3. **Consistent pack/unpack order** - Same concatenation everywhere
4. **Power-of-2 depths for async FIFOs** - Required for Gray code
5. **Add assertions in simulation** - Catch field range violations
6. **Use structs for complex fields** - Leverage SystemVerilog type system
7. **Test with walking patterns** - Verify each field independently

### ❌ DON'T

1. **Mix field orders** - Causes silent data corruption
2. **Use non-power-of-2 async depths** - Will fail in synthesis
3. **Ignore valid-ready protocol** - Leads to data loss
4. **Hardcode widths in multiple places** - Use parameters
5. **Skip field width checking** - Use assertions
6. **Forget to test CDC** - Async FIFOs need special verification

---

## Related Documentation

- [GAXI Multi-Field Integration Tutorial](gaxi_multi_field_integration.md) - Prerequisite
- [GAXI Protocol Overview](../RTLAmba/fabric/gaxi_overview.md)
- [WaveDrom GAXI Example](wavedrom_gaxi_example.md) - Visualizing multi-field transfers
- [Test Examples](advanced_examples.md)

---

## Example Testbenches

**All patterns demonstrated in:**
- `val/integ_amba/test_gaxi_buffer_multi.py`
- `val/integ_amba/test_gaxi_buffer_multi_sigmap.py`

**RTL examples in:**
- `rtl/amba/testcode/gaxi_*.sv` - All 5 multi-field modules

**Run tests:**
```bash
cd val/integ_amba
pytest test_gaxi_buffer_multi.py -v
```

---

**Next Steps:**
1. Review testcode modules: `rtl/amba/testcode/`
2. Study test infrastructure: `bin/CocoTBFramework/tbclasses/gaxi/gaxi_buffer_multi.py`
3. Create your own protocol-specific wrapper
4. Add comprehensive tests with field-level checking
