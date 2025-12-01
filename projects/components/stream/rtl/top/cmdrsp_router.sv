`timescale 1ns / 1ps

// Module: cmdrsp_router
// Description: Routes CMD/RSP transactions based on address
//
// Routing Architecture:
//   - Explicit decode: 0x000-0x03F → Descriptor kick-off (apbtodescr)
//   - Explicit decode: 0x040-0x0FF → Performance profiler (integrated)
//   - Default route:   Everything else → Configuration registers (peakrdl_to_cmdrsp)
//
// This ensures PeakRDL config space can handle any register address
// (including future additions like 0x220-0x230 descriptor engine config)
// without requiring router updates.
//
// Performance Profiler Registers (0x040-0x0FF):
//   0x040: PERF_CONFIG      - R/W: {30'b0, cfg_clear, cfg_mode, cfg_enable}
//   0x044: PERF_DATA_LOW    - RO:  Timestamp/elapsed [31:0] (read pops FIFO)
//   0x048: PERF_DATA_HIGH   - RO:  {28'b0, event_type, channel_id[2:0]}
//   0x04C: PERF_STATUS      - RO:  {15'b0, count[15:0], 14'b0, full, empty}
//
// Protocol: CMD/RSP handshake protocol
//   - Command phase: valid/ready handshake with address, write flag, data
//   - Response phase: valid/ready handshake with read data or error

module cmdrsp_router #(
    parameter int ADDR_WIDTH = 12,  // Total address width
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

    // CMD/RSP Master 1: Configuration registers (default route for all non-m0/perf addresses)
    output logic                    m1_cmd_valid,
    input  logic                    m1_cmd_ready,
    output logic                    m1_cmd_pwrite,
    output logic [ADDR_WIDTH-1:0]   m1_cmd_paddr,
    output logic [DATA_WIDTH-1:0]   m1_cmd_pwdata,
    input  logic                    m1_rsp_valid,
    output logic                    m1_rsp_ready,
    input  logic [DATA_WIDTH-1:0]   m1_rsp_prdata,
    input  logic                    m1_rsp_pslverr,

    //-------------------------------------------------------------------------
    // Performance Profiler Interface (0x040-0x0FF, integrated registers)
    //-------------------------------------------------------------------------
    // Configuration outputs
    output logic                    perf_cfg_enable,
    output logic                    perf_cfg_mode,
    output logic                    perf_cfg_clear,

    // FIFO read interface
    input  logic [31:0]             perf_fifo_data_low,
    input  logic [31:0]             perf_fifo_data_high,
    input  logic                    perf_fifo_empty,
    input  logic                    perf_fifo_full,
    input  logic [15:0]             perf_fifo_count,
    output logic                    perf_fifo_rd
);

    //=========================================================================
    // Address Decode
    //=========================================================================
    logic addr_hit_m0;   // 0x000-0x03F - Descriptor kick-off (explicit)
    logic addr_hit_perf; // 0x040-0x0FF - Performance profiler (explicit, integrated)
    logic addr_hit_m1;   // Everything else - Configuration registers (default route)

    always_comb begin
        addr_hit_m0   = (s_cmd_paddr[ADDR_WIDTH-1:6] == '0);  // 0x000-0x03F
        addr_hit_perf = (s_cmd_paddr[ADDR_WIDTH-1:8] == '0) && (s_cmd_paddr[7:6] != 2'b00);  // 0x040-0x0FF
        // m1 is default route: anything that doesn't match m0 or perf
        addr_hit_m1   = !addr_hit_m0 && !addr_hit_perf;
    end

    //=========================================================================
    // Selection Tracking (for response routing)
    //=========================================================================
    logic r_sel_m0;
    logic r_sel_perf;
    logic r_sel_m1;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_sel_m0   <= 1'b0;
            r_sel_perf <= 1'b0;
            r_sel_m1   <= 1'b0;
        end else begin
            // Capture selection when command accepted
            if (s_cmd_valid && s_cmd_ready) begin
                r_sel_m0   <= addr_hit_m0;
                r_sel_perf <= addr_hit_perf;
                r_sel_m1   <= addr_hit_m1;
            end
            // Clear selection when response accepted
            if (s_rsp_valid && s_rsp_ready) begin
                r_sel_m0   <= 1'b0;
                r_sel_perf <= 1'b0;
                r_sel_m1   <= 1'b0;
            end
        end
    end

    //=========================================================================
    // Performance Profiler Register Logic (Integrated)
    //=========================================================================
    // Register addresses (offset from 0x040):
    localparam logic [7:0] PERF_CONFIG_ADDR    = 8'h40;  // 0x040: Config register
    localparam logic [7:0] PERF_DATA_LOW_ADDR  = 8'h44;  // 0x044: FIFO data low
    localparam logic [7:0] PERF_DATA_HIGH_ADDR = 8'h48;  // 0x048: FIFO data high
    localparam logic [7:0] PERF_STATUS_ADDR    = 8'h4C;  // 0x04C: FIFO status

    // Configuration register (writable)
    logic [2:0] r_perf_config;  // {cfg_clear, cfg_mode, cfg_enable}

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r_perf_config <= 3'b000;  // All disabled on reset
        end else begin
            // Write to PERF_CONFIG register
            if (s_cmd_valid && s_cmd_ready && addr_hit_perf &&
                s_cmd_pwrite && (s_cmd_paddr[7:0] == PERF_CONFIG_ADDR)) begin
                r_perf_config <= s_cmd_pwdata[2:0];
            end
            // Auto-clear cfg_clear after one cycle
            else if (r_perf_config[2]) begin
                r_perf_config[2] <= 1'b0;
            end
        end
    end

    // Configuration outputs
    assign perf_cfg_enable = r_perf_config[0];
    assign perf_cfg_mode   = r_perf_config[1];
    assign perf_cfg_clear  = r_perf_config[2];

    // FIFO read strobe (asserted when PERF_DATA_LOW is read)
    assign perf_fifo_rd = s_cmd_valid && s_cmd_ready && addr_hit_perf &&
                         !s_cmd_pwrite && (s_cmd_paddr[7:0] == PERF_DATA_LOW_ADDR);

    // Register read data
    logic [DATA_WIDTH-1:0] perf_rsp_data;
    logic                  perf_rsp_valid;
    logic                  perf_rsp_ready_internal;

    always_comb begin
        perf_rsp_data = 32'h0;
        case (s_cmd_paddr[7:0])
            PERF_CONFIG_ADDR: begin
                perf_rsp_data = {29'h0, r_perf_config};
            end
            PERF_DATA_LOW_ADDR: begin
                perf_rsp_data = perf_fifo_data_low;
            end
            PERF_DATA_HIGH_ADDR: begin
                perf_rsp_data = perf_fifo_data_high;
            end
            PERF_STATUS_ADDR: begin
                perf_rsp_data = {15'h0, perf_fifo_count, 14'h0, perf_fifo_full, perf_fifo_empty};
            end
            default: begin
                perf_rsp_data = 32'hDEADBEEF;  // Invalid address within perf range
            end
        endcase
    end

    // Perf profiler always ready (single-cycle response)
    assign perf_rsp_ready_internal = 1'b1;

    // Response valid (single cycle after command accepted)
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            perf_rsp_valid <= 1'b0;
        end else begin
            if (s_cmd_valid && s_cmd_ready && addr_hit_perf) begin
                perf_rsp_valid <= 1'b1;
            end else if (perf_rsp_valid && s_rsp_ready) begin
                perf_rsp_valid <= 1'b0;
            end
        end
    end

    //=========================================================================
    // Command Routing
    //=========================================================================
    assign m0_cmd_valid  = s_cmd_valid && addr_hit_m0;
    assign m0_cmd_pwrite = s_cmd_pwrite;
    assign m0_cmd_paddr  = s_cmd_paddr;
    assign m0_cmd_pwdata = s_cmd_pwdata;

    // m1 gets everything that doesn't go to m0 or perf (default route)
    assign m1_cmd_valid  = s_cmd_valid && addr_hit_m1;
    assign m1_cmd_pwrite = s_cmd_pwrite;
    assign m1_cmd_paddr  = s_cmd_paddr;
    assign m1_cmd_pwdata = s_cmd_pwdata;

    // Command ready (mux based on address, default to m1)
    assign s_cmd_ready = addr_hit_m0   ? m0_cmd_ready :
                        addr_hit_perf ? perf_rsp_ready_internal :  // Perf always ready
                        m1_cmd_ready;  // Default route to m1 for everything else

    //=========================================================================
    // Response Routing
    //=========================================================================
    // Default to m1 response if neither m0 nor perf selected
    assign s_rsp_valid   = r_sel_m0   ? m0_rsp_valid :
                          r_sel_perf ? perf_rsp_valid :
                          m1_rsp_valid;  // Default route

    assign s_rsp_prdata  = r_sel_m0   ? m0_rsp_prdata :
                          r_sel_perf ? perf_rsp_data :
                          m1_rsp_prdata;  // Default route

    assign s_rsp_pslverr = r_sel_m0   ? m0_rsp_pslverr :
                          r_sel_perf ? 1'b0 :  // Perf never errors
                          m1_rsp_pslverr;  // Default route (m1 handles errors)

    assign m0_rsp_ready = r_sel_m0 && s_rsp_ready;
    assign m1_rsp_ready = r_sel_m1 && s_rsp_ready;
    // Note: perf uses perf_rsp_ready_internal (always 1)

endmodule : cmdrsp_router
