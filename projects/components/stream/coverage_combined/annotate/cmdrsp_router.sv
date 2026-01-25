//      // verilator_coverage annotation
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
 004646     input  logic                    clk,
%000002     input  logic                    rst_n,
        
            // CMD/RSP Slave (from apb_slave_cdc)
 000048     input  logic                    s_cmd_valid,
 000010     output logic                    s_cmd_ready,
 000028     input  logic                    s_cmd_pwrite,
%000000     input  logic [ADDR_WIDTH-1:0]   s_cmd_paddr,
%000000     input  logic [DATA_WIDTH-1:0]   s_cmd_pwdata,
 000048     output logic                    s_rsp_valid,
%000002     input  logic                    s_rsp_ready,
%000000     output logic [DATA_WIDTH-1:0]   s_rsp_prdata,
%000000     output logic                    s_rsp_pslverr,
        
            // CMD/RSP Master 0: Descriptor kick-off (0x000-0x03F)
%000008     output logic                    m0_cmd_valid,
 000010     input  logic                    m0_cmd_ready,
 000028     output logic                    m0_cmd_pwrite,
%000000     output logic [ADDR_WIDTH-1:0]   m0_cmd_paddr,
%000000     output logic [DATA_WIDTH-1:0]   m0_cmd_pwdata,
%000008     input  logic                    m0_rsp_valid,
%000008     output logic                    m0_rsp_ready,
%000000     input  logic [DATA_WIDTH-1:0]   m0_rsp_prdata,
%000000     input  logic                    m0_rsp_pslverr,
        
            // CMD/RSP Master 1: Configuration registers (default route for all non-m0/perf addresses)
 000040     output logic                    m1_cmd_valid,
 000042     input  logic                    m1_cmd_ready,
 000028     output logic                    m1_cmd_pwrite,
%000000     output logic [ADDR_WIDTH-1:0]   m1_cmd_paddr,
%000000     output logic [DATA_WIDTH-1:0]   m1_cmd_pwdata,
 000040     input  logic                    m1_rsp_valid,
 000040     output logic                    m1_rsp_ready,
%000000     input  logic [DATA_WIDTH-1:0]   m1_rsp_prdata,
%000000     input  logic                    m1_rsp_pslverr,
        
            //-------------------------------------------------------------------------
            // Performance Profiler Interface (0x040-0x0FF, integrated registers)
            //-------------------------------------------------------------------------
            // Configuration outputs
%000000     output logic                    perf_cfg_enable,
%000000     output logic                    perf_cfg_mode,
%000000     output logic                    perf_cfg_clear,
        
            // FIFO read interface
%000000     input  logic [31:0]             perf_fifo_data_low,
%000000     input  logic [31:0]             perf_fifo_data_high,
%000002     input  logic                    perf_fifo_empty,
%000000     input  logic                    perf_fifo_full,
%000000     input  logic [15:0]             perf_fifo_count,
%000000     output logic                    perf_fifo_rd
        );
        
            //=========================================================================
            // Address Decode
            //=========================================================================
 000042     logic addr_hit_m0;   // 0x000-0x03F - Descriptor kick-off (explicit)
%000000     logic addr_hit_perf; // 0x040-0x0FF - Performance profiler (explicit, integrated)
 000040     logic addr_hit_m1;   // Everything else - Configuration registers (default route)
        
%000002     always_comb begin
%000002         addr_hit_m0   = (s_cmd_paddr[ADDR_WIDTH-1:6] == '0);  // 0x000-0x03F
%000002         addr_hit_perf = (s_cmd_paddr[ADDR_WIDTH-1:8] == '0) && (s_cmd_paddr[7:6] != 2'b00);  // 0x040-0x0FF
                // m1 is default route: anything that doesn't match m0 or perf
%000002         addr_hit_m1   = !addr_hit_m0 && !addr_hit_perf;
            end
        
            //=========================================================================
            // Selection Tracking (for response routing)
            //=========================================================================
%000008     logic r_sel_m0;
%000000     logic r_sel_perf;
 000040     logic r_sel_m1;
        
 002324     always_ff @(posedge clk or negedge rst_n) begin
 000022         if (!rst_n) begin
 000022             r_sel_m0   <= 1'b0;
 000022             r_sel_perf <= 1'b0;
 000022             r_sel_m1   <= 1'b0;
 002302         end else begin
                    // Capture selection when command accepted
 000024             if (s_cmd_valid && s_cmd_ready) begin
 000024                 r_sel_m0   <= addr_hit_m0;
 000024                 r_sel_perf <= addr_hit_perf;
 000024                 r_sel_m1   <= addr_hit_m1;
                    end
                    // Clear selection when response accepted
 000024             if (s_rsp_valid && s_rsp_ready) begin
 000024                 r_sel_m0   <= 1'b0;
 000024                 r_sel_perf <= 1'b0;
 000024                 r_sel_m1   <= 1'b0;
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
%000000     logic [2:0] r_perf_config;  // {cfg_clear, cfg_mode, cfg_enable}
        
 002324     always_ff @(posedge clk or negedge rst_n) begin
 000022         if (!rst_n) begin
 000022             r_perf_config <= 3'b000;  // All disabled on reset
 002302         end else begin
                    // Write to PERF_CONFIG register
%000000             if (s_cmd_valid && s_cmd_ready && addr_hit_perf &&
%000000                 s_cmd_pwrite && (s_cmd_paddr[7:0] == PERF_CONFIG_ADDR)) begin
%000000                 r_perf_config <= s_cmd_pwdata[2:0];
                    end
                    // Auto-clear cfg_clear after one cycle
%000000             else if (r_perf_config[2]) begin
%000000                 r_perf_config[2] <= 1'b0;
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
%000000     logic [DATA_WIDTH-1:0] perf_rsp_data;
%000000     logic                  perf_rsp_valid;
%000002     logic                  perf_rsp_ready_internal;
        
 021934     always_comb begin
 021934         perf_rsp_data = 32'h0;
 021934         case (s_cmd_paddr[7:0])
 000036             PERF_CONFIG_ADDR: begin
 000036                 perf_rsp_data = {29'h0, r_perf_config};
                    end
%000000             PERF_DATA_LOW_ADDR: begin
%000000                 perf_rsp_data = perf_fifo_data_low;
                    end
%000000             PERF_DATA_HIGH_ADDR: begin
%000000                 perf_rsp_data = perf_fifo_data_high;
                    end
%000000             PERF_STATUS_ADDR: begin
%000000                 perf_rsp_data = {15'h0, perf_fifo_count, 14'h0, perf_fifo_full, perf_fifo_empty};
                    end
 021898             default: begin
 021898                 perf_rsp_data = 32'hDEADBEEF;  // Invalid address within perf range
                    end
                endcase
            end
        
            // Perf profiler always ready (single-cycle response)
            assign perf_rsp_ready_internal = 1'b1;
        
            // Response valid (single cycle after command accepted)
 002324     always_ff @(posedge clk or negedge rst_n) begin
 000022         if (!rst_n) begin
 000022             perf_rsp_valid <= 1'b0;
 002302         end else begin
%000000             if (s_cmd_valid && s_cmd_ready && addr_hit_perf) begin
%000000                 perf_rsp_valid <= 1'b1;
%000000             end else if (perf_rsp_valid && s_rsp_ready) begin
%000000                 perf_rsp_valid <= 1'b0;
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
        
