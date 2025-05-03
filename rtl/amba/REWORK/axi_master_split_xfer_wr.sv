`timescale 1ns / 1ps

// Import packages
import axi_pkg::*;
import amba_error_pkg::*;

module axi_master_split_xfer_wr #(
    parameter int MAX_OUTSTANDING     = 8,     // Maximum outstanding transactions
    parameter int AXI_ADDR_WIDTH     = 32,    // Address width
    parameter int AXI_DATA_WIDTH     = 64,    // AXI side data width
    parameter int USER_DATA_WIDTH    = 32,    // User side data width
    // Short params and calculations
    parameter int MO       = MAX_OUTSTANDING,
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int UDW     = USER_DATA_WIDTH,
    // Derived parameters for width conversion
    parameter int AXI_STRB_WIDTH  = DW/8,
    parameter int USER_STRB_WIDTH = UDW/8,
    parameter int WIDTH_RATIO     = DW > UDW ? DW/UDW : UDW/DW,
    parameter int LOG2_WR         = $clog2(WIDTH_RATIO),
    parameter int LOG2_MO         = $clog2(MO+1)
) (
    input  logic                     i_clk,
    input  logic                     i_rst_n,

    // User command interface
    input  logic                     i_user_cmd_valid,
    output logic                     o_user_cmd_ready,
    input  logic [AW-1:0]            i_user_cmd_addr,
    input  logic [7:0]               i_user_cmd_len,
    input  logic [2:0]               i_user_cmd_size,
    input  logic [1:0]               i_user_cmd_burst,
    input  logic [3:0]               i_user_cmd_id,
    input  logic                     i_user_cmd_lock,
    input  logic [3:0]               i_user_cmd_cache,
    input  logic [2:0]               i_user_cmd_prot,
    input  logic [3:0]                i_user_cmd_qos,
    input  logic [3:0]                i_user_cmd_region,
    input  logic [AXI_USER_WIDTH-1:0] i_user_cmd_user,
    input  logic [11:0]              i_alignment_boundary,

    // User write data interface
    input  logic [UDW-1:0]           i_user_wdata,
    input  logic [USER_STRB_WIDTH-1:0] i_user_wstrb,
    input  logic                      i_user_wvalid,
    output logic                      o_user_wready,
    input  logic                      i_user_wlast,

    // User write response interface
    output logic                      o_user_bvalid,
    input  logic                      i_user_bready,
    output logic [1:0]               o_user_bresp,
    output logic [3:0]               o_user_bid,

    // AXI write address channel
    output logic                      o_axi_awvalid,
    input  logic                      i_axi_awready,
    output logic [AW-1:0]            o_axi_awaddr,
    output logic [7:0]               o_axi_awlen,
    output logic [2:0]               o_axi_awsize,
    output logic [1:0]               o_axi_awburst,
    output logic [3:0]               o_axi_awid,
    output logic                      o_axi_awlock,
    output logic [3:0]               o_axi_awcache,
    output logic [2:0]               o_axi_awprot,
    output logic [3:0]               o_axi_awqos,
    output logic [3:0]               o_axi_awregion,
    output logic [AXI_USER_WIDTH-1:0] o_axi_awuser,

    // AXI write data channel
    output logic                      o_axi_wvalid,
    input  logic                      i_axi_wready,
    output logic [DW-1:0]            o_axi_wdata,
    output logic [AXI_STRB_WIDTH-1:0] o_axi_wstrb,
    output logic                      o_axi_wlast,
    output logic [AXI_USER_WIDTH-1:0] o_axi_wuser,

    // AXI write response channel
    input  logic                      i_axi_bvalid,
    output logic                      o_axi_bready,
    input  logic [1:0]               i_axi_bresp,
    input  logic [3:0]               i_axi_bid,
    input  logic [AXI_USER_WIDTH-1:0] i_axi_buser,

    // Error and status interface
    output error_type_t              o_error_type,
    output logic [31:0]              o_error_count,
    output logic [31:0]              o_error_addr,
    output logic [31:0]              o_trans_count,
    output logic [31:0]              o_timeout_count
);

// State machine encoding
typedef enum logic [5:0] {
    ST_IDLE     = 6'b000001,
    ST_CALC     = 6'b000010,
    ST_ADDR     = 6'b000100,
    ST_DATA     = 6'b001000,
    ST_RESP     = 6'b010000,
    ST_ERROR    = 6'b100000
} state_t;

// Transfer control registers
state_t               r_state;
logic [AW-1:0]       r_curr_addr;
logic [AW-1:0]       r_boundary_addr;
logic [7:0]          r_total_len;
logic [7:0]          r_current_len;
logic [7:0]          r_beats_remaining;
logic [2:0]          r_size;
logic [1:0]          r_burst;
logic                r_last_split;
logic [AW-1:0]       r_alignment_mask;
logic [7:0]          r_data_count;      // Counts data beats in current burst

// Data conversion control registers
logic [DW-1:0]       r_data_buffer;     // Buffer for width conversion
logic [AXI_STRB_WIDTH-1:0] r_strb_buffer;   // Buffer for write strobes
logic [LOG2_WR-1:0]  r_conv_count;      // Counter for width conversion
logic                r_conv_in_progress; // Conversion in progress flag
logic [2:0]          r_byte_offset;     // Byte offset for unaligned transfers
logic [7:0]          r_adjusted_len;    // Length adjusted for width conversion
logic                r_data_phase_done; // Current data phase completion flag

// Command storage registers
logic [3:0]          r_cmd_id;
logic                r_cmd_lock;
logic [3:0]          r_cmd_cache;
logic [2:0]          r_cmd_prot;
logic [3:0]          r_cmd_qos;
logic [3:0]          r_cmd_region;
logic [AXI_USER_WIDTH-1:0] r_cmd_user;

// Error handling registers
error_type_t         r_error_type;
logic [31:0]         r_error_count;
logic [31:0]         r_error_addr;
logic [31:0]         r_trans_count;
logic [31:0]         r_timeout_count;
logic [31:0]         r_timeout_counter;
localparam int       TIMEOUT_LIMIT = 1000;

// Outstanding transaction counter
logic [LOG2_MO-1:0]  r_outstanding_count;
logic                w_can_accept;

// Control signals
logic               w_cross_boundary;
logic [7:0]         w_beats_to_boundary;
logic               w_addr_aligned;
logic               w_valid_burst_type;
logic               w_valid_burst_length;
logic               w_width_conversion_done;

// Width conversion-specific signals
logic [LOG2_WR-1:0] w_required_beats;
logic               w_is_upsizing;
logic               w_is_downsizing;

// Conversion mode detection
assign w_is_upsizing = UDW > DW;
assign w_is_downsizing = DW > UDW;

// Calculate required beats for width conversion
assign w_required_beats = w_is_upsizing ? WIDTH_RATIO : 1;

// Validation signals
assign w_valid_burst_type = (r_burst inside {BURST_TYPE_FIXED, BURST_TYPE_INCR, BURST_TYPE_WRAP});
assign w_valid_burst_length = (r_total_len < AXI_MAX_BURST_LENGTH);
assign w_can_accept = (r_outstanding_count < MO);
assign w_width_conversion_done = w_is_upsizing ?
                                (r_conv_count == w_required_beats - 1) :
                                (w_is_downsizing ? (r_conv_count == WIDTH_RATIO - 1) : 1'b1);

// Width conversion control
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_data_buffer <= '0;
        r_strb_buffer <= '0;
        r_conv_count <= '0;
        r_conv_in_progress <= 1'b0;
        r_byte_offset <= '0;
        r_data_phase_done <= 1'b0;
    end else begin
        if (r_state == ST_IDLE) begin
            // Reset conversion state on new command
            if (i_user_cmd_valid && w_can_accept) begin
                r_byte_offset <= i_user_cmd_addr[2:0];
                r_conv_in_progress <= 1'b0;
                r_conv_count <= '0;
                r_data_phase_done <= 1'b0;
            end
        end else if (r_state == ST_DATA) begin
            if (i_user_wvalid && o_user_wready) begin
                if (w_is_upsizing) begin
                    // For upsizing: collect multiple narrow writes
                    r_data_buffer[r_conv_count * UDW +: UDW] <= i_user_wdata;
                    r_strb_buffer[r_conv_count * USER_STRB_WIDTH +: USER_STRB_WIDTH] <= i_user_wstrb;
                    r_conv_count <= r_conv_count + 1;
                    r_conv_in_progress <= 1'b1;
                    // Check if we've collected enough data for a wide write
                    if (r_conv_count == WIDTH_RATIO - 1) begin
                        r_conv_in_progress <= 1'b0;
                        r_conv_count <= '0;
                    end
                end else if (w_is_downsizing) begin
                    // For downsizing: buffer wide write data
                    r_data_buffer <= i_user_wdata;
                    r_strb_buffer <= i_user_wstrb;
                    r_conv_in_progress <= 1'b1;
                end
            end else if (o_axi_wvalid && i_axi_wready) begin
                if (w_is_downsizing) begin
                    // For downsizing: increment position in buffer
                    r_conv_count <= r_conv_count + 1;
                    if (r_conv_count == WIDTH_RATIO - 1) begin
                        r_conv_in_progress <= 1'b0;
                        r_conv_count <= '0;
                    end
                end
            end

            // Track data phase completion
            if (i_user_wvalid && o_user_wready && i_user_wlast) begin
                r_data_phase_done <= 1'b1;
            end
        end else begin
            r_data_phase_done <= 1'b0;
        end
    end
end

// Calculate adjusted length for AXI transactions based on width conversion
always_comb begin
    if (w_is_upsizing)
        r_adjusted_len = {1'b0, i_user_cmd_len} >> LOG2_WR;
    else if (w_is_downsizing)
        r_adjusted_len = {i_user_cmd_len, {LOG2_WR{1'b0}}} + WIDTH_RATIO - 1;
    else
        r_adjusted_len = i_user_cmd_len;
end

// Boundary crossing calculation
always_comb begin
    // Calculate next aligned boundary based on dynamic mask
    r_boundary_addr = (r_curr_addr & ~r_alignment_mask) + (1 << i_alignment_boundary);

    // Check if transfer crosses boundary using dynamic mask
    w_cross_boundary = ((r_curr_addr & ~r_alignment_mask) !=
                        ((r_curr_addr + (r_beats_remaining << r_size)) & ~r_alignment_mask));

    // Calculate beats to next boundary
    w_beats_to_boundary = ((r_boundary_addr - r_curr_addr) >> r_size);

    // Check address alignment for current transfer size
    w_addr_aligned = ((r_curr_addr & ((1 << r_size) - 1)) == 0);
end

// Main state machine
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_state <= ST_IDLE;
        r_curr_addr <= '0;
        r_total_len <= '0;
        r_current_len <= '0;
        r_beats_remaining <= '0;
        r_size <= '0;
        r_burst <= '0;
        r_last_split <= 1'b0;
        r_outstanding_count <= '0;
        r_cmd_id <= '0;
        r_cmd_lock <= '0;
        r_cmd_cache <= '0;
        r_cmd_prot <= '0;
        r_cmd_qos <= '0;
        r_cmd_region <= '0;
        r_cmd_user <= '0;
        r_alignment_mask <= '1;
        r_data_count <= '0;
    end else begin
        casez (r_state)
            ST_IDLE: begin
                if (i_user_cmd_valid && w_can_accept) begin
                    r_state <= ST_CALC;
                    r_curr_addr <= i_user_cmd_addr;
                    r_total_len <= r_adjusted_len;  // Use adjusted length
                    r_beats_remaining <= r_adjusted_len + 1;
                    r_size <= i_user_cmd_size;
                    r_burst <= i_user_cmd_burst;
                    r_last_split <= 1'b0;
                    r_data_count <= '0;
                    // Store command attributes
                    r_cmd_id <= i_user_cmd_id;
                    r_cmd_lock <= i_user_cmd_lock;
                    r_cmd_cache <= i_user_cmd_cache;
                    r_cmd_prot <= i_user_cmd_prot;
                    r_cmd_qos <= i_user_cmd_qos;
                    r_cmd_region <= i_user_cmd_region;
                    r_cmd_user <= i_user_cmd_user;
                    // Calculate alignment mask
                    r_alignment_mask <= (1 << i_alignment_boundary) - 1;
                end
            end

            ST_CALC: begin
                if (!w_addr_aligned || !w_valid_burst_type || !w_valid_burst_length)
                    r_state <= ST_ERROR;
                else begin
                    r_state <= ST_ADDR;
                    if (w_cross_boundary) begin
                        r_current_len <= w_beats_to_boundary - 1;
                        r_beats_remaining <= r_beats_remaining - w_beats_to_boundary;
                        r_last_split <= 1'b0;
                    end else begin
                        r_current_len <= r_beats_remaining - 1;
                        r_last_split <= 1'b1;
                    end
                end
            end

            ST_ADDR: begin
                if (o_axi_awvalid && i_axi_awready) begin
                    r_state <= ST_DATA;
                    r_curr_addr <= r_boundary_addr;
                    r_outstanding_count <= r_outstanding_count + 1;
                end
            end

            ST_DATA: begin
                if (o_axi_wvalid && i_axi_wready) begin
                    r_data_count <= r_data_count + 1;
                end
                if (o_axi_wvalid && i_axi_wready && o_axi_wlast) begin
                    r_state <= ST_RESP;
                    r_data_count <= '0;
                end
            end

            ST_RESP: begin
                if (i_axi_bvalid && o_axi_bready) begin
                    r_outstanding_count <= r_outstanding_count - 1;
                    if (i_axi_bresp != RESP_OKAY)
                        r_state <= ST_ERROR;
                    else if (r_last_split)
                        r_state <= ST_IDLE;
                    else
                        r_state <= ST_CALC;
                end
            end

            ST_ERROR: begin
                if (r_outstanding_count == 0)
                    r_state <= ST_IDLE;
            end

            default: r_state <= ST_IDLE;
        endcase
    end
end

// Error handling
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_error_type <= ERR_NONE;
        r_error_count <= '0;
        r_error_addr <= '0;
        r_timeout_counter <= '0;
    end else begin
        // Timeout counter
        if (r_state == ST_DATA || r_state == ST_RESP)
            r_timeout_counter <= r_timeout_counter + 1;
        else
            r_timeout_counter <= '0;

        // Error detection
        if (r_state == ST_CALC) begin
            if (!w_addr_aligned) begin
                r_error_type <= ERR_ALIGNMENT;
                r_error_addr <= r_curr_addr;
                r_error_count <= r_error_count + 1;
            end else if (!w_valid_burst_type) begin
                r_error_type <= ERR_BURST;
                r_error_addr <= r_curr_addr;
                r_error_count <= r_error_count + 1;
            end
        end else if (r_timeout_counter >= TIMEOUT_LIMIT) begin
            r_error_type <= ERR_TIMEOUT;
            r_error_addr <= r_curr_addr;
            r_error_count <= r_error_count + 1;
        end else if (r_state == ST_RESP && i_axi_bvalid && i_axi_bresp != RESP_OKAY) begin
            r_error_type <= ERR_PROT_AXI;
            r_error_addr <= r_curr_addr;
            r_error_count <= r_error_count + 1;
        end
    end
end

// Performance monitoring
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_trans_count <= '0;
        r_timeout_count <= '0;
    end else begin
        // Count successful transactions
        if (i_axi_bvalid && o_axi_bready && i_axi_bresp == RESP_OKAY)
            r_trans_count <= r_trans_count + 1;
        // Count timeouts
        if (r_timeout_counter >= TIMEOUT_LIMIT)
            r_timeout_count <= r_timeout_count + 1;
    end
end

// AXI write address channel assignments
assign o_axi_awvalid = (r_state == ST_ADDR);
assign o_axi_awaddr = r_curr_addr;
assign o_axi_awlen = r_current_len;
assign o_axi_awsize = r_size;
assign o_axi_awburst = r_burst;
assign o_axi_awid = r_cmd_id;
assign o_axi_awlock = r_cmd_lock;
assign o_axi_awcache = r_cmd_cache;
assign o_axi_awprot = r_cmd_prot;
assign o_axi_awqos = r_cmd_qos;
assign o_axi_awregion = r_cmd_region;
assign o_axi_awuser = r_cmd_user;

// AXI write data channel assignments
always_comb begin
    if (w_is_upsizing) begin
        // Combine multiple narrow writes into one wide write
        o_axi_wvalid = r_conv_in_progress && w_width_conversion_done;
        o_axi_wdata = r_data_buffer;
        o_axi_wstrb = r_strb_buffer;
        o_axi_wlast = (r_data_count == r_current_len) && w_width_conversion_done;
        o_user_wready = !r_conv_in_progress || (r_conv_in_progress && !w_width_conversion_done);
    end else if (w_is_downsizing) begin
        // Split wide write into multiple narrow writes
        o_axi_wvalid = i_user_wvalid && r_conv_in_progress;
        o_axi_wdata = {DW{1'b0}};  // Zero padding
        o_axi_wdata[UDW-1:0] = r_data_buffer[r_conv_count * UDW +: UDW];
        o_axi_wstrb = {AXI_STRB_WIDTH{1'b0}};  // Zero padding
        o_axi_wstrb[USER_STRB_WIDTH-1:0] = r_strb_buffer[r_conv_count * USER_STRB_WIDTH +: USER_STRB_WIDTH];
        o_axi_wlast = (r_data_count == r_current_len) && (r_conv_count == WIDTH_RATIO - 1);
        o_user_wready = !r_conv_in_progress;
    end else begin
        // Direct passthrough when widths match
        o_axi_wvalid = i_user_wvalid;
        o_axi_wdata = i_user_wdata;
        o_axi_wstrb = i_user_wstrb;
        o_axi_wlast = i_user_wlast;
        o_user_wready = i_axi_wready;
    end
end
assign o_axi_wuser = r_cmd_user;

// AXI write response channel
assign o_axi_bready = i_user_bready;
assign o_user_bvalid = i_axi_bvalid && r_last_split;
assign o_user_bresp = i_axi_bresp;
assign o_user_bid = i_axi_bid;

// User command interface
assign o_user_cmd_ready = (r_state == ST_IDLE) && w_can_accept;

// Error and status outputs
assign o_error_type = r_error_type;
assign o_error_count = r_error_count;
assign o_error_addr = r_error_addr;
assign o_trans_count = r_trans_count;
assign o_timeout_count = r_timeout_count;

endmodule : axi_master_split_xfer_wr
