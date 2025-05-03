`timescale 1ns / 1ps

// Import packages
import axi_pkg::*;
import amba_error_pkg::*;

module axi_master_split_xfer_rd #(
    parameter int MAX_OUTSTANDING    = 8,     // Maximum outstanding transactions
    parameter int AXI_ADDR_WIDTH     = 32,    // Address width
    parameter int AXI_DATA_WIDTH     = 64,    // AXI side data width
    parameter int USER_DATA_WIDTH    = 32,    // User side data width
    // Short params and calculations
    parameter int MO       = MAX_OUTSTANDING,
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int UDW      = USER_DATA_WIDTH,
    // Derived parameters for width conversion
    parameter int AXI_STRB_WIDTH  = DW/8,
    parameter int USER_STRB_WIDTH = UDW/8,
    parameter int WIDTH_RATIO     = DW > UDW ? DW/UDW : UDW/DW,
    parameter int LOG2_WR         = $clog2(WIDTH_RATIO),
    parameter int LOG2_MO         = $clog2(MO+1)
) (
    input  logic                      i_clk,
    input  logic                      i_rst_n,

    // User command interface
    input  logic                      i_user_cmd_valid,
    output logic                      o_user_cmd_ready,
    input  logic [AW-1:0]             i_user_cmd_addr,
    input  logic [7:0]                i_user_cmd_len,
    input  logic [2:0]                i_user_cmd_size,
    input  logic [1:0]                i_user_cmd_burst,
    input  logic [3:0]                i_user_cmd_id,
    input  logic                      i_user_cmd_lock,
    input  logic [3:0]                i_user_cmd_cache,
    input  logic [2:0]                i_user_cmd_prot,
    input  logic [3:0]                i_user_cmd_qos,
    input  logic [3:0]                i_user_cmd_region,
    input  logic [AXI_USER_WIDTH-1:0] i_user_cmd_user,
    input  logic [11:0]               i_alignment_boundary,

    // User read data interface
    output logic [UDW-1:0]           o_user_rdata,
    output logic                     o_user_rvalid,
    input  logic                     i_user_rready,
    output logic                     o_user_rlast,

    // AXI read address channel
    output logic                     o_axi_arvalid,
    input  logic                     i_axi_arready,
    output logic [AW-1:0]            o_axi_araddr,
    output logic [7:0]               o_axi_arlen,
    output logic [2:0]               o_axi_arsize,
    output logic [1:0]               o_axi_arburst,
    output logic [3:0]               o_axi_arid,
    output logic                     o_axi_arlock,
    output logic [3:0]               o_axi_arcache,
    output logic [2:0]               o_axi_arprot,
    output logic [3:0]               o_axi_arqos,
    output logic [3:0]               o_axi_arregion,
    output logic [AXI_USER_WIDTH-1:0] o_axi_aruser,

    // AXI read data channel
    input  logic [DW-1:0]             i_axi_rdata,
    input  logic                      i_axi_rvalid,
    output logic                      o_axi_rready,
    input  logic                      i_axi_rlast,
    input  logic [1:0]                i_axi_rresp,
    input  logic [3:0]                i_axi_rid,
    input  logic [AXI_USER_WIDTH-1:0] i_axi_ruser,

    // Error and status interface
    output error_type_t               o_error_type,
    output logic [31:0]               o_error_count,
    output logic [31:0]               o_error_addr,
    output logic [31:0]               o_trans_count,
    output logic [31:0]               o_timeout_count
);

// State machine encoding
typedef enum logic [4:0] {
    ST_IDLE     = 5'b00001,
    ST_CALC     = 5'b00010,
    ST_ADDR     = 5'b00100,
    ST_DATA     = 5'b01000,
    ST_ERROR    = 5'b10000
} state_t;

// Transfer control registers
state_t              r_state;
logic [AW-1:0]       r_curr_addr;
logic [AW-1:0]       r_boundary_addr;
logic [7:0]          r_total_len;
logic [7:0]          r_current_len;
logic [7:0]          r_beats_remaining;
logic [2:0]          r_size;
logic [1:0]          r_burst;
logic                r_last_split;
logic [AW-1:0]       r_alignment_mask;

// Data conversion control registers
logic [DW-1:0]       r_data_buffer;          // Buffer for width conversion
logic [LOG2_WR-1:0]  r_data_count;           // Counter for data beats in conversion
logic [LOG2_WR-1:0]  r_beats_per_conv;       // Number of beats needed for conversion
logic                r_conv_in_progress;     // Conversion in progress flag
logic [2:0]          r_user_byte_offset;     // Byte offset for unaligned transfers
logic [7:0]          r_adjusted_len;         // Length adjusted for width conversion

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
localparam int       TimeoutLimit = 1000;

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
logic [2:0]         w_byte_offset;

// Conversion mode detection
assign w_is_upsizing = UDW > DW;
assign w_is_downsizing = DW > UDW;

// Calculate required beats for width conversion
assign w_required_beats = w_is_upsizing ? WIDTH_RATIO : 1;

// Validation signals
assign w_valid_burst_type = (r_burst inside {BURST_TYPE_FIXED, BURST_TYPE_INCR, BURST_TYPE_WRAP});
assign w_valid_burst_length = (r_total_len < AXI_MAX_BURST_LENGTH);
assign w_can_accept = (r_outstanding_count < MO);
// Width conversion control
always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
        r_data_buffer <= '0;
        r_data_count <= '0;
        r_conv_in_progress <= 1'b0;
        r_beats_per_conv <= '0;
        r_user_byte_offset <= '0;
    end else begin
        if (r_state == ST_IDLE) begin
            // Calculate conversion parameters on new command
            if (i_user_cmd_valid && w_can_accept) begin
                r_beats_per_conv <= w_required_beats;
                r_user_byte_offset <= i_user_cmd_addr[2:0];
                r_conv_in_progress <= 1'b0;
                r_data_count <= '0;
            end
        end else if (r_state == ST_DATA) begin
            if (i_axi_rvalid && o_axi_rready) begin
                if (w_is_upsizing) begin
                    // For upsizing: buffer narrow data until we have enough for one wide transfer
                    r_data_buffer <= i_axi_rdata;
                    r_data_count <= r_data_count + 1;
                    r_conv_in_progress <= 1'b1;
                end else if (w_is_downsizing) begin
                    // For downsizing: store wide data and serve it in portions
                    r_data_buffer <= i_axi_rdata;
                    r_conv_in_progress <= 1'b1;
                end
            end else if (i_user_rready && o_user_rvalid) begin
                if (w_width_conversion_done) begin
                    r_conv_in_progress <= 1'b0;
                    r_data_count <= '0;
                end else if (w_is_downsizing) begin
                    // For downsizing: increment position in buffer
                    r_data_count <= r_data_count + 1;
                end
            end
        end
    end
end

// Width conversion completion check
assign w_width_conversion_done = w_is_upsizing ?
                                (r_data_count == r_beats_per_conv - 1) :
                                (w_is_downsizing ? (r_data_count == WIDTH_RATIO - 1) : 1'b1);

// Calculate adjusted length for AXI transactions based on width conversion
always_comb begin
    if (w_is_upsizing)
        r_adjusted_len = {1'b0, i_user_cmd_len} >> LOG2_WR;
    else if (w_is_downsizing)
        r_adjusted_len = {i_user_cmd_len, {LOG2_WR{1'b0}}} + WIDTH_RATIO - 1;
    else
        r_adjusted_len = i_user_cmd_len;
end

// Boundary crossing calculation with width conversion consideration
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
                if (o_axi_arvalid && i_axi_arready) begin
                    r_state <= ST_DATA;
                    r_curr_addr <= r_boundary_addr;
                    r_outstanding_count <= r_outstanding_count + 1;
                end
            end

            ST_DATA: begin
                if (i_axi_rvalid && o_axi_rready && i_axi_rlast) begin
                    r_outstanding_count <= r_outstanding_count - 1;
                    if (i_axi_rresp != RESP_OKAY)
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
        if (r_state == ST_DATA)
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
        end else if (r_timeout_counter >= TimeoutLimit) begin
            r_error_type <= ERR_TIMEOUT;
            r_error_addr <= r_curr_addr;
            r_error_count <= r_error_count + 1;
        end else if (r_state == ST_DATA && i_axi_rvalid && i_axi_rresp != RESP_OKAY) begin
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
        if (o_axi_arvalid && i_axi_arready)
            r_trans_count <= r_trans_count + 1;

        // Count timeouts
        if (r_timeout_counter >= TimeoutLimit)
            r_timeout_count <= r_timeout_count + 1;
    end
end

// Data output multiplexing based on conversion mode
always_comb begin
    if (w_is_downsizing) begin
        // Select the appropriate portion of the wide data
        o_user_rdata = r_data_buffer[r_data_count * UDW +: UDW];
        o_user_rvalid = i_axi_rvalid && r_conv_in_progress;
        o_user_rlast = i_axi_rlast && (r_data_count == WIDTH_RATIO - 1) && r_last_split;
    end else if (w_is_upsizing) begin
        // Combine multiple narrow beats into one wide beat
        o_user_rdata = r_data_buffer;
        o_user_rvalid = r_conv_in_progress && w_width_conversion_done;
        o_user_rlast = i_axi_rlast && r_last_split && w_width_conversion_done;
    end else begin
        // Direct passthrough when widths match
        o_user_rdata = i_axi_rdata;
        o_user_rvalid = i_axi_rvalid;
        o_user_rlast = i_axi_rlast && r_last_split;
    end
end

// AXI read control
assign o_axi_arvalid = (r_state == ST_ADDR);
assign o_axi_araddr = r_curr_addr;
assign o_axi_arlen = r_current_len;
assign o_axi_arsize = r_size;
assign o_axi_arburst = r_burst;
assign o_axi_arid = r_cmd_id;
assign o_axi_arlock = r_cmd_lock;
assign o_axi_arcache = r_cmd_cache;
assign o_axi_arprot = r_cmd_prot;
assign o_axi_arqos = r_cmd_qos;
assign o_axi_arregion = r_cmd_region;
assign o_axi_aruser = r_cmd_user;

// AXI ready signal based on conversion mode
assign o_axi_rready = w_is_downsizing ? !r_conv_in_progress :
                        w_is_upsizing ? (r_data_count != WIDTH_RATIO - 1) :
                        i_user_rready;

// User command interface
assign o_user_cmd_ready = (r_state == ST_IDLE) && w_can_accept;

// Error and status outputs
assign o_error_type = r_error_type;
assign o_error_count = r_error_count;
assign o_error_addr = r_error_addr;
assign o_trans_count = r_trans_count;
assign o_timeout_count = r_timeout_count;

endmodule : axi_master_split_xfer_rd
