/*
 * GAXI Test DUT
 * Simple test harness for GAXI components with loopback functionality
 * Supports different handshaking modes:
 * - skid: Data is valid with valid signal
 * - fifo_mux: Uses multiplexed data signal (ow_rd_data)
 * - fifo_flop: Data is delayed by one clock cycle after valid
 */

 module gaxi_test_dut #(
    parameter int DATA_WIDTH = 32,
    parameter int CTRL_WIDTH = 8
) (
    input  wire                     clk,
    input  wire                     rst_n,

    // Standard mode signals
    input  wire                     i_wr_valid,
    output wire                     o_wr_ready,
    input  wire [DATA_WIDTH-1:0]    i_wr_data,

    output wire                     o_rd_valid,
    input  wire                     i_rd_ready,
    output wire [DATA_WIDTH-1:0]    o_rd_data,
    output wire [DATA_WIDTH-1:0]    ow_rd_data,  // Multiplexed version for fifo_mux mode

    // Multi-signal mode signals
    input  wire [31:0]              i_wr_addr,
    input  wire [DATA_WIDTH-1:0]    i_wr_data_data,
    input  wire [CTRL_WIDTH-1:0]    i_wr_ctrl,

    output wire [31:0]              o_rd_addr,
    output wire [DATA_WIDTH-1:0]    o_rd_data_data,
    output wire [CTRL_WIDTH-1:0]    o_rd_ctrl,

    // Test mode selection (optional, could be set through parameter instead)
    input  wire [1:0]               test_mode    // 0=skid, 1=fifo_mux, 2=fifo_flop
);

    // Internal registers for skid/fifo_mux mode
    reg [DATA_WIDTH-1:0]    data_reg;
    reg [31:0]              addr_reg;
    reg [CTRL_WIDTH-1:0]    ctrl_reg;
    reg                     valid_reg;

    // Additional registers for fifo_flop mode
    reg [DATA_WIDTH-1:0]    data_flop_reg;
    reg [31:0]              addr_flop_reg;
    reg [CTRL_WIDTH-1:0]    ctrl_flop_reg;

    // Handshake tracking
    reg                     handshake_occurred;

    // Main processing logic
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Reset all registers
            data_reg <= {DATA_WIDTH{1'b0}};
            addr_reg <= 32'h0;
            ctrl_reg <= {CTRL_WIDTH{1'b0}};
            valid_reg <= 1'b0;

            data_flop_reg <= {DATA_WIDTH{1'b0}};
            addr_flop_reg <= 32'h0;
            ctrl_flop_reg <= {CTRL_WIDTH{1'b0}};

            handshake_occurred <= 1'b0;
        end else begin
            // Track handshake for fifo_flop mode
            handshake_occurred <= o_rd_valid && i_rd_ready;

            // Capture data when write handshake occurs
            if (i_wr_valid && o_wr_ready) begin
                // Standard mode data
                data_reg <= i_wr_data;

                // Multi-signal mode data
                addr_reg <= i_wr_addr;
                data_reg <= i_wr_data_data;  // For multi-signal mode
                ctrl_reg <= i_wr_ctrl;

                // Set valid for read
                valid_reg <= 1'b1;
            end else if (o_rd_valid && i_rd_ready) begin
                // Clear valid after read handshake
                valid_reg <= 1'b0;
            end

            // For fifo_flop mode: Capture data in flop registers after handshake
            if (o_rd_valid && i_rd_ready) begin
                data_flop_reg <= data_reg;
                addr_flop_reg <= addr_reg;
                ctrl_flop_reg <= ctrl_reg;
            end
        end
    end

    // Connect outputs
    assign o_wr_ready = 1'b1;  // Always ready to accept data
    assign o_rd_valid = valid_reg;

    // Select output data based on mode
    // In skid mode: Data is valid with valid signal
    // In fifo_mux mode: Use ow_rd_data
    // In fifo_flop mode: Use data_flop_reg when handshake_occurred is true

    // Standard mode outputs
    // For skid mode - data is valid with valid
    // For fifo_flop mode - use flop register one cycle after handshake
    assign o_rd_data = (test_mode == 2 && handshake_occurred) ? data_flop_reg : data_reg;

    // For fifo_mux mode - always use muxed output
    assign ow_rd_data = data_reg;

    // Multi-signal mode outputs
    assign o_rd_addr = (test_mode == 2 && handshake_occurred) ? addr_flop_reg : addr_reg;
    assign o_rd_data_data = (test_mode == 2 && handshake_occurred) ? data_flop_reg : data_reg;
    assign o_rd_ctrl = (test_mode == 2 && handshake_occurred) ? ctrl_flop_reg : ctrl_reg;

endmodule : gaxi_test_dut

