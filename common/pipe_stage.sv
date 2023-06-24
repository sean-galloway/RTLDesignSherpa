mple Valid-Ready handshake is acting like a one depth FIFO. There is code from one of my repo:

`timescale 1ns / 1ps // Timescale for following modules

module pipe_stage
(
    clk, rst,
    wdata, wvalid, wready,
    rdata, rvalid, rready
);

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Parameters declaration
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    parameter DATA_WIDTH = 8; // The width of the write data bus and the read data bus

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Ports declaration
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Simple valid-ready streaming protocol that is optimized for minimal power consumption and reduced interface   //
    // complexity. Use it to connect modules that require the high performance. This protocol samples transactions   //
    // on the rising edge of the clock, to simplify the integration into any design flow.                            //
    ///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //----------------------------------------------------------------------------------------------------------------+
    input                       clk   ; // Clock - Transactions are sampled on the rising edge of the clock.          |
    //----------------------------------------------------------------------------------------------------------------+
    input                       rst   ; // Reset - The reset signal is asynchronous active LOW.                       |
    //----------------------------------------------------------------------------------------------------------------+
    input  [DATA_WIDTH - 1 : 0] wdata ; // Write data - The data is written on the rising edge of the clock when      |
                                        // write valid and write ready are both active HIGH. The width of the write   |
                                        // data bus depends on the DATA_WIDTH parameter.                              |
    //----------------------------------------------------------------------------------------------------------------+
    input                       wvalid; // Write valid - Indicates that the write data signal is valid. The write     |
                                        // valid signal is active HIGH.                                               |
    //----------------------------------------------------------------------------------------------------------------+
    output                      wready; // Write ready - Indicates that the write data can be accepted. The write     |
                                        // ready signal is active HIGH.                                               |
    //----------------------------------------------------------------------------------------------------------------+
    output [DATA_WIDTH - 1 : 0] rdata ; // Read data - The data is read on the rising edge of the clock when read     |
                                        // valid and read ready are both active HIGH. The width of the read data bus  |
                                        // depends on the DATA_WIDTH parameter.                                       |
    //----------------------------------------------------------------------------------------------------------------+
    output                      rvalid; // Read valid - Indicates that the read data signal is valid. The read valid  |
                                        // signal is active HIGH.                                                     |
    //----------------------------------------------------------------------------------------------------------------+
    input                       rready; // Read ready - Indicates that the read data can be accepted. The read ready  |
                                        // signal is active HIGH.                                                     |
    //----------------------------------------------------------------------------------------------------------------+

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Port signals declaration
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    wire                      sig_rst;    // rst signal
    wire [DATA_WIDTH - 1 : 0] sig_wdata;  // wdata signal
    wire                      sig_wvalid; // wvalid signal
    wire                      sig_wready; // wready signal
    wire [DATA_WIDTH - 1 : 0] sig_rdata;  // rdata signal
    wire                      sig_rvalid; // rvalid signal
    wire                      sig_rready; // rready signal

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Port signals rewriting
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    assign sig_rst    =     rst;    // rst rewriting
    assign sig_wdata  =     wdata;  // wdata rewriting
    assign sig_wvalid =     wvalid; // wvalid rewriting
    assign     wready = sig_wready; // wready rewriting
    assign     rdata  = sig_rdata;  // rdata rewriting
    assign     rvalid = sig_rvalid; // rvalid rewriting
    assign sig_rready =     rready; // rready rewriting

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Internal signals declaration
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    reg  [DATA_WIDTH - 1 : 0] reg_data;       // Data in PIPE_REG
    reg                       reg_data_valid; // Data in PIPE_REG is valid
    wire                      sig_empty;      // PIPE_REG is empty
    wire                      sig_read;       // Write on the rising edge of the clock
    wire                      sig_write;      // Read on the rising edge of the clock

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Write data
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    assign sig_empty  = ~reg_data_valid;         // PIPE_REG is empty
    assign sig_wready = sig_rready | sig_empty;  // Write ready
    assign sig_write  = sig_wvalid & sig_wready; // Write on the rising edge of the clock

    always @(posedge clk or negedge sig_rst) begin : lab_write_data
        if (~sig_rst)
            reg_data <= {DATA_WIDTH{1'b 0}};
        else begin
            if (sig_write)
                reg_data <= sig_wdata;
        end
    end // lab_write_data

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Data valid
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    always @(posedge clk or negedge sig_rst) begin : lab_data_valid
        if (~sig_rst)
            reg_data_valid <= 1'b 0;
        else begin
            if (sig_write & ~sig_read)
                reg_data_valid <= 1'b 1;
            else if (~sig_write & sig_read)
                reg_data_valid <= 1'b 0;
            else
                reg_data_valid <= reg_data_valid;
        end
    end // lab_data_valid

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Read data
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    assign sig_rvalid = reg_data_valid;          // Read valid
    assign sig_read   = sig_rvalid & sig_rready; // Read on the rising edge of the clock
    assign sig_rdata  = reg_data;                // Read data

endmodule