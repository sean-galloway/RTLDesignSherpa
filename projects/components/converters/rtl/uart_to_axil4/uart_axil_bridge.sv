// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: uart_axil_bridge
// Purpose: UART to AXI4-Lite Master Bridge
//
// Parses UART commands and executes AXI4-Lite transactions with timing isolation
//
// Command Protocol:
//   Write: W <addr_hex> <data_hex>\n  -> Response: "OK\n"
//   Read:  R <addr_hex>\n             -> Response: "0xDEADBEEF\n"

`timescale 1ns / 1ps

`include "reset_defs.svh"

module uart_axil_bridge #(
    parameter int AXIL_ADDR_WIDTH = 32,
    parameter int AXIL_DATA_WIDTH = 32,
    parameter int CLKS_PER_BIT    = 868,  // 100MHz / 115200 baud
    parameter int SKID_DEPTH_AR   = 2,
    parameter int SKID_DEPTH_R    = 4,
    parameter int SKID_DEPTH_AW   = 2,
    parameter int SKID_DEPTH_W    = 4,
    parameter int SKID_DEPTH_B    = 2
)(
    input  logic                         aclk,
    input  logic                         aresetn,

    // UART interface
    input  logic                         i_uart_rx,
    output logic                         o_uart_tx,

    // AXI4-Lite Master interface (with timing isolation)
    output logic [AXIL_ADDR_WIDTH-1:0]   m_axil_awaddr,
    output logic [2:0]                   m_axil_awprot,
    output logic                         m_axil_awvalid,
    input  logic                         m_axil_awready,

    output logic [AXIL_DATA_WIDTH-1:0]   m_axil_wdata,
    output logic [AXIL_DATA_WIDTH/8-1:0] m_axil_wstrb,
    output logic                         m_axil_wvalid,
    input  logic                         m_axil_wready,

    input  logic [1:0]                   m_axil_bresp,
    input  logic                         m_axil_bvalid,
    output logic                         m_axil_bready,

    output logic [AXIL_ADDR_WIDTH-1:0]   m_axil_araddr,
    output logic [2:0]                   m_axil_arprot,
    output logic                         m_axil_arvalid,
    input  logic                         m_axil_arready,

    input  logic [AXIL_DATA_WIDTH-1:0]   m_axil_rdata,
    input  logic [1:0]                   m_axil_rresp,
    input  logic                         m_axil_rvalid,
    output logic                         m_axil_rready
);

    // UART signals
    logic [7:0] w_rx_data, w_tx_data;
    logic       w_rx_valid, w_rx_ready;
    logic       w_tx_valid, w_tx_ready;

    // Internal AXI4-Lite signals (before timing isolation)
    logic [AXIL_ADDR_WIDTH-1:0]   w_fub_awaddr;
    logic [2:0]                   w_fub_awprot;
    logic                         w_fub_awvalid;
    logic                         w_fub_awready;

    logic [AXIL_DATA_WIDTH-1:0]   w_fub_wdata;
    logic [AXIL_DATA_WIDTH/8-1:0] w_fub_wstrb;
    logic                         w_fub_wvalid;
    logic                         w_fub_wready;

    logic [1:0]                   w_fub_bresp;
    logic                         w_fub_bvalid;
    logic                         w_fub_bready;

    logic [AXIL_ADDR_WIDTH-1:0]   w_fub_araddr;
    logic [2:0]                   w_fub_arprot;
    logic                         w_fub_arvalid;
    logic                         w_fub_arready;

    logic [AXIL_DATA_WIDTH-1:0]   w_fub_rdata;
    logic [1:0]                   w_fub_rresp;
    logic                         w_fub_rvalid;
    logic                         w_fub_rready;

    // UART RX instance
    uart_rx #(
        .CLKS_PER_BIT(CLKS_PER_BIT)
    ) u_uart_rx (
        .i_clk      (aclk),
        .i_rst_n    (aresetn),
        .i_rx       (i_uart_rx),
        .o_rx_data  (w_rx_data),
        .o_rx_valid (w_rx_valid),
        .i_rx_ready (w_rx_ready)
    );

    // UART TX instance
    uart_tx #(
        .CLKS_PER_BIT(CLKS_PER_BIT)
    ) u_uart_tx (
        .i_clk      (aclk),
        .i_rst_n    (aresetn),
        .o_tx       (o_uart_tx),
        .i_tx_data  (w_tx_data),
        .i_tx_valid (w_tx_valid),
        .o_tx_ready (w_tx_ready)
    );

    // Command parser state machine
    typedef enum logic [3:0] {
        CMD_IDLE,
        CMD_READ_CMD,
        CMD_READ_ADDR,
        CMD_READ_DATA,
        CMD_EXECUTE,
        CMD_AXIL_WRITE_ADDR,
        CMD_AXIL_WRITE_DATA,
        CMD_AXIL_WRITE_RESP,
        CMD_AXIL_READ_ADDR,
        CMD_AXIL_READ_DATA,
        CMD_SEND_RESPONSE
    } cmd_state_t;

    cmd_state_t r_cmd_state, w_cmd_state_next;

    // Calculate maximum hex digits needed for address and data
    localparam int ADDR_HEX_DIGITS = (AXIL_ADDR_WIDTH + 3) / 4;  // Round up to nibbles
    localparam int DATA_HEX_DIGITS = (AXIL_DATA_WIDTH + 3) / 4;  // Round up to nibbles
    localparam int MAX_RESPONSE_LEN = 2 + DATA_HEX_DIGITS + 1;   // "0x" + hex digits + "\n"
    localparam int RESPONSE_INDEX_WIDTH = $clog2(MAX_RESPONSE_LEN + 1);  // Width for index

    // Command buffer (parameterized for data width)
    logic [7:0]  r_cmd_type;
    logic [31:0] r_cmd_addr;  // Address stays 32-bit (adequate for most systems)
    logic [AXIL_DATA_WIDTH-1:0] r_cmd_data;  // Data width parameterized
    logic [AXIL_DATA_WIDTH-1:0] r_resp_data; // Response data parameterized
    logic [4:0]  r_nibble_count;  // Increased to handle 64-bit (16 nibbles)
    logic [7:0]  r_response_buffer [MAX_RESPONSE_LEN-1:0];  // Dynamic response size
    logic [RESPONSE_INDEX_WIDTH-1:0]  r_response_index;  // Parameterized index width
    logic [RESPONSE_INDEX_WIDTH-1:0]  r_response_length; // Parameterized length width

    // Helper function to convert hex char to value
    function automatic logic [3:0] hex_to_val(input logic [7:0] c);
        logic [7:0] temp;
        if (c >= "0" && c <= "9") begin
            temp = c - 8'd48;  // '0' = 48
            return temp[3:0];
        end else if (c >= "a" && c <= "f") begin
            temp = c - 8'd87;  // 'a' - 10 = 97 - 10 = 87
            return temp[3:0];
        end else if (c >= "A" && c <= "F") begin
            temp = c - 8'd55;  // 'A' - 10 = 65 - 10 = 55
            return temp[3:0];
        end else begin
            return 4'h0;
        end
    endfunction

    // Helper function to convert value to hex char
    function automatic logic [7:0] val_to_hex(input logic [3:0] v);
        logic [7:0] v_extended;
        v_extended = 8'(v);
        if (v < 4'd10)
            return 8'd48 + v_extended;  // '0' = 48
        else
            return 8'd55 + v_extended;  // 'A' - 10 = 65 - 10 = 55
    endfunction

    // State machine registers
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_cmd_state <= CMD_IDLE;
            r_cmd_type <= '0;
            r_cmd_addr <= '0;
            r_cmd_data <= AXIL_DATA_WIDTH'('0);  // Explicitly sized for parameterization
            r_resp_data <= AXIL_DATA_WIDTH'('0); // Explicitly sized for parameterization
            r_nibble_count <= '0;
            r_response_index <= '0;
            r_response_length <= '0;
        end else begin
            r_cmd_state <= w_cmd_state_next;

            case (r_cmd_state)
                CMD_IDLE: begin
                    if (w_rx_valid && w_rx_ready) begin
                        r_cmd_type <= w_rx_data;
                        r_nibble_count <= '0;
                        r_cmd_addr <= '0;
                        r_cmd_data <= AXIL_DATA_WIDTH'('0);  // Explicitly sized
                    end
                end

                CMD_READ_ADDR: begin
                    if (w_rx_valid && w_rx_ready) begin
                        if (w_rx_data != " " && w_rx_data != "\n" && w_rx_data != "\r") begin
                            r_cmd_addr <= {r_cmd_addr[AXIL_ADDR_WIDTH-5:0], hex_to_val(w_rx_data)};
                            r_nibble_count <= r_nibble_count + 1'b1;
                        end
                    end
                end

                CMD_READ_DATA: begin
                    if (w_rx_valid && w_rx_ready) begin
                        if (w_rx_data != " " && w_rx_data != "\n" && w_rx_data != "\r") begin
                            r_cmd_data <= {r_cmd_data[AXIL_DATA_WIDTH-5:0], hex_to_val(w_rx_data)};
                            r_nibble_count <= r_nibble_count + 1'b1;
                        end
                    end
                end

                CMD_AXIL_READ_DATA: begin
                    if (w_fub_rvalid && w_fub_rready) begin
                        r_resp_data <= w_fub_rdata;
                        // Prepare response: "0x<DATA_HEX_DIGITS>\n"
                        // Dynamic formatting based on AXIL_DATA_WIDTH
                        r_response_buffer[0] <= "0";
                        r_response_buffer[1] <= "x";
                        // Generate hex digits from MSB to LSB
                        for (int i = 0; i < DATA_HEX_DIGITS; i++) begin
                            r_response_buffer[2 + i] <= val_to_hex(
                                w_fub_rdata[(AXIL_DATA_WIDTH - 1) - (i * 4) -: 4]
                            );
                        end
                        r_response_buffer[2 + DATA_HEX_DIGITS] <= "\n";
                        r_response_index <= '0;
                        r_response_length <= RESPONSE_INDEX_WIDTH'(2 + DATA_HEX_DIGITS + 1);  // "0x" + digits + "\n"
                    end
                end

                CMD_AXIL_WRITE_RESP: begin
                    if (w_fub_bvalid && w_fub_bready) begin
                        // Prepare "OK\n" response
                        r_response_buffer[0] <= "O";
                        r_response_buffer[1] <= "K";
                        r_response_buffer[2] <= "\n";
                        r_response_index <= '0;
                        r_response_length <= RESPONSE_INDEX_WIDTH'(3);  // "OK\n"
                    end
                end

                CMD_SEND_RESPONSE: begin
                    if (w_tx_valid && w_tx_ready) begin
                        r_response_index <= r_response_index + 1'b1;
                    end
                end

                default: begin
                    // Maintain values
                end
            endcase
        end
    )

    // State machine transitions
    always_comb begin
        w_cmd_state_next = r_cmd_state;

        case (r_cmd_state)
            CMD_IDLE: begin
                if (w_rx_valid && w_rx_ready) begin
                    if (w_rx_data == "W" || w_rx_data == "w")
                        w_cmd_state_next = CMD_READ_ADDR;
                    else if (w_rx_data == "R" || w_rx_data == "r")
                        w_cmd_state_next = CMD_READ_ADDR;
                end
            end

            CMD_READ_ADDR: begin
                if (w_rx_valid && w_rx_ready) begin
                    if (w_rx_data == " ") begin
                        // Only transition if we've accumulated nibbles (skip leading whitespace)
                        if (r_nibble_count > 0) begin
                            if (r_cmd_type == "W" || r_cmd_type == "w")
                                w_cmd_state_next = CMD_READ_DATA;
                            else
                                w_cmd_state_next = CMD_EXECUTE;
                        end
                        // else: stay in CMD_READ_ADDR, skip whitespace
                    end else if (w_rx_data == "\n" || w_rx_data == "\r") begin
                        w_cmd_state_next = CMD_EXECUTE;
                    end
                end
            end

            CMD_READ_DATA: begin
                if (w_rx_valid && w_rx_ready) begin
                    if (w_rx_data == " ") begin
                        // Skip spaces between address and data (already transitioned)
                    end else if (w_rx_data == "\n" || w_rx_data == "\r") begin
                        w_cmd_state_next = CMD_EXECUTE;
                    end
                end
            end

            CMD_EXECUTE: begin
                if (r_cmd_type == "W" || r_cmd_type == "w")
                    w_cmd_state_next = CMD_AXIL_WRITE_ADDR;
                else if (r_cmd_type == "R" || r_cmd_type == "r")
                    w_cmd_state_next = CMD_AXIL_READ_ADDR;
                else
                    w_cmd_state_next = CMD_IDLE;
            end

            CMD_AXIL_WRITE_ADDR: begin
                if (w_fub_awvalid && w_fub_awready)
                    w_cmd_state_next = CMD_AXIL_WRITE_DATA;
            end

            CMD_AXIL_WRITE_DATA: begin
                if (w_fub_wvalid && w_fub_wready)
                    w_cmd_state_next = CMD_AXIL_WRITE_RESP;
            end

            CMD_AXIL_WRITE_RESP: begin
                if (w_fub_bvalid && w_fub_bready)
                    w_cmd_state_next = CMD_SEND_RESPONSE;
            end

            CMD_AXIL_READ_ADDR: begin
                if (w_fub_arvalid && w_fub_arready)
                    w_cmd_state_next = CMD_AXIL_READ_DATA;
            end

            CMD_AXIL_READ_DATA: begin
                if (w_fub_rvalid && w_fub_rready)
                    w_cmd_state_next = CMD_SEND_RESPONSE;
            end

            CMD_SEND_RESPONSE: begin
                if (w_tx_valid && w_tx_ready) begin
                    if (r_response_index >= (r_response_length - 1))
                        w_cmd_state_next = CMD_IDLE;
                end
            end

            default: w_cmd_state_next = CMD_IDLE;
        endcase
    end

    // Output assignments
    assign w_rx_ready = (r_cmd_state == CMD_IDLE) ||
                        (r_cmd_state == CMD_READ_ADDR) ||
                        (r_cmd_state == CMD_READ_DATA);

    assign w_tx_valid = (r_cmd_state == CMD_SEND_RESPONSE);
    assign w_tx_data = r_response_buffer[r_response_index];

    // Internal AXI4-Lite signal assignments (to timing isolation modules)
    // Write path
    assign w_fub_awaddr  = r_cmd_addr[AXIL_ADDR_WIDTH-1:0];
    assign w_fub_awprot  = 3'b000;  // Unprivileged, secure, data access
    assign w_fub_awvalid = (r_cmd_state == CMD_AXIL_WRITE_ADDR);

    assign w_fub_wdata  = r_cmd_data[AXIL_DATA_WIDTH-1:0];
    assign w_fub_wstrb  = {(AXIL_DATA_WIDTH/8){1'b1}};  // All bytes valid
    assign w_fub_wvalid = (r_cmd_state == CMD_AXIL_WRITE_DATA);

    assign w_fub_bready = (r_cmd_state == CMD_AXIL_WRITE_RESP);

    // Read path
    assign w_fub_araddr  = r_cmd_addr[AXIL_ADDR_WIDTH-1:0];
    assign w_fub_arprot  = 3'b000;  // Unprivileged, secure, data access
    assign w_fub_arvalid = (r_cmd_state == CMD_AXIL_READ_ADDR);

    assign w_fub_rready = (r_cmd_state == CMD_AXIL_READ_DATA);

    // AXI4-Lite Write Timing Isolation
    axil4_master_wr #(
        .AXIL_ADDR_WIDTH (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH (AXIL_DATA_WIDTH),
        .SKID_DEPTH_AW   (SKID_DEPTH_AW),
        .SKID_DEPTH_W    (SKID_DEPTH_W),
        .SKID_DEPTH_B    (SKID_DEPTH_B)
    ) u_axil_wr_timing (
        .aclk    (aclk),
        .aresetn (aresetn),

        // FUB side (from command parser)
        .fub_awaddr  (w_fub_awaddr),
        .fub_awprot  (w_fub_awprot),
        .fub_awvalid (w_fub_awvalid),
        .fub_awready (w_fub_awready),

        .fub_wdata  (w_fub_wdata),
        .fub_wstrb  (w_fub_wstrb),
        .fub_wvalid (w_fub_wvalid),
        .fub_wready (w_fub_wready),

        .fub_bresp  (w_fub_bresp),
        .fub_bvalid (w_fub_bvalid),
        .fub_bready (w_fub_bready),

        // Master side (external AXI4-Lite bus)
        .m_axil_awaddr  (m_axil_awaddr),
        .m_axil_awprot  (m_axil_awprot),
        .m_axil_awvalid (m_axil_awvalid),
        .m_axil_awready (m_axil_awready),

        .m_axil_wdata  (m_axil_wdata),
        .m_axil_wstrb  (m_axil_wstrb),
        .m_axil_wvalid (m_axil_wvalid),
        .m_axil_wready (m_axil_wready),

        .m_axil_bresp  (m_axil_bresp),
        .m_axil_bvalid (m_axil_bvalid),
        .m_axil_bready (m_axil_bready),

        .busy ()
    );

    // AXI4-Lite Read Timing Isolation
    axil4_master_rd #(
        .AXIL_ADDR_WIDTH (AXIL_ADDR_WIDTH),
        .AXIL_DATA_WIDTH (AXIL_DATA_WIDTH),
        .SKID_DEPTH_AR   (SKID_DEPTH_AR),
        .SKID_DEPTH_R    (SKID_DEPTH_R)
    ) u_axil_rd_timing (
        .aclk    (aclk),
        .aresetn (aresetn),

        // FUB side (from command parser)
        .fub_araddr  (w_fub_araddr),
        .fub_arprot  (w_fub_arprot),
        .fub_arvalid (w_fub_arvalid),
        .fub_arready (w_fub_arready),

        .fub_rdata  (w_fub_rdata),
        .fub_rresp  (w_fub_rresp),
        .fub_rvalid (w_fub_rvalid),
        .fub_rready (w_fub_rready),

        // Master side (external AXI4-Lite bus)
        .m_axil_araddr  (m_axil_araddr),
        .m_axil_arprot  (m_axil_arprot),
        .m_axil_arvalid (m_axil_arvalid),
        .m_axil_arready (m_axil_arready),

        .m_axil_rdata  (m_axil_rdata),
        .m_axil_rresp  (m_axil_rresp),
        .m_axil_rvalid (m_axil_rvalid),
        .m_axil_rready (m_axil_rready),

        .busy ()
    );

endmodule : uart_axil_bridge
