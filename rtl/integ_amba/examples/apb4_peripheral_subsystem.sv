// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_peripheral_subsystem
// Purpose: Apb Peripheral Subsystem module
//
// Documentation: PRD.md
// Subsystem: integ_amba
//
// Author: sean galloway
// Created: 2025-10-18

`timescale 1ns / 1ps

module apb4_peripheral_subsystem
    import monitor_common_pkg::*;   // monitor_packet_t, monbus_timestamp_t
#(
    parameter int ADDR_WIDTH = 16,   // 64KB address space
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = 4,

    // Monitor parameters
    parameter int MAX_TRANSACTIONS = 4,  // Simple peripherals, small value OK
    parameter int UNIT_ID = 0,

    // Agent IDs for each peripheral
    parameter logic [7:0] AGENT_ID_REGFILE = 8'h50,
    parameter logic [7:0] AGENT_ID_TIMER   = 8'h51,
    parameter logic [7:0] AGENT_ID_GPIO    = 8'h52
) (
    input  logic pclk,
    input  logic presetn,

    // =============================================================================
    // Single APB Master Interface (from CPU or bridge)
    // =============================================================================
    input  logic                  apb_psel,
    input  logic                  apb_penable,
    input  logic                  apb_pwrite,
    input  logic [2:0]            apb_pprot,
    input  logic [ADDR_WIDTH-1:0] apb_paddr,
    input  logic [DATA_WIDTH-1:0] apb_pwdata,
    input  logic [STRB_WIDTH-1:0] apb_pstrb,
    output logic                  apb_pready,
    output logic [DATA_WIDTH-1:0] apb_prdata,
    output logic                  apb_pslverr,

    // =============================================================================
    // Aggregated Monitor Output
    // =============================================================================
    output logic                                  monbus_valid,
    input  logic                                  monbus_ready,
    output monitor_common_pkg::monitor_packet_t   monbus_packet,

    // =============================================================================
    // Configuration
    // =============================================================================
    input logic cfg_error_enable,
    input logic cfg_compl_enable
);

    // =============================================================================
    // APB -> cmd/rsp tap (see below, after the peripheral signals are declared)
    // =============================================================================

    // =============================================================================
    // Address Decoding
    // =============================================================================
    // Address map:
    //   0x0000-0x0FFF: Register File (16 × 32-bit registers)
    //   0x1000-0x1FFF: Timer (control, count, compare registers)
    //   0x2000-0x2FFF: GPIO (data, direction, interrupt registers)

    localparam logic [ADDR_WIDTH-1:0] REGFILE_BASE = 16'h0000;
    localparam logic [ADDR_WIDTH-1:0] REGFILE_MASK = 16'hF000;
    localparam logic [ADDR_WIDTH-1:0] TIMER_BASE   = 16'h1000;
    localparam logic [ADDR_WIDTH-1:0] TIMER_MASK   = 16'hF000;
    localparam logic [ADDR_WIDTH-1:0] GPIO_BASE    = 16'h2000;
    localparam logic [ADDR_WIDTH-1:0] GPIO_MASK    = 16'hF000;

    logic sel_regfile, sel_timer, sel_gpio;

    assign sel_regfile = apb_psel && ((apb_paddr & REGFILE_MASK) == REGFILE_BASE);
    assign sel_timer   = apb_psel && ((apb_paddr & TIMER_MASK)   == TIMER_BASE);
    assign sel_gpio    = apb_psel && ((apb_paddr & GPIO_MASK)    == GPIO_BASE);

    // =============================================================================
    // Peripheral Interfaces
    // =============================================================================

    // Register File
    logic                  regfile_psel;
    logic                  regfile_penable;
    logic                  regfile_pwrite;
    logic [ADDR_WIDTH-1:0] regfile_paddr;
    logic [DATA_WIDTH-1:0] regfile_pwdata;
    logic [STRB_WIDTH-1:0] regfile_pstrb;
    logic                  regfile_pready;
    logic [DATA_WIDTH-1:0] regfile_prdata;
    logic                  regfile_pslverr;

    // Timer
    logic                  timer_psel;
    logic                  timer_penable;
    logic                  timer_pwrite;
    logic [ADDR_WIDTH-1:0] timer_paddr;
    logic [DATA_WIDTH-1:0] timer_pwdata;
    logic [STRB_WIDTH-1:0] timer_pstrb;
    logic                  timer_pready;
    logic [DATA_WIDTH-1:0] timer_prdata;
    logic                  timer_pslverr;

    // GPIO
    logic                  gpio_psel;
    logic                  gpio_penable;
    logic                  gpio_pwrite;
    logic [ADDR_WIDTH-1:0] gpio_paddr;
    logic [DATA_WIDTH-1:0] gpio_pwdata;
    logic [STRB_WIDTH-1:0] gpio_pstrb;
    logic                  gpio_pready;
    logic [DATA_WIDTH-1:0] gpio_prdata;
    logic                  gpio_pslverr;

    // Route master signals to selected peripheral
    assign regfile_psel    = sel_regfile;
    assign timer_psel      = sel_timer;
    assign gpio_psel       = sel_gpio;

    assign regfile_penable = apb_penable && sel_regfile;
    assign timer_penable   = apb_penable && sel_timer;
    assign gpio_penable    = apb_penable && sel_gpio;

    assign regfile_pwrite  = apb_pwrite;
    assign timer_pwrite    = apb_pwrite;
    assign gpio_pwrite     = apb_pwrite;

    assign regfile_paddr   = apb_paddr;
    assign timer_paddr     = apb_paddr;
    assign gpio_paddr      = apb_paddr;

    assign regfile_pwdata  = apb_pwdata;
    assign timer_pwdata    = apb_pwdata;
    assign gpio_pwdata     = apb_pwdata;

    assign regfile_pstrb   = apb_pstrb;
    assign timer_pstrb     = apb_pstrb;
    assign gpio_pstrb      = apb_pstrb;

    // Response muxing
    always_comb begin
        apb_pready  = 1'b0;
        apb_prdata  = '0;
        apb_pslverr = 1'b0;

        if (sel_regfile) begin
            apb_pready  = regfile_pready;
            apb_prdata  = regfile_prdata;
            apb_pslverr = regfile_pslverr;
        end else if (sel_timer) begin
            apb_pready  = timer_pready;
            apb_prdata  = timer_prdata;
            apb_pslverr = timer_pslverr;
        end else if (sel_gpio) begin
            apb_pready  = gpio_pready;
            apb_prdata  = gpio_prdata;
            apb_pslverr = gpio_pslverr;
        end else if (apb_psel) begin
            // Decode error - invalid address
            apb_pready  = 1'b1;
            apb_pslverr = 1'b1;
        end
    end

    // =============================================================================
    // Peripheral 1: Register File (Simple APB Slave)
    // =============================================================================
    // 16 × 32-bit registers at 0x0000-0x003C

    logic [15:0][31:0] registers;

    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            registers <= '0;
        end else if (regfile_psel && regfile_penable && regfile_pwrite) begin
            // Write operation
            logic [3:0] reg_addr;
            reg_addr = regfile_paddr[5:2];  // Word-aligned
            if (reg_addr < 16) begin
                for (int i = 0; i < 4; i++) begin
                    if (regfile_pstrb[i]) begin
                        registers[reg_addr][i*8 +: 8] <= regfile_pwdata[i*8 +: 8];
                    end
                end
            end
        end
    end

    assign regfile_pready  = 1'b1;  // Always ready
    assign regfile_prdata  = (regfile_paddr[5:2] < 16) ? registers[regfile_paddr[5:2]] : '0;
    assign regfile_pslverr = 1'b0;  // No errors

    // =============================================================================
    // Peripheral 2: Timer (Stub - for demonstration)
    // =============================================================================

    assign timer_pready  = 1'b1;
    assign timer_prdata  = 32'hDEAD_BEEF;  // Stub data
    assign timer_pslverr = 1'b0;

    // =============================================================================
    // Peripheral 3: GPIO (Stub - for demonstration)
    // =============================================================================

    assign gpio_pready  = 1'b1;
    assign gpio_prdata  = 32'hCAFE_BABE;  // Stub data
    assign gpio_pslverr = 1'b0;

    // =============================================================================
    // APB -> cmd/rsp tap
    // =============================================================================
    // apb4_monitor observes the TRANSLATED side of a bridge, never the wire: it
    // takes a cmd_valid/cmd_ready + rsp_valid/rsp_ready handshake. That is what
    // lets one monitor serve both APB4 and APB5 -- each bridge presents the same
    // shape regardless of the protocol on its pins.
    //
    // This subsystem has raw APB in hand, so it derives the handshake from the
    // bus phases. APB carries one outstanding transaction and completes in the
    // ACCESS phase, so the command and its response are accepted in the same
    // cycle: psel && penable && pready. The tap is pure observation -- nothing
    // is registered and no cycle is added to the peripheral path.

    logic regfile_xfer, timer_xfer, gpio_xfer;
    assign regfile_xfer = regfile_psel && regfile_penable && regfile_pready;
    assign timer_xfer   = timer_psel   && timer_penable   && timer_pready;
    assign gpio_xfer    = gpio_psel    && gpio_penable    && gpio_pready;

    // These peripherals never stall (pready is tied high), so cmd_ready and
    // rsp_ready are constant. A peripheral that can stall would drive them from
    // its own backpressure.
    localparam logic ALWAYS_READY = 1'b1;

    // =============================================================================
    // Monitor Bus Signals (3 monitors: one per peripheral)
    // =============================================================================

    localparam int NUM_MONITORS = 3;

    logic [NUM_MONITORS-1:0]                    mon_valid;
    logic [NUM_MONITORS-1:0]                    mon_ready;
    monitor_common_pkg::monitor_packet_t        mon_packet [NUM_MONITORS];

    // The monitors take a free-running time broadcast for their side-band
    // timestamp. A real system drives this from the monbus_group time source;
    // an example counts locally so the field is at least monotonic.
    monitor_common_pkg::monbus_timestamp_t mon_time;
    always_ff @(posedge pclk or negedge presetn) begin
        if (!presetn) mon_time <= '0;
        else          mon_time <= mon_time + 1'b1;
    end

    // =============================================================================
    // Monitor 0: Register File
    // =============================================================================

    apb4_monitor #(
        .ADDR_WIDTH       (ADDR_WIDTH),
        .DATA_WIDTH       (DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID[7:0]),
        .AGENT_ID         (16'(AGENT_ID_REGFILE))
    ) u_regfile_mon (
        .aclk                     (pclk),
        .aresetn                  (presetn),

        // Command side of the tap
        .cmd_valid                (regfile_xfer),
        .cmd_ready                (ALWAYS_READY),
        .cmd_pwrite               (regfile_pwrite),
        .cmd_paddr                (regfile_paddr),
        .cmd_pwdata               (regfile_pwdata),
        .cmd_pstrb                (regfile_pstrb),
        .cmd_pprot                (apb_pprot),

        // Response side of the tap
        .rsp_valid                (regfile_xfer),
        .rsp_ready                (ALWAYS_READY),
        .rsp_prdata               (regfile_prdata),
        .rsp_pslverr              (regfile_pslverr),

        // Only error and completion reporting are exposed at this level;
        // everything else is off so the example stays readable.
        .cfg_error_enable         (cfg_error_enable),
        .cfg_timeout_enable       (1'b0),
        .cfg_protocol_enable      (1'b0),
        .cfg_slverr_enable        (cfg_error_enable),
        .cfg_perf_enable          (cfg_compl_enable),
        .cfg_latency_enable       (1'b0),
        .cfg_throughput_enable    (1'b0),
        .cfg_debug_enable         (1'b0),
        .cfg_trans_debug_enable   (1'b0),
        .cfg_debug_level          (4'd0),
        .cfg_cmd_timeout_cnt      (16'd0),
        .cfg_rsp_timeout_cnt      (16'd0),
        .cfg_latency_threshold    (32'd0),
        .cfg_throughput_threshold (16'd0),

        // Address-range checking is off (N_ADDR_RANGES defaults to 0)
        .cfg_addr_check_enable    (1'b0),
        .cfg_addr_range_enable    ('0),
        .cfg_addr_range_low       ('0),
        .cfg_addr_range_high      ('0),

        .i_mon_time               (mon_time),

        .monbus_valid             (mon_valid[0]),
        .monbus_ready             (mon_ready[0]),
        .monbus_packet            (mon_packet[0]),
        .monbus_timestamp         (),

        .active_count             (),
        .error_count              (),
        .transaction_count        ()
    );

    // =============================================================================
    // Monitor 1: Timer
    // =============================================================================

    apb4_monitor #(
        .ADDR_WIDTH       (ADDR_WIDTH),
        .DATA_WIDTH       (DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID[7:0]),
        .AGENT_ID         (16'(AGENT_ID_TIMER))
    ) u_timer_mon (
        .aclk                     (pclk),
        .aresetn                  (presetn),

        // Command side of the tap
        .cmd_valid                (timer_xfer),
        .cmd_ready                (ALWAYS_READY),
        .cmd_pwrite               (timer_pwrite),
        .cmd_paddr                (timer_paddr),
        .cmd_pwdata               (timer_pwdata),
        .cmd_pstrb                (timer_pstrb),
        .cmd_pprot                (apb_pprot),

        // Response side of the tap
        .rsp_valid                (timer_xfer),
        .rsp_ready                (ALWAYS_READY),
        .rsp_prdata               (timer_prdata),
        .rsp_pslverr              (timer_pslverr),

        // Only error and completion reporting are exposed at this level;
        // everything else is off so the example stays readable.
        .cfg_error_enable         (cfg_error_enable),
        .cfg_timeout_enable       (1'b0),
        .cfg_protocol_enable      (1'b0),
        .cfg_slverr_enable        (cfg_error_enable),
        .cfg_perf_enable          (cfg_compl_enable),
        .cfg_latency_enable       (1'b0),
        .cfg_throughput_enable    (1'b0),
        .cfg_debug_enable         (1'b0),
        .cfg_trans_debug_enable   (1'b0),
        .cfg_debug_level          (4'd0),
        .cfg_cmd_timeout_cnt      (16'd0),
        .cfg_rsp_timeout_cnt      (16'd0),
        .cfg_latency_threshold    (32'd0),
        .cfg_throughput_threshold (16'd0),

        // Address-range checking is off (N_ADDR_RANGES defaults to 0)
        .cfg_addr_check_enable    (1'b0),
        .cfg_addr_range_enable    ('0),
        .cfg_addr_range_low       ('0),
        .cfg_addr_range_high      ('0),

        .i_mon_time               (mon_time),

        .monbus_valid             (mon_valid[1]),
        .monbus_ready             (mon_ready[1]),
        .monbus_packet            (mon_packet[1]),
        .monbus_timestamp         (),

        .active_count             (),
        .error_count              (),
        .transaction_count        ()
    );

    // =============================================================================
    // Monitor 2: GPIO
    // =============================================================================

    apb4_monitor #(
        .ADDR_WIDTH       (ADDR_WIDTH),
        .DATA_WIDTH       (DATA_WIDTH),
        .MAX_TRANSACTIONS (MAX_TRANSACTIONS),
        .UNIT_ID          (UNIT_ID[7:0]),
        .AGENT_ID         (16'(AGENT_ID_GPIO))
    ) u_gpio_mon (
        .aclk                     (pclk),
        .aresetn                  (presetn),

        // Command side of the tap
        .cmd_valid                (gpio_xfer),
        .cmd_ready                (ALWAYS_READY),
        .cmd_pwrite               (gpio_pwrite),
        .cmd_paddr                (gpio_paddr),
        .cmd_pwdata               (gpio_pwdata),
        .cmd_pstrb                (gpio_pstrb),
        .cmd_pprot                (apb_pprot),

        // Response side of the tap
        .rsp_valid                (gpio_xfer),
        .rsp_ready                (ALWAYS_READY),
        .rsp_prdata               (gpio_prdata),
        .rsp_pslverr              (gpio_pslverr),

        // Only error and completion reporting are exposed at this level;
        // everything else is off so the example stays readable.
        .cfg_error_enable         (cfg_error_enable),
        .cfg_timeout_enable       (1'b0),
        .cfg_protocol_enable      (1'b0),
        .cfg_slverr_enable        (cfg_error_enable),
        .cfg_perf_enable          (cfg_compl_enable),
        .cfg_latency_enable       (1'b0),
        .cfg_throughput_enable    (1'b0),
        .cfg_debug_enable         (1'b0),
        .cfg_trans_debug_enable   (1'b0),
        .cfg_debug_level          (4'd0),
        .cfg_cmd_timeout_cnt      (16'd0),
        .cfg_rsp_timeout_cnt      (16'd0),
        .cfg_latency_threshold    (32'd0),
        .cfg_throughput_threshold (16'd0),

        // Address-range checking is off (N_ADDR_RANGES defaults to 0)
        .cfg_addr_check_enable    (1'b0),
        .cfg_addr_range_enable    ('0),
        .cfg_addr_range_low       ('0),
        .cfg_addr_range_high      ('0),

        .i_mon_time               (mon_time),

        .monbus_valid             (mon_valid[2]),
        .monbus_ready             (mon_ready[2]),
        .monbus_packet            (mon_packet[2]),
        .monbus_timestamp         (),

        .active_count             (),
        .error_count              (),
        .transaction_count        ()
    );

    // =============================================================================
    // Monitor Bus Arbiter (Simple Round-Robin)
    // =============================================================================

    // =============================================================================
    // Monitor bus aggregation
    // =============================================================================
    // Round-robin, not priority: a peripheral that errors continuously must not
    // lock the others out of the bus, or you lose the evidence that would
    // explain it.

    logic [NUM_MONITORS-1:0] mon_grant;
    logic [$clog2(NUM_MONITORS)-1:0] mon_grant_id;

    arbiter_round_robin #(
        .CLIENTS      (NUM_MONITORS),
        .WAIT_GNT_ACK (0)
    ) u_mon_arbiter (
        .clk         (pclk),
        .rst_n       (presetn),
        .block_arb   (~monbus_ready),      // hold the grant while the sink is busy
        .request     (mon_valid),
        .grant_ack   ('0),
        .grant_valid (monbus_valid),
        .grant       (mon_grant),
        .grant_id    (mon_grant_id),
        .last_grant  ()
    );

    // The granted monitor is the one that gets its packet forwarded and its
    // ready asserted; the others stall until their turn.
    always_comb begin
        mon_ready = '0;
        mon_ready[mon_grant_id] = monbus_valid && monbus_ready;
    end

    assign monbus_packet = mon_packet[mon_grant_id];

endmodule : apb4_peripheral_subsystem
