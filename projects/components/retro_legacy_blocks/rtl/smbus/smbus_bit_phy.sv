// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: smbus_bit_phy
// Purpose: Bit-level SMBus/I2C physical layer for the master engine.
// This is the ONLY module that touches SCL and SDA. It executes one primitive
// at a time - START, repeated START, STOP, transmit one bit, receive one bit -
// and reports completion with a single-cycle pulse. The transaction sequencer
// (smbus_core) never sees a clock period; it sees "the bit went out" and "here
// is the bit that came back".
//
//==============================================================================
// OPEN-DRAIN CONTRACT
//==============================================================================
//   SMBus is a wired-AND bus: a device may pull a line LOW or RELEASE it, and
//   may NEVER drive it high. With this port convention (smb_*_o = value,
//   smb_*_t = 1 means released / input) that collapses to one statement:
//
//       smb_scl_o == smb_scl_t   and   smb_sda_o == smb_sda_t
//
//   Driving is only ever driving a 0 and a 1 is always a release, so "actively
//   driving a 1 on an open-drain line" is structurally impossible rather than
//   something a reviewer has to re-check state by state.
//
//==============================================================================
// TIMING
//==============================================================================
//   Everything is counted in BASE UNITS of w_unit_clocks core clocks:
//
//     standard  unit = (cfg_clk_div + 1) / 2,  8 units per SCL period
//     fast      unit = (cfg_clk_div + 1) / 8,  8 units per SCL period
//
//   so the same SMBUS_CLK_DIV that gives 100 kHz in standard mode gives
//   400 kHz in fast mode - and cfg_fast_mode is a TIMING SET, not just a
//   divider, because the phases are not the same fractions in both modes.
//   A symmetric period cannot satisfy fast mode: tLOW >= 1.3 us and
//   tHIGH >= 0.6 us do not both fit in two halves of 2.5 us at the ratio
//   standard mode uses. Fast mode is therefore ASYMMETRIC - the low phase
//   gets 5/8 of the period and the high phase 3/8.
//
//     phase    std  fast   what it is
//     LO_A      2    2     SCL low, data driven          (tSU;DAT)
//     HI_A      2    1     SCL released -> sample point
//     HI_B      2    2     rest of the high phase
//     LO_B      2    3     SCL driven low again
//     HD_STA    4    2     START hold, SDA low -> SCL low
//     SU_STA    4    2     repeated-START setup, SCL high -> SDA low
//     SU_STO    5    5     STOP setup, SCL high -> SDA released
//     BUF       5    5     bus free, and the wait before a START
//
//     tLOW  = LO_B + LO_A     tHIGH = HI_A + HI_B
//
//   ACHIEVED AT THE RDL DEFAULT (cfg_clk_div = 249, 100 MHz core clock),
//   against the SMBus 2.0 / I2C minimums:
//
//     standard, unit = 125 clk = 1250 ns, SCL period 10.00 us (100.0 kHz)
//       tLOW    5000 ns (>= 4700)   tHIGH   5000 ns (>= 4000)
//       tHD;STA 5000 ns (>= 4000)   tSU;STA 5000 ns (>= 4700)
//       tSU;STO 6250 ns (>= 4000)   tBUF    6250 ns (>= 4700)
//
//     fast, unit = 32 clk = 320 ns, SCL period 2.56 us (390.6 kHz)
//       tLOW    1600 ns (>= 1300)   tHIGH    960 ns (>= 600)
//       tHD;STA  640 ns (>= 600)    tSU;STA  640 ns (>= 600)
//       tSU;STO 1600 ns (>= 600)    tBUF    1600 ns (>= 1300)
//
//   Every figure above is a MINIMUM the block meets, not a target it aims
//   at: the units are integers, so the achieved values sit above the spec
//   rather than on it.
//
//   CLOCK STRETCHING. Every phase that RELEASES SCL holds its unit counter at
//   zero until the synchronized SCL input actually reads high, so a slave
//   holding SCL down extends the phase instead of being clocked through. That
//   covers data bits, ACK bits, the repeated START and the STOP alike.
//
//   BUS FREE BEFORE A START. A START waits for SCL and SDA both sampled high,
//   then holds tBUF, before pulling SDA down. A master that pulls SDA low
//   under a low SCL has not generated a START at all - it has put a data bit
//   on someone else's transfer.
//
//==============================================================================
// TIMEOUT AND ABORT
//==============================================================================
//   The timeout counts core clocks for as long as the PHY is STALLED: SCL low
//   on the bus (either this master pulling it down, or the line still reading
//   low after we let go), or a START still waiting for the bus to go free.
//   cfg_timeout == 0 DISABLES the check; it must never mean "expire
//   immediately".
//
//   On expiry the PHY ABANDONS the primitive: it releases both lines, pulses
//   op_done and raises phy_timeout. Releasing is the only thing that is always
//   safe and always possible - a STOP cannot be generated at all while another
//   device is holding SCL down, so the alternative to giving up is hanging
//   forever, which is what this block used to do.
//
//   abort_req starts a STOP from its first phase REGARDLESS of whether a
//   primitive is running, which is the other half of the same problem: op_req
//   is only sampled while idle, so a single-cycle STOP request issued mid-bit
//   used to be dropped silently and left SCL driven low with busy stuck high.
//   The abort's first phase pulls SCL low and leaves SDA UNCHANGED, because
//   moving SDA while SCL is high is a START or a STOP, not an abort.
//
//   BUS RECOVERY (PHY_OP_RECOVER) pulses SCL up to nine times with SDA
//   released, sampling SDA at the end of each high phase and stopping as soon
//   as it reads high, then generates a proper STOP. Each recovery clock is a
//   FULL STANDARD-MODE BIT whatever cfg_fast_mode says - tLOW = LO_B + LO_A
//   and tHIGH = HI_A + HI_B, so 5000 ns each at the default divider, against
//   the 4.7 us / 4.0 us minimums. SCL is driven low a whole phase before SDA
//   moves, never on the same edge.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module smbus_bit_phy (
    input  wire        clk,
    input  wire        rst_n,           // Active-low reset (house convention)

    //--- SMBus lines (open-drain, see contract above)
    input  wire        smb_scl_i,
    output wire        smb_scl_o,
    output wire        smb_scl_t,
    input  wire        smb_sda_i,
    output wire        smb_sda_o,
    output wire        smb_sda_t,

    //--- Configuration
    input  wire [15:0] cfg_clk_div,     // see the timing table above
    input  wire        cfg_fast_mode,   // 400 kHz timing set
    input  wire [23:0] cfg_timeout,     // stall limit in clocks, 0 = off
    input  wire        cfg_soft_reset,  // synchronous return to idle
    input  wire        timeout_ack,     // sequencer has consumed phy_timeout

    //--- Primitive request interface
    input  wire [2:0]  op,              // see PHY_OP_* below
    input  wire        op_req,          // single-cycle request, idle only
    input  wire        abort_req,       // single-cycle, accepted at any time
    input  wire        abort_recover,   // ... and start with bus recovery
    input  wire        tx_bit,          // bit value for PHY_OP_TX
    output wire        op_done,         // single-cycle completion
    output wire        rx_bit,          // bit sampled by PHY_OP_RX
    output wire        phy_busy,

    //--- Bus observation
    output wire        phy_timeout,     // stalled past cfg_timeout
    output wire        recover_failed,  // SDA still low after nine clocks
    output wire        sda_sync,        // synchronized SDA, for the sequencer
    output wire        scl_sync         // synchronized SCL, for the sequencer
);

    //--- Primitive encoding - shared with smbus_core through this header
    localparam logic [2:0] PHY_OP_START   = 3'd0;  // S   (bus free -> held)
    localparam logic [2:0] PHY_OP_RESTART = 3'd1;  // Sr  (SCL low -> SCL low)
    localparam logic [2:0] PHY_OP_STOP    = 3'd2;  // P   (anywhere -> bus free)
    localparam logic [2:0] PHY_OP_TX      = 3'd3;  // one bit out
    localparam logic [2:0] PHY_OP_RX      = 3'd4;  // one bit in
    localparam logic [2:0] PHY_OP_RECOVER = 3'd5;  // bus recovery, then P

    //--- Phase lengths in base units (see the table in the header)
    localparam logic [3:0] U_LO_A_STD   = 4'd2, U_LO_A_FST   = 4'd2;
    localparam logic [3:0] U_HI_A_STD   = 4'd2, U_HI_A_FST   = 4'd1;
    localparam logic [3:0] U_HI_B_STD   = 4'd2, U_HI_B_FST   = 4'd2;
    localparam logic [3:0] U_LO_B_STD   = 4'd2, U_LO_B_FST   = 4'd3;
    localparam logic [3:0] U_HD_STA_STD = 4'd4, U_HD_STA_FST = 4'd2;
    localparam logic [3:0] U_SU_STA_STD = 4'd4, U_SU_STA_FST = 4'd2;
    localparam logic [3:0] U_SU_STO     = 4'd5;
    localparam logic [3:0] U_BUF        = 4'd5;

    // How many stall windows a primitive gets before it is abandoned.
    //
    // A STOP IS DELIBERATELY MORE PATIENT than an ordinary bit. Its whole
    // purpose is to leave the bus correctly, and a slave that is stretching
    // is usually about to finish; a controller that gives up on the STOP
    // after one window strands transactions that were a moment from ending,
    // and leaves every other device on the bus watching a transfer that was
    // never terminated. SMBus's own limits have the same shape - TLOW:SEXT
    // (cumulative slave extend, 25 ms) is well over twice TLOW:MEXT (master,
    // 10 ms) - so one window is the wrong yardstick for waiting on a slave.
    //
    // The counts are "extra windows after the first", so NORMAL = 0 is ONE
    // window and STOP = 3 is FOUR: a 4:1 ratio, not 2.5:1. WORST CASE FROM
    // "SCL WEDGES" TO busy=0 IS FIVE WINDOWS - one for the primitive that
    // stalls, four for the abort's STOP - about 125 ms at the default
    // SMBUS_TIMEOUT. It stays BOUNDED either way: a permanently held SCL ends
    // in release-report-idle, not a hang.
    localparam logic [2:0] WINDOWS_NORMAL = 3'd0;
    localparam logic [2:0] WINDOWS_STOP   = 3'd3;

    //--- Declarations
    logic [1:0]  r_scl_meta;
    logic [1:0]  r_sda_meta;

    logic        r_active;
    logic [2:0]  r_op;
    logic [2:0]  r_phase;
    logic        r_tx_bit;
    logic        r_rx_bit;
    logic        r_done;

    logic [15:0] r_clk_cnt;
    logic [3:0]  r_unit_cnt;

    logic [3:0]  r_recov_cnt;
    logic        r_recov_failed;
    logic        r_scl_drive_low;   // 1 = pull SCL down
    logic        r_sda_drive_low;   // 1 = pull SDA down

    logic [23:0] r_stall_cnt;
    logic [2:0]  r_stall_windows;
    logic        r_timeout;

    logic        w_scl_sync;
    logic        w_sda_sync;
    logic        w_scl_low;
    logic        w_bus_free;
    logic [15:0] w_unit_raw;
    logic [15:0] w_unit_clocks;
    logic [15:0] w_unit_target;
    logic [3:0]  w_phase_units;
    logic        w_scl_release_phase;
    logic        w_busfree_phase;
    logic        w_stall;
    logic        w_unit_tick;
    logic        w_phase_end;
    logic        w_last_phase;
    logic        w_sample_now;
    logic        w_start_phy;
    logic [2:0]  w_start_op;
    logic [2:0]  w_windows_allowed;
    logic        w_use_fast;
    logic        w_leaves_bus_free;
    logic        w_recov_decide;
    logic        w_recov_retry;
    logic        w_recov_fail;
    logic        w_stop_needs_recovery;

    //--- Input synchronization
    // SCL and SDA are asynchronous in every build (they come from pads, and
    // with CDC_ENABLE=1 the whole core runs on smbus_clk). Two flops each, and
    // NOTHING in this module looks at the raw pin.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_scl_meta <= 2'b11;   // idle bus is released = high
            r_sda_meta <= 2'b11;
        end else begin
            r_scl_meta <= {r_scl_meta[0], smb_scl_i};
            r_sda_meta <= {r_sda_meta[0], smb_sda_i};
        end
    )

    assign w_scl_sync = r_scl_meta[1];
    assign w_sda_sync = r_sda_meta[1];
    assign w_bus_free = w_scl_sync && w_sda_sync;

    //--- Base unit
    // Floored at one clock so a degenerate divider stays legal instead of
    // wrapping the counter.

    // Rounded UP, not truncated. The SCL period is 8 units, so a truncating
    // divide shortens the period at small dividers - at cfg_clk_div = 2 it
    // gave 8 clocks per bit instead of 12, which is a different bus speed
    // than the register field advertises.
    // Recovery clocks are STANDARD-MODE timing regardless of cfg_fast_mode:
    // the device being recovered is by definition not keeping up, so the
    // slowest legal clock is the one most likely to shake it loose.
    assign w_use_fast    = cfg_fast_mode && (r_op != PHY_OP_RECOVER);
    assign w_unit_raw    = w_use_fast ? ((cfg_clk_div + 16'd8) >> 3)
                                      : ((cfg_clk_div + 16'd2) >> 1);
    assign w_unit_clocks = (w_unit_raw == 16'd0) ? 16'd1 : w_unit_raw;
    assign w_unit_target = w_unit_clocks - 16'd1;

    //--- Phase length table: (primitive, phase) -> units
    always_comb begin
        unique case (r_op)
            PHY_OP_START: begin
                unique case (r_phase)
                    3'd0:    w_phase_units = U_BUF;                                   // bus free
                    3'd1:    w_phase_units = cfg_fast_mode ? U_HD_STA_FST : U_HD_STA_STD;
                    default: w_phase_units = cfg_fast_mode ? U_LO_B_FST   : U_LO_B_STD;
                endcase
            end
            PHY_OP_RESTART: begin
                unique case (r_phase)
                    3'd0:    w_phase_units = cfg_fast_mode ? U_LO_A_FST   : U_LO_A_STD;
                    3'd1:    w_phase_units = cfg_fast_mode ? U_SU_STA_FST : U_SU_STA_STD;
                    3'd2:    w_phase_units = cfg_fast_mode ? U_HD_STA_FST : U_HD_STA_STD;
                    default: w_phase_units = cfg_fast_mode ? U_LO_B_FST   : U_LO_B_STD;
                endcase
            end
            PHY_OP_STOP: begin
                unique case (r_phase)
                    3'd0:    w_phase_units = cfg_fast_mode ? U_LO_A_FST : U_LO_A_STD;  // quiesce
                    3'd1:    w_phase_units = cfg_fast_mode ? U_LO_A_FST : U_LO_A_STD;
                    3'd2:    w_phase_units = U_SU_STO;
                    3'd3:    w_phase_units = U_BUF;
                    default: w_phase_units = 4'd1;
                endcase
            end
            PHY_OP_RECOVER: begin
                // A recovery clock is a FULL standard-mode bit, not a bit's
                // worth of one phase: tLOW is LO_B + LO_A and tHIGH is
                // HI_A + HI_B, so both clear 4.7 us / 4.0 us at the default
                // divider. Clocking a stuck device at 133 kHz asymmetric is
                // not "standard-mode timing", whatever the unit says.
                unique case (r_phase)
                    3'd0:    w_phase_units = U_LO_B_STD + U_LO_A_STD;  // tLOW
                    3'd1:    w_phase_units = U_HI_A_STD;   // release, sample
                    3'd2:    w_phase_units = U_HI_B_STD;   // rest of tHIGH
                    3'd3:    w_phase_units = U_LO_A_STD;   // SCL low, SDA free
                    3'd4:    w_phase_units = U_LO_A_STD;   // ... then SDA low
                    3'd5:    w_phase_units = U_SU_STO;
                    3'd6:    w_phase_units = U_BUF;
                    default: w_phase_units = 4'd1;
                endcase
            end
            default: begin   // PHY_OP_TX / PHY_OP_RX
                unique case (r_phase)
                    3'd0:    w_phase_units = cfg_fast_mode ? U_LO_A_FST : U_LO_A_STD;
                    3'd1:    w_phase_units = cfg_fast_mode ? U_HI_A_FST : U_HI_A_STD;
                    3'd2:    w_phase_units = cfg_fast_mode ? U_HI_B_FST : U_HI_B_STD;
                    default: w_phase_units = cfg_fast_mode ? U_LO_B_FST : U_LO_B_STD;
                endcase
            end
        endcase
    end

    //--- Which phases wait on the bus
    always_comb begin
        w_scl_release_phase = 1'b0;
        unique case (r_op)
            PHY_OP_RESTART: w_scl_release_phase = (r_phase == 3'd1);
            PHY_OP_STOP:    w_scl_release_phase = (r_phase == 3'd2);
            PHY_OP_RECOVER: w_scl_release_phase = (r_phase == 3'd1) ||
                                                  (r_phase == 3'd5);
            PHY_OP_TX,
            PHY_OP_RX:      w_scl_release_phase = (r_phase == 3'd1);
            default:        w_scl_release_phase = 1'b0;
        endcase
    end

    assign w_busfree_phase = (r_op == PHY_OP_START) && (r_phase == 3'd0);

    // Held at zero until the line we just let go of has actually risen, and -
    // before a START - until the whole bus reads free.
    assign w_stall = r_active && ((w_scl_release_phase && !w_scl_sync) ||
                                  (w_busfree_phase     && !w_bus_free));

    assign w_unit_tick  = r_active && !w_stall && (r_clk_cnt >= w_unit_target);
    assign w_phase_end  = w_unit_tick && (r_unit_cnt + 4'd1 >= w_phase_units);

    always_comb begin
        unique case (r_op)
            PHY_OP_START:   w_last_phase = (r_phase == 3'd2);
            PHY_OP_STOP:    w_last_phase = (r_phase == 3'd4);
            PHY_OP_RECOVER: w_last_phase = (r_phase == 3'd7);
            default:        w_last_phase = (r_phase == 3'd3);
        endcase
    end

    // Both of these leave the bus FREE; every other primitive leaves SCL low.
    assign w_leaves_bus_free = (r_op == PHY_OP_STOP) || (r_op == PHY_OP_RECOVER);

    // BUS RECOVERY. Sample SDA at the end of each recovery clock's high phase.
    // As soon as it reads high the stuck device has let go and we go straight
    // to the STOP. Nine clocks is the I2C recovery limit - it is one more than
    // a byte, so a device stuck anywhere inside one has been clocked out of it.
    assign w_recov_decide = (r_op == PHY_OP_RECOVER) && (r_phase == 3'd2) &&
                            w_phase_end;
    assign w_recov_retry  = w_recov_decide && !w_sda_sync && (r_recov_cnt < 4'd8);
    assign w_recov_fail   = w_recov_decide && !w_sda_sync && (r_recov_cnt >= 4'd8);

    // A STOP that released SDA and did NOT see it rise was not a STOP at all -
    // somebody else is holding the line down. That is exactly what recovery
    // is for, so the STOP turns into one rather than reporting success.
    assign w_stop_needs_recovery = (r_op == PHY_OP_STOP) && (r_phase == 3'd3) &&
                                   w_phase_end && !w_sda_sync;

    // RX samples at the end of the first high phase, in the middle of tHIGH.
    assign w_sample_now = (r_op == PHY_OP_RX) && (r_phase == 3'd1) && w_phase_end;

    assign w_start_phy = abort_req || (op_req && !r_active);
    assign w_start_op  = abort_req ? (abort_recover ? PHY_OP_RECOVER : PHY_OP_STOP)
                                   : op;

    //--- Primitive sequencer
    // Line state per (primitive, phase). This table IS the block's whole
    // electrical behaviour, so it is written out rather than derived:
    //
    //   START    P0 rel SCL+SDA (wait free)  P1 SDA low   P2 SCL low
    //   RESTART  P0 rel SDA        P1 rel SCL (wait)  P2 SDA low   P3 SCL low
    //   STOP     P0 SCL low, SDA UNCHANGED   P1 SDA low   P2 rel SCL (wait)
    //            P3 rel SDA (the STOP marker)  P4 idle
    //   TX/RX    P0 data bit       P1 rel SCL (wait)  P2 (high)    P3 SCL low
    //
    // STOP's P0 leaves SDA alone on purpose: it is the phase an ABORT enters
    // on, potentially with SCL high mid-bit, and moving SDA while SCL is high
    // would emit a spurious START or STOP instead of aborting.
    //
    // Between two transmitted 0 bits SDA is briefly released while SCL is low
    // (P3 of one bit into P0 of the next). That is legal - data is only ever
    // sampled while SCL is high - and it is visible on a waveform, so it is
    // recorded here rather than being re-diagnosed each time.

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n) || cfg_soft_reset) begin
            // A soft reset stops mid-primitive and RELEASES both lines.
            // Leaving them driven would wedge the bus for every other device.
            r_active        <= 1'b0;
            r_op            <= PHY_OP_START;
            r_phase         <= 3'd0;
            r_tx_bit        <= 1'b1;
            r_rx_bit        <= 1'b1;
            r_done          <= 1'b0;
            r_clk_cnt       <= 16'h0;
            r_unit_cnt      <= 4'd0;
            r_scl_drive_low <= 1'b0;
            r_sda_drive_low <= 1'b0;
            r_recov_cnt     <= 4'd0;
            r_recov_failed  <= 1'b0;
        end else begin
            r_done <= 1'b0;

            if (w_start_phy) begin
                r_active       <= 1'b1;
                r_op           <= w_start_op;
                r_phase        <= 3'd0;
                r_clk_cnt      <= 16'h0;
                r_unit_cnt     <= 4'd0;
                r_tx_bit       <= tx_bit;
                r_recov_cnt    <= 4'd0;
                r_recov_failed <= 1'b0;

                // Phase 0 line state.
                unique case (w_start_op)
                    PHY_OP_START: begin
                        r_scl_drive_low <= 1'b0;
                        r_sda_drive_low <= 1'b0;
                    end
                    PHY_OP_RESTART: begin
                        r_scl_drive_low <= 1'b1;
                        r_sda_drive_low <= 1'b0;
                    end
                    PHY_OP_STOP: begin
                        r_scl_drive_low <= 1'b1;
                        // SDA deliberately unchanged - see the note above.
                    end
                    PHY_OP_RECOVER: begin
                        r_scl_drive_low <= 1'b1;
                        r_sda_drive_low <= 1'b0;   // SDA released to clock
                    end
                    PHY_OP_TX: begin
                        r_scl_drive_low <= 1'b1;
                        r_sda_drive_low <= ~tx_bit;
                    end
                    default: begin   // PHY_OP_RX
                        r_scl_drive_low <= 1'b1;
                        r_sda_drive_low <= 1'b0;
                    end
                endcase
            end else if (r_active) begin
                if (r_timeout) begin
                    // Abandon: release both lines and report. A STOP cannot be
                    // generated while someone else holds SCL down, so giving
                    // up is the only exit that always exists.
                    r_active        <= 1'b0;
                    r_done          <= 1'b1;
                    r_scl_drive_low <= 1'b0;
                    r_sda_drive_low <= 1'b0;
                end else begin
                    if (w_sample_now) begin
                        r_rx_bit <= w_sda_sync;
                    end

                    if (w_unit_tick && !w_phase_end) begin
                        r_clk_cnt  <= 16'h0;
                        r_unit_cnt <= r_unit_cnt + 4'd1;
                    end else if (w_phase_end) begin
                        r_clk_cnt  <= 16'h0;
                        r_unit_cnt <= 4'd0;

                        if (w_recov_retry) begin
                            // SDA still low: another recovery clock.
                            r_phase         <= 3'd0;
                            r_recov_cnt     <= r_recov_cnt + 4'd1;
                            r_scl_drive_low <= 1'b1;
                            r_sda_drive_low <= 1'b0;
                        end else if (w_recov_fail) begin
                            // Nine clocks and SDA is still held. Nothing this
                            // master can do releases it, so release our own
                            // lines, say so, and stop.
                            r_active        <= 1'b0;
                            r_done          <= 1'b1;
                            r_recov_failed  <= 1'b1;
                            r_scl_drive_low <= 1'b0;
                            r_sda_drive_low <= 1'b0;
                        end else if (w_stop_needs_recovery) begin
                            // The STOP let SDA go and it did not rise.
                            r_op            <= PHY_OP_RECOVER;
                            r_phase         <= 3'd0;
                            r_recov_cnt     <= 4'd0;
                            r_scl_drive_low <= 1'b1;
                            r_sda_drive_low <= 1'b0;
                        end else if (w_last_phase) begin
                            r_active <= 1'b0;
                            r_done   <= 1'b1;
                            // STOP and RECOVER leave the bus free; every
                            // other primitive leaves SCL low.
                            r_scl_drive_low <= !w_leaves_bus_free;
                            r_sda_drive_low <= 1'b0;
                        end else begin
                            r_phase <= r_phase + 3'd1;

                            unique case (r_op)
                                PHY_OP_START: begin
                                    // P0->P1 SDA low (START), P1->P2 SCL low
                                    r_sda_drive_low <= 1'b1;
                                    r_scl_drive_low <= (r_phase == 3'd1);
                                end
                                PHY_OP_RESTART: begin
                                    // P0->P1 rel SCL, P1->P2 SDA low, P2->P3 SCL low
                                    r_scl_drive_low <= (r_phase == 3'd2);
                                    r_sda_drive_low <= (r_phase != 3'd0);
                                end
                                PHY_OP_STOP: begin
                                    // P0->P1 SDA low (SCL stays low)
                                    // P1->P2 release SCL, SDA STAYS LOW
                                    // P2->P3 release SDA - THIS is the STOP
                                    // P3->P4 idle, bus free
                                    //
                                    // SDA has to outlast SCL by tSU;STO. It
                                    // used to share SCL's predicate, so both
                                    // lines released on the same edge and no
                                    // STOP condition was ever generated -
                                    // every transaction just stopped clocking.
                                    r_scl_drive_low <= (r_phase == 3'd0);
                                    r_sda_drive_low <= (r_phase == 3'd0) ||
                                                       (r_phase == 3'd1);
                                end
                                PHY_OP_RECOVER: begin
                                    // p0->p1 release SCL, p1->p2 hold high,
                                    // p2->p3 SCL LOW ONLY, p3->p4 SDA low,
                                    // p4->p5 release SCL, p5->p6 release SDA
                                    // (the STOP marker), p6->p7 idle.
                                    //
                                    // SCL falls a whole phase before SDA is
                                    // driven, never on the same edge: moving
                                    // SDA while SCL may still be high is what
                                    // makes a START or a STOP, which is the
                                    // module's own rule a few lines up.
                                    r_scl_drive_low <= (r_phase == 3'd2) ||
                                                       (r_phase == 3'd3);
                                    r_sda_drive_low <= (r_phase == 3'd3) ||
                                                       (r_phase == 3'd4);
                                end
                                default: begin  // PHY_OP_TX / PHY_OP_RX
                                    // P0->P1 rel SCL, P1->P2 hold, P2->P3 SCL low
                                    r_scl_drive_low <= (r_phase == 3'd2);
                                    r_sda_drive_low <= (r_op == PHY_OP_TX) ? ~r_tx_bit : 1'b0;
                                end
                            endcase
                        end
                    end else if (!w_stall) begin
                        r_clk_cnt <= r_clk_cnt + 16'h1;
                    end
                end
            end
        end
    )

    assign op_done  = r_done;
    assign rx_bit   = r_rx_bit;
    assign phy_busy = r_active;

    //--- Stall timeout
    // "SCL low" means low ON THE BUS: either this master is pulling it down
    // (a wedged master) or the line still reads low after we let go (a slave
    // stretching forever, or a short). Looking only at the input would miss
    // the first; looking only at our own drive would miss the second.

    // ONLY WHILE THIS PHY OWNS A PRIMITIVE. The counter used to run off the
    // WIRE, so a foreign master holding SCL low while this master was idle set
    // the timeout level, and the first transaction started afterwards aborted
    // on a report that belonged to nobody. r_active covers the bus-free wait
    // too, because that wait is inside the START primitive.
    assign w_scl_low = r_active && (r_scl_drive_low || !w_scl_sync);

    assign w_windows_allowed = w_leaves_bus_free ? WINDOWS_STOP : WINDOWS_NORMAL;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n) || cfg_soft_reset) begin
            r_stall_cnt     <= 24'h0;
            r_stall_windows <= 3'd0;
            r_timeout       <= 1'b0;
        end else if (w_start_phy || timeout_ack) begin
            // A new primitive - including the abort's STOP - starts a fresh
            // window, and so does the sequencer telling us it has taken the
            // report. THE REPORT IS CONSUMED ONCE: a level that outlives the
            // primitive it describes is read again by the next one.
            r_stall_cnt     <= 24'h0;
            r_stall_windows <= 3'd0;
            r_timeout       <= 1'b0;
        end else if ((cfg_timeout == 24'h0) || !(w_scl_low || w_stall)) begin
            r_stall_cnt     <= 24'h0;
            r_stall_windows <= 3'd0;
            r_timeout       <= 1'b0;
        end else if (r_stall_cnt >= cfg_timeout) begin
            r_stall_cnt     <= 24'h0;
            if (r_stall_windows >= w_windows_allowed) begin
                r_timeout   <= 1'b1;
            end else begin
                r_stall_windows <= r_stall_windows + 3'd1;
            end
        end else begin
            r_stall_cnt     <= r_stall_cnt + 24'h1;
        end
    )

    assign phy_timeout    = r_timeout;
    assign recover_failed = r_recov_failed;
    assign sda_sync       = w_sda_sync;
    assign scl_sync       = w_scl_sync;

    //--- Line drivers - the whole open-drain contract, in four assigns
    assign smb_scl_o = ~r_scl_drive_low;
    assign smb_scl_t = ~r_scl_drive_low;
    assign smb_sda_o = ~r_sda_drive_low;
    assign smb_sda_t = ~r_sda_drive_low;

endmodule
