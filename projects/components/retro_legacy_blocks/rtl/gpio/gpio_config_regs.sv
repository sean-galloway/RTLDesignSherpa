// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: gpio_config_regs
// Purpose: GPIO Configuration Registers - Connects PeakRDL to Core
//
// Description:
//   Wrapper connecting PeakRDL-generated registers to GPIO core.
//   Handles the hwif (hardware interface) signal mapping.
//
// Architecture:
//   APB -> apb4_slave -> CMD/RSP -> peakrdl_to_cmdrsp -> regblk_* ->
//     -> gpio_regs (PeakRDL) -> hwif -> gpio_core
//
// Write-strobe contract (issue #44)
//   Every software-visible operation in this block is driven by the register
//   WRITE STROBE, never by a change in a stored value. The regblock exports
//   `swmod` for GPIO_OUTPUT, GPIO_OUTPUT_SET/CLR/TGL and GPIO_INT_STATUS;
//   swmod is combinational with the decoded request, so two things have to be
//   corrected before it can be used as an operation pulse:
//
//     1. It is a LEVEL, not a pulse. peakrdl_to_cmdrsp deliberately HOLDS
//        regblk_req from the accept cycle through CMD_WAIT_ACK (see the
//        warning in that file - shortening it broke every register read), so
//        swmod is asserted for the whole transaction, at least two cycles.
//        Taking it at face value performs each operation twice. That is
//        invisible for SET and CLR, which are idempotent, and fatal for TGL,
//        which cancels itself. Hence the rising-edge detect below: one write
//        transaction, one pulse. (Verify a strobe change on TGL, never on SET.)
//     2. It leads the data by one cycle - it is asserted while the field
//        storage is still taking the written value. Hence the extra flop:
//        the edge at cycle T becomes the strobe at T+1, which is exactly when
//        the field presents the new mask.
//
//   SystemRDL restricts `singlepulse` to 1-bit fields, so the 32-bit atomic
//   masks cannot self-clear; the registered edge is what makes them one-cycle
//   pulses instead. The consequence that matters: writing the SAME mask twice
//   performs the operation twice.
//
// GPIO_OUTPUT readback
//   GPIO_OUTPUT reads back the LIVE output latch. gpio_core's output latch is
//   written back into the field (hw = rw + we) one cycle after any atomic
//   operation, so an atomic SET/CLR/TGL is visible in the register. The
//   write-back is strobe-gated rather than continuous because a continuous
//   write-back would present the pre-write latch value in the cycle after a
//   software write and stomp it; `precedence = sw` additionally makes a
//   software write win over a coincident write-back.
//
// GPIO_INT_STATUS W1C-vs-hardware-set race
//   CHOSEN: option (a), a one-cycle deferred-set register here.
//   The generated regblock resolves the field as
//     if (sw W1C write) ... else if (hw set) ...
//   for the WHOLE register, so a hardware set landing in the same cycle as any
//   software W1C write is discarded - and edge pulses are one cycle wide, so
//   the event is lost permanently. This module latches the coincident set into
//   r_int_set_deferred (qualified by w_int_status_sw_wr, a MIRROR of the
//   regblock's own discard condition rather than swmod - see that signal for
//   why swmod is not sufficient; the whole multi-cycle transaction discards
//   hardware sets, so the deferral must cover all of it, and it accumulates
//   while the level is high - masked by the W1C mask taken from
//   regblk_wr_data/regblk_wr_biten, which are combinational with that same
//   request) and ORs it into `.next` on the following cycle, giving the
//   conventional per-bit semantic
//     next = (value | hw_set) & ~w1c_mask
//   Option (b) - owning the sticky register here and exposing it through an
//   external register or a write-only clear alias - was rejected: it duplicates
//   storage the regblock already owns, moves the W1C decode out of the
//   generated file where it can silently drift from the RDL, and changes the
//   register's software-visible type for no behavioural gain.
//
// Documentation: projects/components/retro_legacy_blocks/rtl/gpio/README.md
// Created: 2025-11-29
// Updated: 2025-11-30 - Changed to 32-bit data width
// Updated: 2026-09-08 - issue #44: strobe-driven atomics and direct writes,
//                       live GPIO_OUTPUT readback, W1C race deferral
// Updated: 2026-09-08 - issue #44 review: deferral mirrors the regblock decode
//                       instead of swmod, write-back preserves bits above
//                       GPIO_WIDTH, per-pin enable gates edge irq too
// Updated: 2026-09-09 - param guard is simulation-time, gated `ifndef SYNTHESIS

`timescale 1ns / 1ps

`include "reset_defs.svh"

module gpio_config_regs
    import gpio_regs_pkg::*;
#(
    parameter int GPIO_WIDTH = 32,
    parameter int SYNC_STAGES = 2,
    parameter int ADDR_WIDTH = 12,
    parameter int DATA_WIDTH = 32
) (
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,

    // PeakRDL regblock interface (from peakrdl_to_cmdrsp)
    input  logic                    regblk_req,
    input  logic                    regblk_req_is_wr,
    input  logic [ADDR_WIDTH-1:0]   regblk_addr,
    input  logic [DATA_WIDTH-1:0]   regblk_wr_data,
    input  logic [DATA_WIDTH-1:0]   regblk_wr_biten,
    output logic                    regblk_req_stall_wr,
    output logic                    regblk_req_stall_rd,
    output logic                    regblk_rd_ack,
    output logic                    regblk_rd_err,
    output logic [DATA_WIDTH-1:0]   regblk_rd_data,
    output logic                    regblk_wr_ack,
    output logic                    regblk_wr_err,

    // GPIO Pins Interface
    input  logic [GPIO_WIDTH-1:0]   gpio_in,
    output logic [GPIO_WIDTH-1:0]   gpio_out,
    output logic [GPIO_WIDTH-1:0]   gpio_oe,

    // Interrupt Output
    output logic                    irq
);

    // Width of a register field in the PeakRDL block (regwidth = 32 in the RDL)
    localparam int REG_WIDTH = 32;

    // ========================================================================
    // Simulation-time parameter validation
    // ========================================================================
    // Every GPIO_WIDTH-wide value in this block is carried in a 32-bit register
    // field, so a wider port would silently truncate; a zero/negative width has
    // no legal slice.
    //
    // This is an `initial` block, so it runs at time 0 in SIMULATION - it is
    // not an elaboration-time check and cannot stop a synthesis run. Gated by
    // `ifndef SYNTHESIS` for the same reason every other sim-only construct in
    // this block is.
`ifndef SYNTHESIS
    initial begin : param_check
        if (GPIO_WIDTH > REG_WIDTH || GPIO_WIDTH < 1) begin
            $error("gpio_config_regs: GPIO_WIDTH=%0d out of range [1,%0d]",
                   GPIO_WIDTH, REG_WIDTH);
        end
    end
`endif

    // PeakRDL hardware interface signals
    gpio_regs_pkg::gpio_regs__in_t  hwif_in;
    gpio_regs_pkg::gpio_regs__out_t hwif_out;

    // Internal signals to/from core
    logic [GPIO_WIDTH-1:0] w_sts_input_data;
    logic [GPIO_WIDTH-1:0] w_sts_raw_int;
    logic [GPIO_WIDTH-1:0] w_sts_int_pending;

    // Live output latch inside gpio_core (drives the pins AND the readback).
    // r_ because the flop lives in gpio_core (r_output_data): reading this
    // costs a cycle of latency exactly as if the flop were declared here.
    logic [GPIO_WIDTH-1:0] r_output_live;

    // swmod levels, and their one-cycle-delayed copies for edge detection
    logic w_output_swmod;
    logic w_set_swmod;
    logic w_clr_swmod;
    logic w_tgl_swmod;
    logic r_output_swmod_d;
    logic r_set_swmod_d;
    logic r_clr_swmod_d;
    logic r_tgl_swmod_d;

    // One write transaction = one rising edge of the swmod level
    logic w_output_wr_event;
    logic w_set_wr_event;
    logic w_clr_wr_event;
    logic w_tgl_wr_event;

    // Registered write strobes (the write event delayed one cycle, to line up
    // with the field storage it qualifies)
    logic r_output_wr_stb;
    logic r_set_stb;
    logic r_clr_stb;
    logic r_tgl_stb;

    // Atomic operation pulses handed to the core
    logic [GPIO_WIDTH-1:0] w_output_set;
    logic [GPIO_WIDTH-1:0] w_output_clr;
    logic [GPIO_WIDTH-1:0] w_output_tgl;

    // GPIO_OUTPUT write-back control
    logic w_atomic_active;
    logic r_output_wb_en;

    // GPIO_INT_STATUS deferred-set (W1C race)
    logic                  w_int_status_sw_wr;
    logic [GPIO_WIDTH-1:0] r_int_set_deferred;
    logic [GPIO_WIDTH-1:0] w_int_w1c_mask;
    logic [GPIO_WIDTH-1:0] w_int_set_now;

    // 32-bit register-facing views of the GPIO_WIDTH-wide core signals
    logic [REG_WIDTH-1:0] w_input_data_reg;
    logic [REG_WIDTH-1:0] w_raw_int_reg;
    logic [REG_WIDTH-1:0] w_output_live_reg;
    logic [REG_WIDTH-1:0] w_int_set_now_reg;

    // ========================================================================
    // PeakRDL Register Block
    // ========================================================================
    gpio_regs u_gpio_regs (
        .clk        (clk),
        .rst        (~rst_n),  // PeakRDL uses active-high reset

        // PeakRDL cpuif interface (from peakrdl_to_cmdrsp)
        .s_cpuif_req            (regblk_req),
        .s_cpuif_req_is_wr      (regblk_req_is_wr),
        .s_cpuif_addr           (regblk_addr[5:0]),  // 6-bit address (64 bytes)
        .s_cpuif_wr_data        (regblk_wr_data),
        .s_cpuif_wr_biten       (regblk_wr_biten),
        .s_cpuif_req_stall_wr   (regblk_req_stall_wr),
        .s_cpuif_req_stall_rd   (regblk_req_stall_rd),
        .s_cpuif_rd_ack         (regblk_rd_ack),
        .s_cpuif_rd_err         (regblk_rd_err),
        .s_cpuif_rd_data        (regblk_rd_data),
        .s_cpuif_wr_ack         (regblk_wr_ack),
        .s_cpuif_wr_err         (regblk_wr_err),

        // Hardware interface
        .hwif_in    (hwif_in),
        .hwif_out   (hwif_out)
    );

    // ========================================================================
    // Write Strobe Generation (edge-detect, then align)
    // ========================================================================
    // swmod is a LEVEL held for the whole regblock transaction and it leads
    // the field storage by one cycle. Rising edge -> exactly one event per
    // write; one flop -> the strobe lands in the cycle where the field
    // presents the newly written value. The operation no longer depends on
    // that value being DIFFERENT from what the field already held.
    //
    // REQUIREMENT on the upstream cpuif: regblk_req must DE-ASSERT between
    // transactions. The edge detect counts writes by rising edges, so two
    // back-to-back writes to the same register with no idle cycle between them
    // look like one long level and produce one event -- which halves TGL. This
    // holds for apb4_slave and apb4_slave_cdc today (both are strictly
    // one-outstanding and drop req while waiting for the ack), and the
    // a_*_swmod_len assertions at the bottom of this file trip if a future
    // pipelined cpuif breaks it.

    assign w_output_swmod = hwif_out.GPIO_OUTPUT.output_data.swmod;
    assign w_set_swmod    = hwif_out.GPIO_OUTPUT_SET.set_bits.swmod;
    assign w_clr_swmod    = hwif_out.GPIO_OUTPUT_CLR.clear_bits.swmod;
    assign w_tgl_swmod    = hwif_out.GPIO_OUTPUT_TGL.toggle_bits.swmod;

    assign w_output_wr_event = w_output_swmod & ~r_output_swmod_d;
    assign w_set_wr_event    = w_set_swmod    & ~r_set_swmod_d;
    assign w_clr_wr_event    = w_clr_swmod    & ~r_clr_swmod_d;
    assign w_tgl_wr_event    = w_tgl_swmod    & ~r_tgl_swmod_d;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_output_swmod_d <= 1'b0;
            r_set_swmod_d    <= 1'b0;
            r_clr_swmod_d    <= 1'b0;
            r_tgl_swmod_d    <= 1'b0;
            r_output_wr_stb  <= 1'b0;
            r_set_stb        <= 1'b0;
            r_clr_stb        <= 1'b0;
            r_tgl_stb        <= 1'b0;
        end else begin
            r_output_swmod_d <= w_output_swmod;
            r_set_swmod_d    <= w_set_swmod;
            r_clr_swmod_d    <= w_clr_swmod;
            r_tgl_swmod_d    <= w_tgl_swmod;
            r_output_wr_stb  <= w_output_wr_event;
            r_set_stb        <= w_set_wr_event;
            r_clr_stb        <= w_clr_wr_event;
            r_tgl_stb        <= w_tgl_wr_event;
        end
    )

    // One-cycle atomic operation pulses: the stored mask, gated by its strobe.
    assign w_output_set =
        r_set_stb ? hwif_out.GPIO_OUTPUT_SET.set_bits.value[GPIO_WIDTH-1:0] : '0;
    assign w_output_clr =
        r_clr_stb ? hwif_out.GPIO_OUTPUT_CLR.clear_bits.value[GPIO_WIDTH-1:0] : '0;
    assign w_output_tgl =
        r_tgl_stb ? hwif_out.GPIO_OUTPUT_TGL.toggle_bits.value[GPIO_WIDTH-1:0] : '0;

    // ========================================================================
    // GPIO Core Instance
    // ========================================================================
    gpio_core #(
        .GPIO_WIDTH     (GPIO_WIDTH),
        .SYNC_STAGES    (SYNC_STAGES)
    ) u_gpio_core (
        .clk            (clk),
        .rst_n          (rst_n),

        // GPIO Pins
        .gpio_in        (gpio_in),
        .gpio_out       (r_output_live),
        .gpio_oe        (gpio_oe),

        // Configuration (now single 32-bit registers)
        .cfg_gpio_enable    (hwif_out.GPIO_CONTROL.gpio_enable.value),
        .cfg_direction      (hwif_out.GPIO_DIRECTION.direction.value[GPIO_WIDTH-1:0]),
        .cfg_output_data    (hwif_out.GPIO_OUTPUT.output_data.value[GPIO_WIDTH-1:0]),
        .cfg_output_wr_stb  (r_output_wr_stb),
        .cfg_int_enable_pins(hwif_out.GPIO_INT_ENABLE.int_enable.value[GPIO_WIDTH-1:0]),
        .cfg_int_type       (hwif_out.GPIO_INT_TYPE.int_type.value[GPIO_WIDTH-1:0]),
        .cfg_int_polarity   (hwif_out.GPIO_INT_POLARITY.int_polarity.value[GPIO_WIDTH-1:0]),
        .cfg_int_both       (hwif_out.GPIO_INT_BOTH.int_both.value[GPIO_WIDTH-1:0]),

        // Atomic operations
        .cfg_output_set     (w_output_set),
        .cfg_output_clr     (w_output_clr),
        .cfg_output_tgl     (w_output_tgl),

        // Status
        .sts_input_data     (w_sts_input_data),
        .sts_raw_int        (w_sts_raw_int),
        .sts_int_pending    (w_sts_int_pending)
    );

    assign gpio_out = r_output_live;

    // ========================================================================
    // GPIO_OUTPUT Live Write-Back
    // ========================================================================
    // An atomic pulse in cycle T updates gpio_core's latch at the end of T, so
    // the new value is present during T+1 -- which is exactly when the
    // registered enable below fires. Direct software writes need no write-back
    // (the field already holds what the core is about to latch).

    assign w_atomic_active = |(w_output_set | w_output_clr | w_output_tgl);

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_output_wb_en <= 1'b0;
        end else begin
            r_output_wb_en <= w_atomic_active;
        end
    )

    // ========================================================================
    // GPIO_INT_STATUS Deferred Set (W1C-vs-hardware-set race)
    // ========================================================================
    // regblk_wr_data/regblk_wr_biten are combinational into the regblock's
    // decode, so during the swmod cycle they ARE the W1C mask of the write the
    // regblock is committing. Bits that the write clears must not be deferred
    // (that is what makes this `(value | hw_set) & ~w1c_mask` rather than
    // "hardware set always wins").

    // The condition that discards a hardware set is the regblock's SW-write
    // branch, NOT swmod. gpio_regs.sv takes the "SW write 1 clear" branch on
    //     decoded_reg_strb.GPIO_INT_STATUS && decoded_req_is_wr
    // but exports
    //     swmod = decoded_reg_strb.GPIO_INT_STATUS && decoded_req_is_wr
    //             && |decoded_wr_biten
    // so an APB4 write with PSTRB=0 takes the discarding branch with swmod LOW:
    // qualifying the deferral on swmod would leave it idle and lose the event.
    // Mirror the regblock decode instead. It decodes
    //   decoded_reg_strb.GPIO_INT_STATUS = cpuif_req_masked & (cpuif_addr == 6'h20)
    // on the same 6 address bits this module feeds it, and both cpuif stalls
    // are tied to zero inside the regblock, so cpuif_req_masked == regblk_req.
    // The a_int_status_swmod_mirrored assertion below is the drift guard: if a
    // regenerated regblock changes that decode, it fires rather than silently
    // dropping interrupts.
    assign w_int_status_sw_wr = regblk_req && regblk_req_is_wr &&
                                (regblk_addr[5:0] == 6'h20);

    assign w_int_w1c_mask = regblk_wr_data[GPIO_WIDTH-1:0] & regblk_wr_biten[GPIO_WIDTH-1:0];
    assign w_int_set_now  = w_sts_int_pending | r_int_set_deferred;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_int_set_deferred <= '0;
        end else if (w_int_status_sw_wr) begin
            // The regblock is taking the software W1C branch this cycle and
            // will throw the hardware set away -- hold it for the next cycle.
            r_int_set_deferred <= w_int_set_now & ~w_int_w1c_mask;
        end else begin
            // Not a software write: the stickybit branch accepts `.next`, so
            // anything held has now been applied.
            r_int_set_deferred <= '0;
        end
    )

    // ========================================================================
    // IRQ Generation - Mode-Dependent (Edge=Sticky, Level=Live)
    // ========================================================================
    // IRQ is asserted when:
    // 1. Global interrupt enable is set (in GPIO_CONTROL)
    // 2. For EDGE mode: sticky status register bit is set (W1C behavior)
    // 3. For LEVEL mode: live raw interrupt is active (follows input level)
    //
    // This ensures:
    // - Edge interrupts latch and require explicit W1C to clear
    // - Level interrupts de-assert automatically when input level changes

    logic [GPIO_WIDTH-1:0] w_sticky_int_status;
    assign w_sticky_int_status = hwif_out.GPIO_INT_STATUS.int_status.value[GPIO_WIDTH-1:0];

    // Get interrupt type configuration (1=level, 0=edge)
    logic [GPIO_WIDTH-1:0] w_int_type;
    assign w_int_type = hwif_out.GPIO_INT_TYPE.int_type.value[GPIO_WIDTH-1:0];

    // Get per-pin interrupt enable
    logic [GPIO_WIDTH-1:0] w_int_enable_pins;
    assign w_int_enable_pins = hwif_out.GPIO_INT_ENABLE.int_enable.value[GPIO_WIDTH-1:0];

    // Effective interrupt status per bit:
    // - Edge mode (type=0): use sticky register
    // - Level mode (type=1): use live raw interrupt status
    logic [GPIO_WIDTH-1:0] w_effective_int_status;
    always_comb begin
        for (int i = 0; i < GPIO_WIDTH; i++) begin
            if (w_int_type[i]) begin
                // Level mode: use live signal (AND with enable)
                w_effective_int_status[i] = w_sts_raw_int[i] & w_int_enable_pins[i];
            end else begin
                // Edge mode: sticky register, RE-GATED by the per-pin enable.
                // The sticky bit is only SET while the pin is enabled, but it
                // survives a later disable; without this gate, clearing a pin's
                // GPIO_INT_ENABLE leaves irq asserted until software W1Cs the
                // status. Every pin's contribution is gated in both modes, so
                // irq = |(effective_status & int_enable) & global_enable.
                w_effective_int_status[i] = w_sticky_int_status[i] & w_int_enable_pins[i];
            end
        end
    end

    assign irq = hwif_out.GPIO_CONTROL.int_enable.value && (|w_effective_int_status);

    // ========================================================================
    // Connect Status to hwif_in
    // ========================================================================
    // Zero-extend the GPIO_WIDTH-wide core signals to the 32-bit register
    // fields (GPIO_WIDTH <= 32; the upper bits read back as 0).
    always_comb begin
        w_input_data_reg = '0;
        w_input_data_reg[GPIO_WIDTH-1:0] = w_sts_input_data;
    end

    always_comb begin
        w_raw_int_reg = '0;
        w_raw_int_reg[GPIO_WIDTH-1:0] = w_sts_raw_int;
    end

    // GPIO_OUTPUT is written BACK into the field, so it must not be
    // zero-extended: only the live lanes exist in the core, and bits
    // [31:GPIO_WIDTH] are ordinary storage software may have written. Seed the
    // write-back with the field's current value so an atomic op changes the
    // live lanes and nothing else.
    always_comb begin
        w_output_live_reg = hwif_out.GPIO_OUTPUT.output_data.value;
        w_output_live_reg[GPIO_WIDTH-1:0] = r_output_live;
    end

    always_comb begin
        w_int_set_now_reg = '0;
        w_int_set_now_reg[GPIO_WIDTH-1:0] = w_int_set_now;
    end

    // Input data register (read-only)
    assign hwif_in.GPIO_INPUT.input_data.next = w_input_data_reg;

    // Raw interrupt status (read-only)
    assign hwif_in.GPIO_RAW_INT.raw_status.next = w_raw_int_reg;

    // Output data register: live value written back after an atomic op
    assign hwif_in.GPIO_OUTPUT.output_data.next = w_output_live_reg;
    assign hwif_in.GPIO_OUTPUT.output_data.we   = r_output_wb_en;

    // Interrupt status (W1C with stickybit - set by hardware via next)
    // stickybit: when next[i] is high, bit i is set in the register
    assign hwif_in.GPIO_INT_STATUS.int_status.next = w_int_set_now_reg;

    // ========================================================================
    // Simulation-only contract checks
    // ========================================================================
`ifndef SYNTHESIS
`ifndef VERILATOR
    // Drift guard for the mirrored GPIO_INT_STATUS write decode. swmod is that
    // same decode ANDed with |wr_biten, so swmod high with the mirror low is
    // impossible unless the generated regblock's decode has changed underneath
    // this module -- at which point the deferral silently stops covering the
    // discard window and hardware sets are lost.
    a_int_status_swmod_mirrored: assert property (
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        hwif_out.GPIO_INT_STATUS.int_status.swmod |-> w_int_status_sw_wr
    ) else $error("gpio_config_regs: GPIO_INT_STATUS swmod asserted without ",
                  "the mirrored regblock decode -- w_int_status_sw_wr has ",
                  "drifted from gpio_regs.sv and the W1C deferral no longer ",
                  "covers the discard window");

    // The write strobes are rising-edge detects on swmod, so a swmod level that
    // spans more than one transaction merges two writes into one operation.
    // The upstream bridge holds regblk_req for the accept cycle plus
    // CMD_WAIT_ACK -- two cycles -- and then drops it, so three consecutive
    // cycles means the cpuif has become pipelined and TGL is now being halved.
    property p_swmod_max_two(logic swmod_level);
        @(posedge clk) disable iff (`RST_ASSERTED(rst_n))
        not (swmod_level [*3]);
    endproperty

    a_output_swmod_len: assert property (p_swmod_max_two(w_output_swmod))
        else $error("gpio_config_regs: GPIO_OUTPUT swmod held >2 cycles -- ",
                    "the cpuif no longer drops regblk_req between ",
                    "writes, so the rising-edge detect merges them");
    a_set_swmod_len: assert property (p_swmod_max_two(w_set_swmod))
        else $error("gpio_config_regs: GPIO_OUTPUT_SET swmod held >2 cycles -- ",
                    "the cpuif no longer drops regblk_req between ",
                    "writes, so the rising-edge detect merges them");
    a_clr_swmod_len: assert property (p_swmod_max_two(w_clr_swmod))
        else $error("gpio_config_regs: GPIO_OUTPUT_CLR swmod held >2 cycles -- ",
                    "the cpuif no longer drops regblk_req between ",
                    "writes, so the rising-edge detect merges them");
    a_tgl_swmod_len: assert property (p_swmod_max_two(w_tgl_swmod))
        else $error("gpio_config_regs: GPIO_OUTPUT_TGL swmod held >2 cycles -- ",
                    "the cpuif no longer drops regblk_req between ",
                    "writes, so the rising-edge detect merges them");
`endif
`endif

endmodule : gpio_config_regs
