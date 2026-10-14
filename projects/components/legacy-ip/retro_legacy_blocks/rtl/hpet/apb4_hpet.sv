// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: apb4_hpet
// Purpose: Apb Hpet module
//
// Documentation: projects/components/apb4_hpet.sv/PRD.md
// Subsystem: apb4_hpet.sv
//
// Author: sean galloway
// Created: 2025-10-18
// Updated: 2026-09-09 - issue #46 review: halted-counter requirement for
//                       partial counter writes, r_ prefix on flopped strobes
// Updated: 2026-09-28 - RLB/hpet TASK-003: legacy_irq0/legacy_irq8 outputs, and
//                       w_legacy_replacement now reaches hpet_core (it was
//                       declared and driven but consumed by nothing)
// Updated: 2026-10-13 - header register map brought to the published spec
//                       map the RDL implements (comments only)

/**
 * ============================================================================
 * APB HPET Top Level Integration
 * ============================================================================
 *
 * DESCRIPTION:
 *   Top-level module that integrates APB slave with CDC, configuration
 *   registers, and HPET timer core. Provides complete HPET functionality
 *   with dual clock domain support.
 *
 * ARCHITECTURE:
 *   - APB Slave CDC: Handles low-frequency APB interface with clock crossing
 *   - Config Registers: High-speed register bank for HPET configuration
 *   - HPET Core: High-speed timer logic with precise timing
 *
 * CLOCK DOMAINS:
 *   - pclk: Low frequency APB interface clock
 *   - hpet_clk: High frequency timer clock
 *
 * REGISTER MAP AND BIT FIELDS:
 *   The PUBLISHED HPET spec map (RLB/hpet TASK-006); rdl/hpet/hpet_regs.rdl
 *   is the source of truth. 64-bit spec registers appear as LO/HI halves.
 *
 *   Global Registers:
 *   ----------------
 *   0x000: HPET_ID - GCAP_ID[31:0], Capabilities and ID (Read-Only)
 *          [31:16] vendor_id - the VENDOR_ID parameter, full 16 bits
 *          [15]    leg_rt_cap - reads 1: the LegacyReplacement Route is
 *                  implemented (RLB/hpet TASK-003). Drivers gate on this
 *                  bit, so its POSITION is load-bearing
 *          [14]    Reserved
 *          [13]    count_size_cap - reads 1 (64-bit main counter)
 *          [12:8]  num_tim_cap - NUM_TIMERS - 1 (e.g., 0x01 for 2 timers)
 *          [7:0]   rev_id - the REVISION_ID parameter
 *
 *   0x004: HPET_PERIOD - GCAP_ID[63:32] (Read-Only)
 *          [31:0]  Femtoseconds per main-counter tick, from
 *                  COUNTER_CLK_PERIOD_FS
 *
 *   0x010: HPET_CONFIG - GEN_CONF, Global Configuration (Read/Write)
 *          [31:2]  Reserved
 *          [1]     legacy_replacement - timer 0 leaves on legacy_irq0 (IRQ0)
 *                  and timer 1 on legacy_irq8 (IRQ8), both SUPPRESSED on
 *                  timer_irq
 *          [0]     hpet_enable (1=counter runs, 0=counter halted). The ONLY
 *                  run control: the spec defines no per-timer run enable
 *
 *   0x020: HPET_STATUS - GINTR_STA, Interrupt Status (Read/Write-1-to-Clear)
 *          [31:8]  Reserved
 *          [7:0]   Timer Interrupt Status, bit n = timer n (bits at or
 *                  above NUM_TIMERS read 0). Set on EVERY fire, whatever
 *                  TIMER_CONFIG.timer_int_enable says; write 1 to clear
 *
 *   0x0F0: HPET_COUNTER_LO - MAIN_CNT[31:0] (Read/Write)
 *          [31:0]  Lower 32 bits of 64-bit main counter
 *
 *   0x0F4: HPET_COUNTER_HI - MAIN_CNT[63:32] (Read/Write)
 *          [31:0]  Upper 32 bits of 64-bit main counter
 *
 *          The two halves are written INDEPENDENTLY: each write loads only
 *          its own half of the main counter, so a 64-bit value takes two
 *          writes and the intermediate state is visible. Write them with
 *          the counter halted (HPET_CONFIG[0] = 0), as on a real HPET.
 *
 *          A PARTIAL (byte-strobed, PSTRB != 4'hF) write to either counter
 *          half REQUIRES the counter to be halted, and this is a harder
 *          requirement than the one above, not a restatement of it. The
 *          regblock merges the un-written bytes from its own mirror of the
 *          field, and that mirror is one cycle behind the running counter
 *          while the strobe alignment costs another - so on a RUNNING
 *          counter a partial write puts the bytes software did not write
 *          BACKWARDS by two counts. With the counter halted the mirror is
 *          stable and the merge is exact. Full-word writes are unaffected:
 *          they replace all four bytes and never read the mirror.
 *
 *   Every other offset in 0x000-0x0FF is reserved: reads return 0, writes
 *   are dropped, and no PSLVERR is raised.
 *
 *   Timer Registers (32-byte blocks starting at 0x100):
 *   ---------------------------------------------------------------
 *   Timer N occupies 0x100 + N*0x20 .. 0x11F + N*0x20:
 *      +0x00: TIMER_CONFIG        - TN_CONF[31:0] (Read/Write)
 *      +0x04: TIMER_INT_ROUTE_CAP - TN_CONF[63:32] (Read-Only, reads 0)
 *      +0x08: TIMER_COMPARATOR_LO - comparator [31:0] (Read/Write)
 *      +0x0C: TIMER_COMPARATOR_HI - comparator [63:32] (Read/Write)
 *      +0x10-0x1F: Reserved - the spec's FSB route registers, not
 *                  implemented (fsb_int_del_cap reads 0)
 *
 *   e.g. Timer 0: 0x100 / 0x104 / 0x108 / 0x10C
 *        Timer 1: 0x120 / 0x124 / 0x128 / 0x12C
 *        Timer 7: 0x1E0 / 0x1E4 / 0x1E8 / 0x1EC (if NUM_TIMERS = 8)
 *
 *   Timer Register Bit Fields:
 *   ---------------------------
 *   TIMER_CONFIG Register (TN_CONF):
 *          [31:16] Reserved
 *          [15]    fsb_int_del_cap - RO, reads 0 (no FSB delivery)
 *          [14]    timer_fsb_en - storage only
 *          [13:9]  timer_int_route - storage only (general I/O APIC
 *                  routing is not implemented)
 *          [8]     timer_32mode - 1 FORCES 32-bit compare, so 64-bit is
 *                  the bit CLEAR. hpet_config_regs drives the core's
 *                  timer_size = ~timer_32mode
 *          [7]     Reserved
 *          [6]     timer_value_set - stored and readable, but NOT consumed
 *                  by any logic. On a real HPET this selects whether a
 *                  periodic comparator write loads the accumulator or the
 *                  period; this core always loads both, so there is
 *                  nothing to select.
 *          [5]     size_cap - RO, reads 1 (64-bit capable)
 *          [4]     per_int_cap - RO, reads 1 (periodic capable)
 *          [3]     timer_type (1=periodic mode, 0=one-shot mode)
 *          [2]     timer_int_enable - gates the INTERRUPT only; a timer is
 *                  live whenever the counter runs, and its HPET_STATUS bit
 *                  is set on every fire either way
 *          [1]     timer_int_type (0=edge, 1=level) - storage only
 *          [0]     Reserved
 *          Reads 0x00000030 out of reset.
 *
 *   TIMER_COMPARATOR_LO Register:
 *          [31:0]  Lower 32 bits of timer comparator value
 *                  In one-shot mode: fires when counter >= comparator
 *                  In periodic mode: initial compare value and period
 *                  Each half loads hpet_core on its own WRITE STROBE, so
 *                  rewriting the same value reloads the comparator; the
 *                  write re-arms the timer only while the counter is
 *                  halted. Readback returns the core's LIVE comparator,
 *                  so in periodic mode it shows the advanced value, not
 *                  the last one written (RLB/hpet TASK-002).
 *
 *   TIMER_COMPARATOR_HI Register:
 *          [31:0]  Upper 32 bits of timer comparator value
 *                  Ignored by the compare when timer_32mode is set
 *
 * ADDRESS SPACE LAYOUT (Fixed 12-bit addressing for all configurations):
 *
 *   Address Range    | Description
 *   -----------------|--------------------------------------------------
 *   0x000-0x0FF      | Global registers (ID, Config, Status, Counter)
 *   0x100-0x11F      | Timer 0 registers
 *   0x120-0x13F      | Timer 1 registers
 *   0x140-0x15F      | Timer 2 registers (if NUM_TIMERS >= 3)
 *   0x160-0x17F      | Timer 3 registers (if NUM_TIMERS >= 4)
 *   0x180-0x19F      | Timer 4 registers (if NUM_TIMERS >= 5)
 *   0x1A0-0x1BF      | Timer 5 registers (if NUM_TIMERS >= 6)
 *   0x1C0-0x1DF      | Timer 6 registers (if NUM_TIMERS >= 7)
 *   0x1E0-0x1FF      | Timer 7 registers (if NUM_TIMERS = 8)
 *   0x200-0xFFF      | Aliases of 0x000-0x1FF (only addr[8:0] decoded)
 *
 * NOTES:
 *   - Fixed 12-bit address width supports up to 4KB address space
 *   - Timer spacing of 32 bytes allows for future expansion
 *   - All configurations (2-8 timers) use the same address map
 *   - TIMER[NUM_TIMERS..7] registers are real decoded storage
 *     (read back written values) but reach no core timer
 * ============================================================================
 */

`timescale 1ns / 1ps

/* verilator lint_off SYNCASYNCNET */
// Note: presetn and hpet_resetn connect to modules with different reset styles.
// hpet_config_regs uses async reset, peakrdl_to_cmdrsp uses sync reset.
// This is intentional - both modules are in same clock domain.
module apb4_hpet #(
    parameter int VENDOR_ID = 1,
    parameter int REVISION_ID = 1,
    parameter int NUM_TIMERS = 2,
    parameter int CDC_ENABLE = 0, // 0=same clock (apb4_slave), 1=different clocks (apb4_slave_cdc)
    // Async-FIFO pointer encoding, forwarded to the CDC block: 0 = Gray
    // (power-of-2 depth only), 1 = Johnson (any depth, DEPTH-bit pointers).
    // Gray by default -- Johnson is opt-in.
    parameter int USE_JOHNSON = 0,
    // GCAP_ID[63:32], femtoseconds per main-counter tick, published read-only at
    // HPET_PERIOD (0x004). MUST be the period of the clock the counter actually
    // ticks on, which is CDC_ENABLE[0] ? hpet_clk : pclk -- pass the matching
    // value per instantiation or software's time conversions are all wrong.
    // Spec: non-zero, <= 0x05F5E100 (100 ns = a 10 MHz floor). 10 ns default.
    parameter int COUNTER_CLK_PERIOD_FS = 10000000
)(
    // ========================================================================
    // Clock and Reset - Dual Domain
    // ========================================================================
    input  logic                    pclk,          // APB clock domain (always used for APB)
    input  logic                    presetn,       // APB reset (active low)
    input  logic                    hpet_clk,      // HPET clock domain (used for timer logic)
    input  logic                    hpet_resetn,   // HPET reset (active low)

    // ========================================================================
    // APB4 Slave Interface (Low Frequency Domain)
    // ========================================================================
    input  logic                    s_apb_PSEL,
    input  logic                    s_apb_PENABLE,
    output logic                    s_apb_PREADY,
    input  logic [11:0]             s_apb_PADDR,   // Fixed 12-bit addressing
    input  logic                    s_apb_PWRITE,
    input  logic [31:0]             s_apb_PWDATA,
    input  logic [3:0]              s_apb_PSTRB,
    input  logic [2:0]              s_apb_PPROT,
    output logic [31:0]             s_apb_PRDATA,
    output logic                    s_apb_PSLVERR,

    // ========================================================================
    // Timer Interrupt Outputs (High Frequency Domain)
    // ========================================================================
    output logic [NUM_TIMERS-1:0]   timer_irq,

    // ========================================================================
    // Legacy Replacement Routes (High Frequency Domain)
    // ========================================================================
    // Asserted only while HPET_CONFIG.legacy_replacement is set, in which case
    // timers 0 and 1 are suppressed on timer_irq above (RLB/hpet TASK-003).
    output logic                    legacy_irq0,
    output logic                    legacy_irq8
);

// ============================================================================
// CDC Command/Response Interface Signals
// ============================================================================
logic                    w_cmd_valid;
logic                    w_cmd_ready;
logic                    w_cmd_pwrite;
logic [11:0]             w_cmd_paddr;     // Fixed 12-bit addressing
logic [31:0]             w_cmd_pwdata;    // Fixed 32-bit data
logic [3:0]              w_cmd_pstrb;
logic [2:0]              w_cmd_pprot;

logic                    w_rsp_valid;
logic                    w_rsp_ready;
logic [31:0]             w_rsp_prdata;    // Fixed 32-bit data
logic                    w_rsp_pslverr;

// ============================================================================
// Configuration Register Interface Signals
// ============================================================================
logic                    w_hpet_enable;
logic                    w_legacy_replacement;
// The four *_write_* strobes below are REGISTERED: they are the outputs of
// ALWAYS_FF_RST blocks inside hpet_config_regs (the aligned rising-edge
// detects on swmod), so they carry the r_ prefix even though the flop itself
// lives one level down. w_counter_rdata / w_timer_int_status stay w_ - those
// are combinational assigns out of hpet_core.
logic                    r_counter_write_lo;
logic                    r_counter_write_hi;
logic [63:0]             w_counter_wdata;
logic [63:0]             w_counter_rdata;
logic [63:0]             w_timer_comp_rdata [NUM_TIMERS];
logic [NUM_TIMERS-1:0]   w_timer_int_enable;
logic [NUM_TIMERS-1:0]   w_timer_type;
logic [NUM_TIMERS-1:0]   w_timer_size;
logic [NUM_TIMERS-1:0]   w_timer_value_set;
logic [NUM_TIMERS-1:0]   r_timer_comp_write_lo;
logic [NUM_TIMERS-1:0]   r_timer_comp_write_hi;
logic [63:0]             w_timer_comp_wdata [NUM_TIMERS];  // Per-timer data bus
logic [NUM_TIMERS-1:0]   w_timer_int_status;
logic [NUM_TIMERS-1:0]   w_timer_int_clear;

// ============================================================================
// APB Slave - CDC or Non-CDC based on parameter
// ============================================================================
generate
    if (CDC_ENABLE != 0) begin : g_apb4_slave_cdc
        // Clock Domain Crossing version for async clocks
        apb4_slave_cdc #(
            .ADDR_WIDTH(12),
            .DATA_WIDTH(32),
            .STRB_WIDTH(4),
            .PROT_WIDTH(3),
            .DEPTH     (2),
            .USE_JOHNSON (USE_JOHNSON)
        ) u_apb4_slave_cdc (
            // APB Clock Domain
            .pclk                 (pclk),
            .presetn              (presetn),

            // HPET Clock Domain
            .aclk                 (hpet_clk),
            .aresetn              (hpet_resetn),

            // APB Interface (pclk domain)
            .s_apb_PSEL           (s_apb_PSEL),
            .s_apb_PENABLE        (s_apb_PENABLE),
            .s_apb_PREADY         (s_apb_PREADY),
            .s_apb_PADDR          (s_apb_PADDR),
            .s_apb_PWRITE         (s_apb_PWRITE),
            .s_apb_PWDATA         (s_apb_PWDATA),
            .s_apb_PSTRB          (s_apb_PSTRB),
            .s_apb_PPROT          (s_apb_PPROT),
            .s_apb_PRDATA         (s_apb_PRDATA),
            .s_apb_PSLVERR        (s_apb_PSLVERR),

            // Command Interface (hpet_clk domain)
            .cmd_valid            (w_cmd_valid),
            .cmd_ready            (w_cmd_ready),
            .cmd_pwrite           (w_cmd_pwrite),
            .cmd_paddr            (w_cmd_paddr),
            .cmd_pwdata           (w_cmd_pwdata),
            .cmd_pstrb            (w_cmd_pstrb),
            .cmd_pprot            (w_cmd_pprot),

            // Response Interface (hpet_clk domain)
            .rsp_valid            (w_rsp_valid),
            .rsp_ready            (w_rsp_ready),
            .rsp_prdata           (w_rsp_prdata),
            .rsp_pslverr          (w_rsp_pslverr)
        );
    end else begin : g_apb4_slave_no_cdc
        // Non-CDC version for same clock domain (pclk == hpet_clk)
        apb4_slave #(
            .ADDR_WIDTH(12),
            .DATA_WIDTH(32),
            .STRB_WIDTH(4),
            .PROT_WIDTH(3)
        ) u_apb4_slave (
            // Single clock domain (use pclk for both APB and cmd/rsp)
            .pclk                 (pclk),
            .presetn              (presetn),

            // APB Interface
            .s_apb_PSEL           (s_apb_PSEL),
            .s_apb_PENABLE        (s_apb_PENABLE),
            .s_apb_PREADY         (s_apb_PREADY),
            .s_apb_PADDR          (s_apb_PADDR),
            .s_apb_PWRITE         (s_apb_PWRITE),
            .s_apb_PWDATA         (s_apb_PWDATA),
            .s_apb_PSTRB          (s_apb_PSTRB),
            .s_apb_PPROT          (s_apb_PPROT),
            .s_apb_PRDATA         (s_apb_PRDATA),
            .s_apb_PSLVERR        (s_apb_PSLVERR),

            // Command Interface (same pclk domain)
            .cmd_valid            (w_cmd_valid),
            .cmd_ready            (w_cmd_ready),
            .cmd_pwrite           (w_cmd_pwrite),
            .cmd_paddr            (w_cmd_paddr),
            .cmd_pwdata           (w_cmd_pwdata),
            .cmd_pstrb            (w_cmd_pstrb),
            .cmd_pprot            (w_cmd_pprot),

            // Response Interface (same pclk domain)
            .rsp_valid            (w_rsp_valid),
            .rsp_ready            (w_rsp_ready),
            .rsp_prdata           (w_rsp_prdata),
            .rsp_pslverr          (w_rsp_pslverr)
        );
    end
endgenerate

// ============================================================================
// HPET Configuration Registers
// CDC_ENABLE=0: Uses pclk (same clock as APB)
// CDC_ENABLE=1: Uses hpet_clk (async clock)
// ============================================================================
hpet_config_regs #(
    .VENDOR_ID             (VENDOR_ID),
    .REVISION_ID           (REVISION_ID),
    .NUM_TIMERS            (NUM_TIMERS),
    .COUNTER_CLK_PERIOD_FS (COUNTER_CLK_PERIOD_FS)
) u_hpet_config_regs (
    // Clock and Reset - conditional based on CDC_ENABLE
    .clk               (CDC_ENABLE[0] ? hpet_clk : pclk),
    .rst_n             (CDC_ENABLE[0] ? hpet_resetn : presetn),

    // Command/Response Interface
    .cmd_valid         (w_cmd_valid),
    .cmd_ready         (w_cmd_ready),
    .cmd_pwrite        (w_cmd_pwrite),
    .cmd_paddr         (w_cmd_paddr),
    .cmd_pwdata        (w_cmd_pwdata),
    .cmd_pstrb         (w_cmd_pstrb),

    .rsp_valid         (w_rsp_valid),
    .rsp_ready         (w_rsp_ready),
    .rsp_prdata        (w_rsp_prdata),
    .rsp_pslverr       (w_rsp_pslverr),

    // HPET Core Interface
    .hpet_enable          (w_hpet_enable),
    .legacy_replacement   (w_legacy_replacement),
    .counter_write_lo     (r_counter_write_lo),
    .counter_write_hi     (r_counter_write_hi),
    .counter_wdata        (w_counter_wdata),
    .counter_rdata        (w_counter_rdata),
    .timer_comp_rdata     (w_timer_comp_rdata),
    .timer_int_enable     (w_timer_int_enable),
    .timer_type           (w_timer_type),
    .timer_size           (w_timer_size),
    .timer_value_set      (w_timer_value_set),
    .timer_comp_write_lo  (r_timer_comp_write_lo),
    .timer_comp_write_hi  (r_timer_comp_write_hi),
    .timer_comp_wdata     (w_timer_comp_wdata),
    .timer_int_status     (w_timer_int_status),
    .timer_int_clear      (w_timer_int_clear)
);

// ============================================================================
// HPET Timer Core
// CDC_ENABLE=0: Uses pclk (same clock as APB)
// CDC_ENABLE=1: Uses hpet_clk (async clock, high speed for precise timing)
// ============================================================================
hpet_core #(
    .NUM_TIMERS(NUM_TIMERS)
) u_hpet_core (
    // Clock and Reset - conditional based on CDC_ENABLE
    .clk                  (CDC_ENABLE[0] ? hpet_clk : pclk),
    .rst_n                (CDC_ENABLE[0] ? hpet_resetn : presetn),

    // Configuration Interface
    .hpet_enable          (w_hpet_enable),
    .legacy_replacement   (w_legacy_replacement),
    .counter_write_lo     (r_counter_write_lo),
    .counter_write_hi     (r_counter_write_hi),
    .counter_wdata        (w_counter_wdata),
    .counter_rdata        (w_counter_rdata),
    .timer_comp_rdata     (w_timer_comp_rdata),
    .timer_int_enable     (w_timer_int_enable),
    .timer_type           (w_timer_type),
    .timer_size           (w_timer_size),
    .timer_comp_write_lo  (r_timer_comp_write_lo),
    .timer_comp_write_hi  (r_timer_comp_write_hi),
    .timer_comp_wdata     (w_timer_comp_wdata),

    // Interrupt Interface
    .timer_int_status     (w_timer_int_status),
    .timer_int_clear      (w_timer_int_clear),
    .timer_irq            (timer_irq),
    .legacy_irq0          (legacy_irq0),
    .legacy_irq8          (legacy_irq8)
);

/* verilator lint_on SYNCASYNCNET */
endmodule : apb4_hpet
