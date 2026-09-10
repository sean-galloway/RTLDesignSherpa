// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: pm_acpi_config_regs
// Purpose: Configuration register wrapper for PM_ACPI - PeakRDL wrapper
//
// Documentation: projects/components/retro_legacy_blocks/rtl/pm_acpi/README.md
// Subsystem: pm_acpi
//
// Author: sean galloway
// Created: 2025-11-16
// Updated: 2026-09-09 - GitHub #54: strict decode with PSLVERR, per-bit W1C
//          mask decode, status fields become live mirrors

/**
 * ============================================================================
 * PM_ACPI Configuration Registers - PeakRDL Wrapper
 * ============================================================================
 *
 * ARCHITECTURE:
 *   cmd/rsp --> peakrdl_to_cmdrsp --> decode gate --> pm_acpi_regs (PeakRDL)
 *                                                 --> hwif --> pm_acpi_core
 *
 * ADDRESS DECODE POLICY (issue #54 round_2 item 4)
 *   Only the twenty-one mapped registers decode. Equality is on the WHOLE
 *   12-bit address, register by register: everything else in the 4 KB window
 *   is DROPPED - the write is ignored, the read returns zero, and PSLVERR is
 *   raised. This is the policy ioapic, pic_8259 and pit_8254 already use.
 *
 *   What it replaces: this module used to hand regblk_addr[8:0] to a 7-bit
 *   s_cpuif_addr port, so only PADDR[6:0] was ever compared and the map
 *   aliased every 0x80 across the window - a write to 'reserved' 0x080 landed
 *   on ACPI_CONTROL. The generated block ties both of its error outputs to 0,
 *   so nothing reported it either.
 *
 *   A dropped access is acknowledged LOCALLY (w_drop_ack) in the same
 *   combinational form the register block uses, because peakrdl_to_cmdrsp
 *   HOLDS its request until it is acked; without the local ack a dropped
 *   access would hang the bus rather than error.
 *
 * PER-BIT W1C (issue #54 C2, round_2 items 1-2)
 *   pm_acpi_core OWNS every sticky status bit. The generated fields are live
 *   mirrors (sw=rw, hw=w, precedence=sw, onwrite=woclr, no hwset), driven from
 *   the core's level every cycle, and the software write is turned into a
 *   per-bit CLEAR PULSE into the core.
 *
 *   The clear mask is `regblk_wr_data & regblk_wr_biten` at the register's own
 *   address, so a bit clears only if software wrote a 1 to it, a write of 0 is
 *   the no-op W1C requires, and a byte-strobed write cannot clear bits outside
 *   the enabled bytes.
 *
 *   The write is detected by MIRRORING the register block's own decode rather
 *   than by using swmod, for the reason gpio_config_regs documents: swmod
 *   carries an extra `|biten` term the regblock's write branch does not, so
 *   the two are not interchangeable as a decode. Nothing in the RTL
 *   cross-checks the mirror; see CHECK BY INSPECTION below for the DV guard.
 *
 *   The clear is narrowed to ONE cycle (rising edge of the mirrored decode).
 *   peakrdl_to_cmdrsp holds regblk_req for the accept cycle plus
 *   CMD_WAIT_ACK, and a two-cycle clear would undo a hardware set that landed
 *   in the first of them; one cycle plus set-wins-over-clear in the core
 *   closes that window.
 *
 * SELF-CLEARING REQUEST BITS
 *   ACPI_CONTROL.soft_reset, PM1_CONTROL.sleep_enable and
 *   RESET_CTRL.sys_reset/periph_reset are `singlepulse` in the RDL, so the
 *   register block clears them itself and this module no longer ties their
 *   `next` inputs to zero to fake an auto-clear. They reach pm_acpi_core as
 *   short levels and are edge-detected there.
 *
 * STORAGE-ONLY FIELDS
 *   ACPI_CONTROL.low_power_req and PM1_CONTROL.pwrbtn_ovr/slpbtn_ovr are
 *   software-visible storage with no hardware effect (issue #54 H3). They are
 *   NOT routed to pm_acpi_core: a register that does nothing should look like
 *   one, not like a connected input nobody reads. Their RDL descriptions say
 *   so as well.
 *
 * CHECK BY INSPECTION (these were assertions; properties belong in external
 * formal bindings, not inside the module)
 *   - Every W1C swmod implies its mirrored decode: ACPI_STATUS.pme_status,
 *     ACPI_INT_STATUS.pme_int, PM1_STATUS.tmr_sts, WAKE_STATUS.gpe_wake and
 *     GPE0_STATUS_LO/HI.gpe_status each imply the matching w_w1c_level bit.
 *     swmod is that same decode ANDed with |wr_biten, so swmod high with the
 *     mirror low is impossible unless the generated block's decode has drifted
 *     from pm_acpi_regs.sv -- at which point W1C silently stops reaching
 *     pm_acpi_core. The guards are pm_acpi_tests_gh54.py::
 *     test_gh54_acpi_status_sticky, ::test_gh54_acpi_int_status_sticky,
 *     ::test_gh54_pm1_status_sticky, ::test_gh54_wake_status_sticky and
 *     ::test_gh54_gpe_status_per_bit_sticky, one per mirrored register.
 *   - No w_w1c_level bit is ever high for three consecutive cycles.
 *     peakrdl_to_cmdrsp holds regblk_req for the accept cycle plus
 *     CMD_WAIT_ACK -- two cycles -- then drops it; three would mean the cpuif
 *     has become pipelined and the rising-edge detect is merging two writes
 *     into one clear. Guarded by
 *     pm_acpi_tests_gh54.py::test_gh54_gpe_status_two_bits_exact and
 *     ::test_gh54_gpe_interrupt_deasserts_after_w1c.
 *   - Every address presented to the register block is one its generated
 *     decode recognises -- the twenty-one ADDR_* localparams below and nothing
 *     else. If the RDL layout drifts from those localparams the access reads
 *     zero and writes nowhere instead of failing. Guarded by
 *     pm_acpi_tests_gh54.py::test_gh54_address_alias_dropped_with_pslverr and
 *     pm_acpi_tests_basic.py::test_register_access, which touches every mapped
 *     address.
 *   - A dropped access never reaches the register block and is always
 *     acknowledged locally: adapter_req && w_drop implies !regblk_req and
 *     implies adapter_rd_ack || adapter_wr_ack. peakrdl_to_cmdrsp HOLDS its
 *     request until it is acked, so a dropped access that is merely gated off
 *     hangs the bus rather than erroring. Guarded by
 *     pm_acpi_tests_gh54.py::test_gh54_address_alias_dropped_with_pslverr,
 *     which would time out rather than fail if the ack were lost.
 * ============================================================================
 */

`timescale 1ns / 1ps

/* verilator lint_off SYNCASYNCNET */
// Note: rst_n feeds both async-reset flops here and peakrdl_to_cmdrsp's
// sync-reset macros. Intentional - both uses are in the same clock domain.

`include "reset_defs.svh"

module pm_acpi_config_regs
    import pm_acpi_regs_pkg::*;
(
    input logic clk,
    input logic rst_n,  // Active-low reset

    // Command/Response Interface (from apb4_slave)
    input  logic        cmd_valid,
    output logic        cmd_ready,
    input  logic        cmd_pwrite,
    input  logic [11:0] cmd_paddr,
    input  logic [31:0] cmd_pwdata,
    input  logic [3:0]  cmd_pstrb,

    output logic        rsp_valid,
    input  logic        rsp_ready,
    output logic [31:0] rsp_prdata,
    output logic        rsp_pslverr,

    // PM_ACPI Core Interface - Configuration Outputs
    output logic        cfg_acpi_enable,
    output logic        cfg_pm_timer_enable,
    output logic        cfg_gpe_enable,
    output logic        cfg_soft_reset,
    output logic [2:0]  cfg_sleep_type,
    output logic        cfg_sleep_enable,
    output logic        cfg_pm1_tmr_en,
    output logic        cfg_pm1_pwrbtn_en,
    output logic        cfg_pm1_slpbtn_en,
    output logic        cfg_pm1_rtc_en,
    output logic [15:0] cfg_pm_timer_div,
    output logic [31:0] cfg_gpe_enables,
    output logic [31:0] cfg_clk_gate_ctrl,
    output logic [7:0]  cfg_pwr_domain_ctrl,
    output logic        cfg_gpe_wake_en,
    output logic        cfg_pwrbtn_wake_en,
    output logic        cfg_rtc_wake_en,
    output logic        cfg_ext_wake_en,
    output logic        cfg_pme_enable,
    output logic        cfg_wake_enable,
    output logic        cfg_timer_ovf_enable,
    output logic        cfg_state_trans_enable,
    output logic        cfg_pm1_enable,
    output logic        cfg_gpe_int_enable,
    output logic        cfg_sys_reset,
    output logic        cfg_periph_reset,

    // Per-bit W1C clear pulses to pm_acpi_core (one cycle per transaction)
    output logic [3:0]  sw_clr_acpi_status,
    output logic [5:0]  sw_clr_acpi_int_status,
    output logic [4:0]  sw_clr_pm1_status,
    output logic [3:0]  sw_clr_wake_status,
    output logic [31:0] sw_clr_gpe_status,

    // Status inputs (from pm_acpi_core) - sticky, mirrored into the regblock
    input  logic [1:0]  status_current_state,
    input  logic [3:0]  status_acpi,
    input  logic [5:0]  status_acpi_int,
    input  logic [4:0]  status_pm1,
    input  logic [3:0]  status_wake_src,
    input  logic [31:0] status_gpe,
    input  logic [3:0]  status_reset_src,
    input  logic [31:0] status_pm_timer_value,
    input  logic [31:0] status_clk_gate_status,
    input  logic [7:0]  status_pwr_domain_status
);

    //========================================================================
    // Local Parameters
    //========================================================================

    // Register offsets, as the generated block decodes them (7 bits). These
    // MUST track pm_acpi_regs.rdl - a_regblk_addr_mapped below is the guard.
    localparam logic [6:0] ADDR_ACPI_CONTROL        = 7'h00;
    localparam logic [6:0] ADDR_ACPI_STATUS         = 7'h04;
    localparam logic [6:0] ADDR_ACPI_INT_ENABLE     = 7'h08;
    localparam logic [6:0] ADDR_ACPI_INT_STATUS     = 7'h0C;
    localparam logic [6:0] ADDR_PM1_CONTROL         = 7'h10;
    localparam logic [6:0] ADDR_PM1_STATUS          = 7'h14;
    localparam logic [6:0] ADDR_PM1_ENABLE          = 7'h18;
    localparam logic [6:0] ADDR_PM_TIMER_VALUE      = 7'h20;
    localparam logic [6:0] ADDR_PM_TIMER_CONFIG     = 7'h24;
    localparam logic [6:0] ADDR_GPE0_STATUS_LO      = 7'h30;
    localparam logic [6:0] ADDR_GPE0_STATUS_HI      = 7'h34;
    localparam logic [6:0] ADDR_GPE0_ENABLE_LO      = 7'h38;
    localparam logic [6:0] ADDR_GPE0_ENABLE_HI      = 7'h3C;
    localparam logic [6:0] ADDR_CLOCK_GATE_CTRL     = 7'h50;
    localparam logic [6:0] ADDR_CLOCK_GATE_STATUS   = 7'h54;
    localparam logic [6:0] ADDR_POWER_DOMAIN_CTRL   = 7'h58;
    localparam logic [6:0] ADDR_POWER_DOMAIN_STATUS = 7'h5C;
    localparam logic [6:0] ADDR_WAKE_STATUS         = 7'h60;
    localparam logic [6:0] ADDR_WAKE_ENABLE         = 7'h64;
    localparam logic [6:0] ADDR_RESET_CTRL          = 7'h68;
    localparam logic [6:0] ADDR_RESET_STATUS        = 7'h6C;

    // The five W1C register windows, one index each. GPE0_STATUS is two
    // registers over one 32-bit core vector, hence six indices.
    localparam int W1C_ACPI_STATUS     = 0;
    localparam int W1C_ACPI_INT_STATUS = 1;
    localparam int W1C_PM1_STATUS      = 2;
    localparam int W1C_WAKE_STATUS     = 3;
    localparam int W1C_GPE_LO          = 4;
    localparam int W1C_GPE_HI          = 5;
    localparam int W1C_COUNT           = 6;

    //========================================================================
    // Signals
    //========================================================================

    // From the protocol adapter, before the decode gate
    logic        adapter_req;
    logic        adapter_req_is_wr;
    logic [11:0] adapter_addr;
    logic [31:0] adapter_wr_data;
    logic [31:0] adapter_wr_biten;
    logic        adapter_req_stall_wr;
    logic        adapter_req_stall_rd;
    logic        adapter_rd_ack;
    logic        adapter_rd_err;
    logic [31:0] adapter_rd_data;
    logic        adapter_wr_ack;
    logic        adapter_wr_err;

    // To the register block, after the decode gate
    logic        regblk_req;
    logic [6:0]  regblk_addr;
    logic        regblk_req_stall_wr;
    logic        regblk_req_stall_rd;
    logic        regblk_rd_ack;
    logic        regblk_rd_err;
    logic [31:0] regblk_rd_data;
    logic        regblk_wr_ack;
    logic        regblk_wr_err;

    // Decode
    logic        w_addr_mapped;
    logic        w_drop;
    logic        w_drop_ack;

    // W1C write detect: mirrored decode level, its delayed copy, the edge
    logic [W1C_COUNT-1:0] w_w1c_level;
    logic [W1C_COUNT-1:0] r_w1c_level_d;
    logic [W1C_COUNT-1:0] w_w1c_event;
    logic [15:0]          w_w1c_mask;

    // Hardware interface structs
    pm_acpi_regs__in_t  hwif_in;
    pm_acpi_regs__out_t hwif_out;

    //========================================================================
    // CMD/RSP to PeakRDL Adapter
    //========================================================================

    peakrdl_to_cmdrsp #(
        .ADDR_WIDTH(12),
        .DATA_WIDTH(32)
    ) u_adapter (
        .aclk               (clk),
        .aresetn            (rst_n),

        // CMD/RSP interface (external)
        .cmd_valid          (cmd_valid),
        .cmd_ready          (cmd_ready),
        .cmd_pwrite         (cmd_pwrite),
        .cmd_paddr          (cmd_paddr),
        .cmd_pwdata         (cmd_pwdata),
        .cmd_pstrb          (cmd_pstrb),

        .rsp_valid          (rsp_valid),
        .rsp_ready          (rsp_ready),
        .rsp_prdata         (rsp_prdata),
        .rsp_pslverr        (rsp_pslverr),

        // PeakRDL passthrough interface (to the decode gate)
        .regblk_req         (adapter_req),
        .regblk_req_is_wr   (adapter_req_is_wr),
        .regblk_addr        (adapter_addr),
        .regblk_wr_data     (adapter_wr_data),
        .regblk_wr_biten    (adapter_wr_biten),
        .regblk_req_stall_wr(adapter_req_stall_wr),
        .regblk_req_stall_rd(adapter_req_stall_rd),
        .regblk_rd_ack      (adapter_rd_ack),
        .regblk_rd_err      (adapter_rd_err),
        .regblk_rd_data     (adapter_rd_data),
        .regblk_wr_ack      (adapter_wr_ack),
        .regblk_wr_err      (adapter_wr_err)
    );

    //========================================================================
    // Strict Address Decode
    //========================================================================
    // Equality on all 12 bits. The 7-bit alias at 0x080 shares its low seven
    // bits with ACPI_CONTROL and is exactly what this rejects.

    always_comb begin
        w_addr_mapped = (adapter_addr == {5'h00, ADDR_ACPI_CONTROL})        ||
                        (adapter_addr == {5'h00, ADDR_ACPI_STATUS})         ||
                        (adapter_addr == {5'h00, ADDR_ACPI_INT_ENABLE})     ||
                        (adapter_addr == {5'h00, ADDR_ACPI_INT_STATUS})     ||
                        (adapter_addr == {5'h00, ADDR_PM1_CONTROL})         ||
                        (adapter_addr == {5'h00, ADDR_PM1_STATUS})          ||
                        (adapter_addr == {5'h00, ADDR_PM1_ENABLE})          ||
                        (adapter_addr == {5'h00, ADDR_PM_TIMER_VALUE})      ||
                        (adapter_addr == {5'h00, ADDR_PM_TIMER_CONFIG})     ||
                        (adapter_addr == {5'h00, ADDR_GPE0_STATUS_LO})      ||
                        (adapter_addr == {5'h00, ADDR_GPE0_STATUS_HI})      ||
                        (adapter_addr == {5'h00, ADDR_GPE0_ENABLE_LO})      ||
                        (adapter_addr == {5'h00, ADDR_GPE0_ENABLE_HI})      ||
                        (adapter_addr == {5'h00, ADDR_CLOCK_GATE_CTRL})     ||
                        (adapter_addr == {5'h00, ADDR_CLOCK_GATE_STATUS})   ||
                        (adapter_addr == {5'h00, ADDR_POWER_DOMAIN_CTRL})   ||
                        (adapter_addr == {5'h00, ADDR_POWER_DOMAIN_STATUS}) ||
                        (adapter_addr == {5'h00, ADDR_WAKE_STATUS})         ||
                        (adapter_addr == {5'h00, ADDR_WAKE_ENABLE})         ||
                        (adapter_addr == {5'h00, ADDR_RESET_CTRL})          ||
                        (adapter_addr == {5'h00, ADDR_RESET_STATUS});
    end

    assign w_drop      = !w_addr_mapped;
    assign regblk_req  = adapter_req && !w_drop;
    assign regblk_addr = adapter_addr[6:0];

    // Local acknowledge for a dropped access, in the same combinational form
    // the register block uses. The adapter holds its request until acked.
    assign w_drop_ack = adapter_req && w_drop;

    assign adapter_req_stall_wr = regblk_req_stall_wr;
    assign adapter_req_stall_rd = regblk_req_stall_rd;
    assign adapter_rd_ack  = regblk_rd_ack | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_err  = regblk_rd_err | (w_drop_ack & ~adapter_req_is_wr);
    assign adapter_rd_data = w_drop_ack ? 32'h0 : regblk_rd_data;
    assign adapter_wr_ack  = regblk_wr_ack | (w_drop_ack & adapter_req_is_wr);
    assign adapter_wr_err  = regblk_wr_err | (w_drop_ack & adapter_req_is_wr);

    //========================================================================
    // Instantiate PeakRDL-Generated Register Block
    //========================================================================

    pm_acpi_regs u_pm_acpi_regs (
        .clk                (clk),
        .rst                (~rst_n),  // PeakRDL uses active-high reset

        // Passthrough CPU interface
        .s_cpuif_req        (regblk_req),
        .s_cpuif_req_is_wr  (adapter_req_is_wr),
        .s_cpuif_addr       (regblk_addr),
        .s_cpuif_wr_data    (adapter_wr_data),
        .s_cpuif_wr_biten   (adapter_wr_biten),
        .s_cpuif_req_stall_wr(regblk_req_stall_wr),
        .s_cpuif_req_stall_rd(regblk_req_stall_rd),
        .s_cpuif_rd_ack     (regblk_rd_ack),
        .s_cpuif_rd_err     (regblk_rd_err),
        .s_cpuif_rd_data    (regblk_rd_data),
        .s_cpuif_wr_ack     (regblk_wr_ack),
        .s_cpuif_wr_err     (regblk_wr_err),

        // Hardware interface
        .hwif_in            (hwif_in),
        .hwif_out           (hwif_out)
    );

    //========================================================================
    // hwif_out -> pm_acpi_core Configuration
    //========================================================================

    // ACPI Control register
    assign cfg_acpi_enable     = hwif_out.ACPI_CONTROL.acpi_enable.value;
    assign cfg_pm_timer_enable = hwif_out.ACPI_CONTROL.pm_timer_enable.value;
    assign cfg_gpe_enable      = hwif_out.ACPI_CONTROL.gpe_enable.value;
    assign cfg_soft_reset      = hwif_out.ACPI_CONTROL.soft_reset.value;

    // PM1 Control register. pwrbtn_ovr / slpbtn_ovr are storage only and are
    // deliberately not read here (see the header).
    assign cfg_sleep_type   = hwif_out.PM1_CONTROL.sleep_type.value;
    assign cfg_sleep_enable = hwif_out.PM1_CONTROL.sleep_enable.value;

    // PM1 Enable register
    assign cfg_pm1_tmr_en    = hwif_out.PM1_ENABLE.tmr_en.value;
    assign cfg_pm1_pwrbtn_en = hwif_out.PM1_ENABLE.pwrbtn_en.value;
    assign cfg_pm1_slpbtn_en = hwif_out.PM1_ENABLE.slpbtn_en.value;
    assign cfg_pm1_rtc_en    = hwif_out.PM1_ENABLE.rtc_en.value;

    // PM Timer configuration
    assign cfg_pm_timer_div = hwif_out.PM_TIMER_CONFIG.timer_div.value;

    // GPE enables (HI concatenated above LO - the same order status_gpe uses)
    assign cfg_gpe_enables = {hwif_out.GPE0_ENABLE_HI.gpe_enable.value,
                              hwif_out.GPE0_ENABLE_LO.gpe_enable.value};

    // Clock gate and power domain control
    assign cfg_clk_gate_ctrl   = hwif_out.CLOCK_GATE_CTRL.clk_gate_ctrl.value;
    assign cfg_pwr_domain_ctrl = hwif_out.POWER_DOMAIN_CTRL.pwr_domain_ctrl.value;

    // Wake enables
    assign cfg_gpe_wake_en    = hwif_out.WAKE_ENABLE.gpe_wake_en.value;
    assign cfg_pwrbtn_wake_en = hwif_out.WAKE_ENABLE.pwrbtn_wake_en.value;
    assign cfg_rtc_wake_en    = hwif_out.WAKE_ENABLE.rtc_wake_en.value;
    assign cfg_ext_wake_en    = hwif_out.WAKE_ENABLE.ext_wake_en.value;

    // Interrupt enables
    assign cfg_pme_enable         = hwif_out.ACPI_INT_ENABLE.pme_enable.value;
    assign cfg_wake_enable        = hwif_out.ACPI_INT_ENABLE.wake_enable.value;
    assign cfg_timer_ovf_enable   = hwif_out.ACPI_INT_ENABLE.timer_ovf_enable.value;
    assign cfg_state_trans_enable = hwif_out.ACPI_INT_ENABLE.state_trans_enable.value;
    assign cfg_pm1_enable         = hwif_out.ACPI_INT_ENABLE.pm1_enable.value;
    assign cfg_gpe_int_enable     = hwif_out.ACPI_INT_ENABLE.gpe_int_enable.value;

    // Reset control requests
    assign cfg_sys_reset    = hwif_out.RESET_CTRL.sys_reset.value;
    assign cfg_periph_reset = hwif_out.RESET_CTRL.periph_reset.value;

    //========================================================================
    // W1C Write Decode - mirror of the register block's own decode
    //========================================================================
    // pm_acpi_regs.sv decodes
    //   decoded_reg_strb.<REG> = cpuif_req_masked & (cpuif_addr == <ADDR>)
    // on the same seven address bits this module feeds it, and both cpuif
    // stalls are tied low inside the block, so cpuif_req_masked == regblk_req.
    // a_w1c_swmod_mirrored fires if a regenerated block changes that decode.

    always_comb begin
        w_w1c_level = '0;
        w_w1c_level[W1C_ACPI_STATUS]     = regblk_req && adapter_req_is_wr &&
                                           (regblk_addr == ADDR_ACPI_STATUS);
        w_w1c_level[W1C_ACPI_INT_STATUS] = regblk_req && adapter_req_is_wr &&
                                           (regblk_addr == ADDR_ACPI_INT_STATUS);
        w_w1c_level[W1C_PM1_STATUS]      = regblk_req && adapter_req_is_wr &&
                                           (regblk_addr == ADDR_PM1_STATUS);
        w_w1c_level[W1C_WAKE_STATUS]     = regblk_req && adapter_req_is_wr &&
                                           (regblk_addr == ADDR_WAKE_STATUS);
        w_w1c_level[W1C_GPE_LO]          = regblk_req && adapter_req_is_wr &&
                                           (regblk_addr == ADDR_GPE0_STATUS_LO);
        w_w1c_level[W1C_GPE_HI]          = regblk_req && adapter_req_is_wr &&
                                           (regblk_addr == ADDR_GPE0_STATUS_HI);
    end

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_w1c_level_d <= '0;
        end else begin
            r_w1c_level_d <= w_w1c_level;
        end
    )

    // One clear event per transaction: the request is held for the whole
    // transaction, and a two-cycle clear would undo a set the core accepted in
    // the first of them.
    assign w_w1c_event = w_w1c_level & ~r_w1c_level_d;

    // The write data and byte enables are combinational into the register
    // block's decode, so during the request they ARE the mask of the write
    // being committed.
    // Only the low half-word is ever needed: the widest W1C field group is
    // GPE0_STATUS_LO/HI at 16 bits, and every other status register fits in
    // six. Taking the full word would leave the top half unread.
    assign w_w1c_mask = adapter_wr_data[15:0] & adapter_wr_biten[15:0];

    assign sw_clr_acpi_status     = w_w1c_event[W1C_ACPI_STATUS]     ?
                                    w_w1c_mask[3:0] : 4'h0;
    assign sw_clr_acpi_int_status = w_w1c_event[W1C_ACPI_INT_STATUS] ?
                                    w_w1c_mask[5:0] : 6'h0;
    assign sw_clr_pm1_status      = w_w1c_event[W1C_PM1_STATUS]      ?
                                    w_w1c_mask[4:0] : 5'h0;
    assign sw_clr_wake_status     = w_w1c_event[W1C_WAKE_STATUS]     ?
                                    w_w1c_mask[3:0] : 4'h0;

    // GPE0_STATUS_HI carries core bits [31:16] in its OWN bits [15:0]; the two
    // halves are independent transactions and are never written together.
    assign sw_clr_gpe_status[15:0]  = w_w1c_event[W1C_GPE_LO] ?
                                      w_w1c_mask[15:0] : 16'h0;
    assign sw_clr_gpe_status[31:16] = w_w1c_event[W1C_GPE_HI] ?
                                      w_w1c_mask[15:0] : 16'h0;

    //========================================================================
    // pm_acpi_core -> hwif_in (every member of pm_acpi_regs__in_t is driven)
    //========================================================================

    // ACPI Control - current power state
    assign hwif_in.ACPI_CONTROL.current_state.next = status_current_state;

    // ACPI_STATUS mirror (bit order matches pm_acpi_core's STATUS BIT MAP)
    assign hwif_in.ACPI_STATUS.pme_status.next      = status_acpi[0];
    assign hwif_in.ACPI_STATUS.wake_status.next     = status_acpi[1];
    assign hwif_in.ACPI_STATUS.timer_overflow.next  = status_acpi[2];
    assign hwif_in.ACPI_STATUS.state_transition.next = status_acpi[3];

    // ACPI_INT_STATUS mirror
    assign hwif_in.ACPI_INT_STATUS.pme_int.next         = status_acpi_int[0];
    assign hwif_in.ACPI_INT_STATUS.wake_int.next        = status_acpi_int[1];
    assign hwif_in.ACPI_INT_STATUS.timer_ovf_int.next   = status_acpi_int[2];
    assign hwif_in.ACPI_INT_STATUS.state_trans_int.next = status_acpi_int[3];
    assign hwif_in.ACPI_INT_STATUS.pm1_int.next         = status_acpi_int[4];
    assign hwif_in.ACPI_INT_STATUS.gpe_int.next         = status_acpi_int[5];

    // PM1_STATUS mirror
    assign hwif_in.PM1_STATUS.tmr_sts.next    = status_pm1[0];
    assign hwif_in.PM1_STATUS.pwrbtn_sts.next = status_pm1[1];
    assign hwif_in.PM1_STATUS.slpbtn_sts.next = status_pm1[2];
    assign hwif_in.PM1_STATUS.rtc_sts.next    = status_pm1[3];
    assign hwif_in.PM1_STATUS.wak_sts.next    = status_pm1[4];

    // WAKE_STATUS mirror
    assign hwif_in.WAKE_STATUS.gpe_wake.next    = status_wake_src[0];
    assign hwif_in.WAKE_STATUS.pwrbtn_wake.next = status_wake_src[1];
    assign hwif_in.WAKE_STATUS.rtc_wake.next    = status_wake_src[2];
    assign hwif_in.WAKE_STATUS.ext_wake.next    = status_wake_src[3];

    // GPE0_STATUS mirror (LO = core [15:0], HI = core [31:16])
    assign hwif_in.GPE0_STATUS_LO.gpe_status.next = status_gpe[15:0];
    assign hwif_in.GPE0_STATUS_HI.gpe_status.next = status_gpe[31:16];

    // RESET_STATUS mirror
    assign hwif_in.RESET_STATUS.por_reset.next = status_reset_src[0];
    assign hwif_in.RESET_STATUS.wdt_reset.next = status_reset_src[1];
    assign hwif_in.RESET_STATUS.sw_reset.next  = status_reset_src[2];
    assign hwif_in.RESET_STATUS.ext_reset.next = status_reset_src[3];

    // Read-only hardware mirrors
    assign hwif_in.PM_TIMER_VALUE.timer_value.next          = status_pm_timer_value;
    assign hwif_in.CLOCK_GATE_STATUS.clk_gate_status.next   = status_clk_gate_status;
    assign hwif_in.POWER_DOMAIN_STATUS.pwr_domain_status.next = status_pwr_domain_status;

/* verilator lint_on SYNCASYNCNET */
endmodule : pm_acpi_config_regs
