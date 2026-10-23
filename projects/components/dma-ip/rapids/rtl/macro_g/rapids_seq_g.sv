// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: rapids_seq_g
// Purpose: The rapids-g sequencer (rapids TASK-034): ONE gatling barrel core
//          running the scheduler firmware for 4 or 8 scheduler_g channels.
//
// Mapping.  Hart h serves slot s = channel h + NUM_HARTS*s.  By default
// NUM_HARTS = NUM_CHANNELS, one hart per channel and one slot each; with
// NUM_HARTS = 4 at 8 channels each hart serves two slots.  Every hart runs
// the SAME image -- contexts
// stay implicit (gatling PRD 7 item 2): the slot windows and the scratch are
// aliased by the context the access comes from, so "slot 0" is a different
// channel for each hart and no code ever names a hart.
//
// Memory map (byte addresses; dmem):
//   0x0000_0000  instruction ROM (fetch only; a data access reads 0)
//   0x1000_0000  slot 0 window, 0x1000_0100 slot 1 window: scheduler_g's
//                word-indexed register window, 32 words (scheduler_g header)
//   0x1000_1000  SUMMARY  [NUM_SLOTS-1:0] attn of this hart's slots
//   0x1000_1004  SLOTS    number of slots per hart (1 or 2)
//   0x1000_3000  register mailbox (aliased by context): this half's PeakRDL
//                registers through the host's command queue (rapids_g_reg_arb)
//                  +0x00 W REG_ADDR   [11:0] byte offset in this half
//                  +0x04 W REG_WDATA
//                  +0x08 W REG_CTRL   [0] go  [1] write
//                  +0x0C R REG_STATUS [0] busy  [1] done  [2] error
//                  +0x10 R REG_RDATA
//                A hart posts one access, polls STATUS, then reads RDATA; the
//                harts' accesses go out one at a time, round robin.
//   0x2000_0000  scratch, SCRATCH_WORDS words per hart (aliased by context)
// Every access has one stage of latency, as gatling requires (no wait):
// reads are registered (address in X, data in W), writes are registered
// into the scheduler window one cycle after X -- a hart's next instruction
// is NUM_HARTS (at least four) cycles later, so it always sees its own write.
//
// Faults.  A hart that halts (trap, illegal instruction) faults its channels:
// seq_fault makes scheduler_g force CH_ERROR, so the scheduler's existing
// error MonBus packet reports it.  The hart restarts from RESET_ADDR once
// every channel it serves is in reset.
//
// Restart.  A pulse on seq_restart resets the whole gatling (its reset
// synchronizer, so the release is clean): the barrel rotation and every
// hart's PC start over, and the harts reach the idle loop a fixed number of
// clocks after the pulse.  Without it the poll loop's phase at a given
// moment depends on how many clocks have passed since reset, and with it how
// soon each hart notices a new descriptor.  A test harness pulses it on its
// launch so a run's timing is the same in simulation and on the board.  Pulse
// it only while every channel is idle: the firmware keeps no state across an
// idle channel, but a hart restarted mid-service drops what it was doing.
// Tie it to 0 otherwise.
//
// Firmware.  rtl/macro_g/generated/fw/sched_g_fw.svh, generated from
// fw_g/sched_g.S by bin/gen_rapids_g_fw.py (never hand-edited).
//
// Parameters:
//   - NUM_CHANNELS: 4 or 8
//   - NUM_HARTS: gatling contexts, 4 or 8, at most NUM_CHANNELS and dividing
//     it; default NUM_CHANNELS (one hart per channel).  Each hart issues one
//     instruction every NUM_HARTS clocks, the core one per clock in total.
//   - IMEM_WORDS: instruction ROM depth (words); the image must fit
//   - SCRATCH_WORDS: scratch words per hart, power of 2; the firmware keeps
//     64 words per slot (sched_g.S SLOT_STRIDE), so NUM_SLOTS * 64 at least
//
// Documentation: projects/components/dma-ip/rapids/docs/rapids_mas (rapids-g)
// Subsystem: rapids macro_g
//
// Author: sean galloway
// Created: 2026-10-21

`timescale 1ns / 1ps

`include "reset_defs.svh"

module rapids_seq_g #(
    parameter int NUM_CHANNELS  = 8,
    parameter int NUM_HARTS     = NUM_CHANNELS,
    parameter int IMEM_WORDS    = 1024,
    parameter int SCRATCH_WORDS = 128
) (
    input  logic                            clk,
    input  logic                            rst_n,

    input  logic                            seq_restart,        // one cycle: restart every hart
    input  logic [NUM_CHANNELS-1:0]         cfg_channel_reset,

    // scheduler_g windows: address and write data are broadcast, the write
    // enable and the read data are per channel
    output logic [NUM_CHANNELS-1:0]         seq_wr_en,
    output logic [4:0]                      seq_wr_addr,
    output logic [31:0]                     seq_wr_data,
    output logic [4:0]                      seq_rd_addr,
    input  logic [NUM_CHANNELS-1:0][31:0]   seq_rd_data,
    input  logic [NUM_CHANNELS-1:0]         seq_attn,
    output logic [NUM_CHANNELS-1:0]         seq_fault,

    // This half's register block, through the host's command queue
    output logic                            reg_cmd_valid,
    input  logic                            reg_cmd_ready,
    output logic                            reg_cmd_pwrite,
    output logic [11:0]                     reg_cmd_paddr,      // byte offset within the half
    output logic [31:0]                     reg_cmd_pwdata,
    input  logic                            reg_rsp_valid,
    output logic                            reg_rsp_ready,
    input  logic [31:0]                     reg_rsp_prdata,
    input  logic                            reg_rsp_pslverr,

    // Observability
    output logic [NUM_HARTS-1:0]            hart_halted
);

    localparam int NUM_SLOTS = NUM_CHANNELS / NUM_HARTS;
    localparam int HART_W    = $clog2(NUM_HARTS);
    localparam int IMEM_AW   = $clog2(IMEM_WORDS);
    localparam int SCR_AW    = $clog2(SCRATCH_WORDS);

    // The firmware image: localparam FW_WORDS, FW_IMAGE[FW_WORDS]
    `include "sched_g_fw.svh"

    initial begin
        if ((NUM_CHANNELS != 4) && (NUM_CHANNELS != 8))
            $fatal(1, "rapids_seq_g: NUM_CHANNELS must be 4 or 8, got %0d", NUM_CHANNELS);
        if (((NUM_HARTS != 4) && (NUM_HARTS != 8)) || (NUM_HARTS > NUM_CHANNELS) || ((NUM_CHANNELS % NUM_HARTS) != 0))
            $fatal(1, "rapids_seq_g: NUM_HARTS %0d must be 4 or 8 and divide NUM_CHANNELS %0d",
                   NUM_HARTS, NUM_CHANNELS);
        if (FW_WORDS > IMEM_WORDS)
            $fatal(1, "rapids_seq_g: firmware is %0d words, ROM is %0d", FW_WORDS, IMEM_WORDS);
        if ((1 << SCR_AW) != SCRATCH_WORDS)
            $fatal(1, "rapids_seq_g: SCRATCH_WORDS must be a power of 2, got %0d", SCRATCH_WORDS);
        // A smaller scratch aliases slot 1 onto slot 0 (the address decode
        // drops the upper bits), and the two channels share EXT state.
        if (SCRATCH_WORDS < NUM_SLOTS * 64)
            $fatal(1, "rapids_seq_g: SCRATCH_WORDS %0d < %0d slots x 64 words", SCRATCH_WORDS, NUM_SLOTS);
    end

    //=========================================================================
    // gatling
    //=========================================================================

    logic [NUM_HARTS-1:0] w_hart_run, w_halted;
    logic [HART_W-1:0] w_imem_ctx;
    logic [31:0]       w_imem_addr;
    logic [31:0]       r_imem_rdata;
    logic              w_dmem_req;
    logic [HART_W-1:0] w_dmem_ctx;
    logic [31:0]       w_dmem_addr;
    logic [31:0]       w_dmem_rdata;
    logic [3:0]        w_dmem_wstrb;
    logic [31:0]       w_dmem_wdata;

    // The restart: registered, so the gatling's reset input sees a flop and
    // the system reset, never a decode
    logic r_restart;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) r_restart <= 1'b0;
        else                      r_restart <= seq_restart;
    )

    wire w_gatling_rst_n = rst_n && !r_restart;

    gatling_core #(
        .NUM_HARTS  (NUM_HARTS),
        .RESET_ADDR (32'h0000_0000)
    ) u_gatling (
        .clk            (clk),
        .rst_n          (w_gatling_rst_n),
        .hart_run       (w_hart_run),
        .imem_ctx       (w_imem_ctx),
        .imem_addr      (w_imem_addr),
        .imem_rdata     (r_imem_rdata),
        .dmem_req       (w_dmem_req),
        .dmem_ctx       (w_dmem_ctx),
        .dmem_addr      (w_dmem_addr),
        .dmem_rdata     (w_dmem_rdata),
        .dmem_wstrb     (w_dmem_wstrb),
        .dmem_wdata     (w_dmem_wdata),
        .halted         (w_halted),
        .halt_cause     (),
        .rvfi_valid     (),
        .rvfi_ctx       (),
        .rvfi_order     (),
        .rvfi_pc_rdata  (),
        .rvfi_pc_wdata  (),
        .rvfi_insn      (),
        .rvfi_trap      (),
        .rvfi_rs1_addr  (),
        .rvfi_rs2_addr  (),
        .rvfi_rs1_rdata (),
        .rvfi_rs2_rdata (),
        .rvfi_rd_addr   (),
        .rvfi_rd_wdata  (),
        .rvfi_mem_addr  (),
        .rvfi_mem_rmask (),
        .rvfi_mem_wmask (),
        .rvfi_mem_rdata (),
        .rvfi_mem_wdata ()
    );

    assign hart_halted = w_halted;

    // A halted hart restarts once every channel it serves is in reset
    always_comb begin
        for (int h = 0; h < NUM_HARTS; h++) begin
            logic all_reset;
            all_reset = 1'b1;
            for (int s = 0; s < NUM_SLOTS; s++) begin
                all_reset = all_reset && cfg_channel_reset[h + NUM_HARTS*s];
            end
            w_hart_run[h] = !(w_halted[h] && all_reset);
        end
    end

    always_comb begin
        for (int c = 0; c < NUM_CHANNELS; c++) begin
            seq_fault[c] = w_halted[c % NUM_HARTS];
        end
    end

    //=========================================================================
    // Instruction ROM: one port, one fetch per cycle (the barrel fetches for
    // one context per cycle, and every context runs the same image)
    //=========================================================================

    logic [31:0] r_rom [IMEM_WORDS];

    initial begin
        for (int i = 0; i < IMEM_WORDS; i++) begin
            r_rom[i] = (i < FW_WORDS) ? FW_IMAGE[i] : 32'h0000_0000;
        end
    end

    always_ff @(posedge clk) begin
        r_imem_rdata <= r_rom[w_imem_addr[IMEM_AW+1:2]];
    end

    //=========================================================================
    // Data side: decode (X), registered response (W)
    //=========================================================================

    localparam logic [1:0] RGN_ROM  = 2'd0;
    localparam logic [1:0] RGN_MMIO = 2'd1;
    localparam logic [1:0] RGN_SCR  = 2'd2;

    wire [1:0] w_rgn    = w_dmem_addr[29:28];
    wire       w_global = w_dmem_addr[12];
    wire       w_mbox   = w_dmem_addr[13];               // 0x1000_3000: with w_global
    wire       w_slot   = w_dmem_addr[8];
    wire       w_store  = w_dmem_req && (w_dmem_wstrb != 4'h0);
    wire       w_load   = w_dmem_req && (w_dmem_wstrb == 4'h0);

    // Channel of (context, slot); a slot past NUM_SLOTS is absent
    function automatic int chan_of(input logic [HART_W-1:0] ctx, input logic slot);
        return int'(ctx) + NUM_HARTS * int'(slot);
    endfunction
    wire w_slot_ok = (int'(w_slot) < NUM_SLOTS);

    // Scheduler window writes, registered
    logic                     r_wr_en;
    logic [$clog2(NUM_CHANNELS)-1:0] r_wr_ch;
    logic [4:0]               r_wr_addr;
    logic [31:0]              r_wr_data;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_wr_en   <= 1'b0;
            r_wr_ch   <= '0;
            r_wr_addr <= 5'h0;
            r_wr_data <= 32'h0;
        end else begin
            r_wr_en   <= w_store && (w_rgn == RGN_MMIO) && !w_global && w_slot_ok;
            r_wr_ch   <= $clog2(NUM_CHANNELS)'(chan_of(w_dmem_ctx, w_slot));
            r_wr_addr <= w_dmem_addr[6:2];
            r_wr_data <= w_dmem_wdata;
        end
    )

    always_comb begin
        seq_wr_en = '0;
        seq_wr_en[r_wr_ch] = r_wr_en;
    end
    assign seq_wr_addr = r_wr_addr;
    assign seq_wr_data = r_wr_data;

    //=========================================================================
    // Register mailbox: one per hart, one access out at a time
    //=========================================================================
    logic [NUM_HARTS-1:0][11:0] r_mb_addr;
    logic [NUM_HARTS-1:0][31:0] r_mb_wdata, r_mb_rdata;
    logic [NUM_HARTS-1:0]       r_mb_wr, r_mb_busy, r_mb_done, r_mb_err;
    logic [NUM_HARTS-1:0]       w_mb_gnt;
    logic [HART_W-1:0]          w_mb_gnt_id;
    logic                       w_mb_gnt_valid, r_mb_sent;
    logic [NUM_HARTS-1:0]       w_mb_ack;

    wire w_mb_store = w_store && (w_rgn == RGN_MMIO) && w_global && w_mbox;

    arbiter_round_robin_simple_ack #(
        .N (NUM_HARTS)
    ) u_mb_arb (
        .clk         (clk),
        .rst_n       (rst_n),
        .request     (r_mb_busy),
        .grant_ack   (w_mb_ack),
        .grant_valid (w_mb_gnt_valid),
        .grant       (w_mb_gnt),
        .grant_id    (w_mb_gnt_id)
    );

    assign reg_cmd_valid  = w_mb_gnt_valid && !r_mb_sent && r_mb_busy[w_mb_gnt_id];
    assign reg_cmd_pwrite = r_mb_wr[w_mb_gnt_id];
    assign reg_cmd_paddr  = r_mb_addr[w_mb_gnt_id];
    assign reg_cmd_pwdata = r_mb_wdata[w_mb_gnt_id];
    assign reg_rsp_ready  = w_mb_gnt_valid && r_mb_sent;
    assign w_mb_ack       = (reg_rsp_valid && reg_rsp_ready) ? w_mb_gnt : '0;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_mb_addr  <= '0;
            r_mb_wdata <= '0;
            r_mb_rdata <= '0;
            r_mb_wr    <= '0;
            r_mb_busy  <= '0;
            r_mb_done  <= '0;
            r_mb_err   <= '0;
            r_mb_sent  <= 1'b0;
        end else begin
            if (reg_rsp_valid && reg_rsp_ready) begin
                r_mb_sent                <= 1'b0;
                r_mb_busy[w_mb_gnt_id]   <= 1'b0;
                r_mb_done[w_mb_gnt_id]   <= 1'b1;
                r_mb_err[w_mb_gnt_id]    <= reg_rsp_pslverr;
                r_mb_rdata[w_mb_gnt_id]  <= reg_rsp_prdata;
            end else if (reg_cmd_valid && reg_cmd_ready) begin
                r_mb_sent <= 1'b1;
            end
            if (w_mb_store && !r_mb_busy[w_dmem_ctx]) begin
                case (w_dmem_addr[4:2])
                    3'd0: r_mb_addr[w_dmem_ctx]  <= w_dmem_wdata[11:0];
                    3'd1: r_mb_wdata[w_dmem_ctx] <= w_dmem_wdata;
                    3'd2: if (w_dmem_wdata[0]) begin                 // go
                              r_mb_wr[w_dmem_ctx]   <= w_dmem_wdata[1];
                              r_mb_busy[w_dmem_ctx] <= 1'b1;
                              r_mb_done[w_dmem_ctx] <= 1'b0;
                              r_mb_err[w_dmem_ctx]  <= 1'b0;
                          end
                    default: ;
                endcase
            end
        end
    )

    // Window reads: the word index is broadcast; pick the channel here
    assign seq_rd_addr = w_dmem_addr[6:2];

    logic [NUM_SLOTS-1:0] w_summary;
    always_comb begin
        for (int s = 0; s < NUM_SLOTS; s++) begin
            w_summary[s] = seq_attn[chan_of(w_dmem_ctx, 1'(s))];
        end
    end

    logic [31:0] w_mmio_rdata;
    always_comb begin
        w_mmio_rdata = 32'h0;
        if (w_global && w_mbox) begin
            case (w_dmem_addr[4:2])
                3'd3:    w_mmio_rdata = {29'h0, r_mb_err[w_dmem_ctx], r_mb_done[w_dmem_ctx], r_mb_busy[w_dmem_ctx]};
                3'd4:    w_mmio_rdata = r_mb_rdata[w_dmem_ctx];
                default: w_mmio_rdata = 32'h0;
            endcase
        end else if (w_global) begin
            case (w_dmem_addr[3:2])
                2'd0:    w_mmio_rdata = 32'(w_summary);
                2'd1:    w_mmio_rdata = 32'(NUM_SLOTS);
                default: w_mmio_rdata = 32'h0;
            endcase
        end else if (w_slot_ok) begin
            w_mmio_rdata = seq_rd_data[chan_of(w_dmem_ctx, w_slot)];
        end
    end

    // Scratch: one block RAM, indexed {context, word}
    `ifdef XILINX
        (* ram_style = "auto" *)
    `elsif SYNTH_PRAGMA
        /* synthesis ramstyle = "AUTO" */
    `endif
    logic [31:0] r_scratch [NUM_HARTS * SCRATCH_WORDS];

    wire [HART_W+SCR_AW-1:0] w_scr_idx = {w_dmem_ctx, w_dmem_addr[SCR_AW+1:2]};
    logic [31:0] r_scr_rdata;

    always_ff @(posedge clk) begin
        if (w_store && (w_rgn == RGN_SCR)) begin
            for (int b = 0; b < 4; b++) begin
                if (w_dmem_wstrb[b]) r_scratch[w_scr_idx][8*b +: 8] <= w_dmem_wdata[8*b +: 8];
            end
        end
        r_scr_rdata <= r_scratch[w_scr_idx];
    end

    logic [1:0]  r_rd_rgn;
    logic [31:0] r_mmio_rdata;

    `ALWAYS_FF_RST(clk, rst_n,
        if (`RST_ASSERTED(rst_n)) begin
            r_rd_rgn     <= RGN_ROM;
            r_mmio_rdata <= 32'h0;
        end else begin
            r_rd_rgn     <= w_load ? w_rgn : RGN_ROM;
            r_mmio_rdata <= (w_load && (w_rgn == RGN_MMIO)) ? w_mmio_rdata : 32'h0;
        end
    )

    assign w_dmem_rdata = (r_rd_rgn == RGN_SCR)  ? r_scr_rdata  :
                          (r_rd_rgn == RGN_MMIO) ? r_mmio_rdata : 32'h0;

endmodule : rapids_seq_g
