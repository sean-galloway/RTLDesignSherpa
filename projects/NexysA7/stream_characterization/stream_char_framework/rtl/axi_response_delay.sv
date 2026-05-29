// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: axi_response_delay
// Purpose: Pipelined memory-controller delay model for an AXI response
//          channel (R-data or B-resp).
//
// Description:
//   Models a real memory controller (DDR, HBM, on-chip SRAM controller,
//   etc.) where every request pays a fixed access latency L, but L
//   *overlaps* across pipelined requests. Concretely:
//
//     - Each beat presented on the slave side enters a queue with a
//       timestamp.
//     - The beat is released to the master side exactly i_delay_cycles
//       cycles after it was admitted.
//     - Up to CAPACITY beats can be in flight simultaneously. Once the
//       queue is full, s_ready drops, naturally back-pressuring the
//       slave model — that mirrors a controller running out of in-flight
//       slots.
//
//   By Little's Law, sustained throughput is min(1, N/L) beats/cycle,
//   where N is the number of beats the master has outstanding. So
//   throughput is decoupled from L as long as the master keeps the pipe
//   full (which is exactly what AXI multi-outstanding is for).
//
//   Concretely: with AR_MAX_OUTSTANDING=8 and 16-beat bursts, the master
//   keeps up to 128 beats in flight. As long as CAPACITY ≥ 128, every
//   beat is admitted on arrival, dwells L cycles, and emerges at line
//   rate after the initial fill. Throughput stays at 1 beat/cycle for
//   any L up to where the queue fills (pipeline-limited).
//
// Interface:
//   - i_delay_cycles : runtime-programmable per-beat latency (in aclk
//                      cycles). 0 → 1-cycle minimum (FIFO register
//                      stage); N → N cycles end-to-end.
//   - s_valid/s_ready/s_data : slave-side ingress.
//   - m_valid/m_ready/m_data : master-side egress.
//
// Parameters:
//   DATA_WIDTH : payload width (R: data+id+resp+last+user, B: id+resp+user).
//   DELAY_W    : width of i_delay_cycles register.
//   CAPACITY   : maximum beats in flight. MUST be a power of 2 ≥ 2 so
//                head/tail pointers wrap by truncation.
//                  - R channel: ≥ AR_MAX_OUTSTANDING × max_burst_len
//                  - B channel: ≥ AW_MAX_OUTSTANDING
//
// Notes:
//   - Strict FIFO drain — preserves response ordering at this point in
//     the path. AXI per-ID ordering is enforced upstream by the slave.
//   - Minimum end-to-end latency is 1 aclk cycle (a real controller
//     always has at least one register stage, so this is realistic).
//   - i_delay_cycles is sampled per drain decision, not per admission,
//     so changing it mid-flight will affect in-queue beats. In normal
//     operation the value is held constant for an entire test.

`timescale 1ns / 1ps

`include "reset_defs.svh"

module axi_response_delay #(
    parameter int DATA_WIDTH = 128,
    parameter int DELAY_W    = 16,
    parameter int CAPACITY   = 256
) (
    input  logic                    aclk,
    input  logic                    aresetn,

    // Per-beat fixed latency, in aclk cycles. 0 → 1-cycle pass-through.
    input  logic [DELAY_W-1:0]      i_delay_cycles,

    // Slave-facing input
    input  logic [DATA_WIDTH-1:0]   s_data,
    input  logic                    s_valid,
    output logic                    s_ready,

    // Master-facing output
    output logic [DATA_WIDTH-1:0]   m_data,
    output logic                    m_valid,
    input  logic                    m_ready
);

    // ---- Sanity check ------------------------------------------------------
    // CAPACITY must be a power of 2 ≥ 2 so the index pointers wrap by
    // truncation (no comparison logic needed in the increment path).
    initial begin
        if ((CAPACITY < 2) || ((CAPACITY & (CAPACITY - 1)) != 0)) begin
            $fatal(1, "axi_response_delay: CAPACITY (=%0d) must be a power of 2 >= 2",
                   CAPACITY);
        end
    end

    // ---- Free-running cycle counter ----------------------------------------
    // Width sized generously so (cyc - tin) never wraps before drain.
    // 32 bits = 42 s at 100 MHz; far longer than any realistic queue dwell.
    localparam int CYC_W = 32;
    localparam int IDX_W = $clog2(CAPACITY);
    localparam int CNT_W = $clog2(CAPACITY + 1);

    logic [CYC_W-1:0] r_cyc;
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) r_cyc <= '0;
        else                        r_cyc <= r_cyc + 1'b1;
    )

    // ---- Storage -----------------------------------------------------------
    // Each slot holds {payload, admit-timestamp}. Vivado picks BRAM or LUTRAM
    // based on width/depth — at 256×~160b the R-channel queue lands in BRAM,
    // the small B-channel queue in LUTRAM.
    `ifdef XILINX
        (* ram_style = "auto" *)
    `elsif INTEL
        /* synthesis ramstyle = "AUTO" */
    `endif
    logic [DATA_WIDTH-1:0] r_data [CAPACITY];

    `ifdef XILINX
        (* ram_style = "auto" *)
    `elsif INTEL
        /* synthesis ramstyle = "AUTO" */
    `endif
    logic [CYC_W-1:0]      r_tin  [CAPACITY];

    logic [IDX_W-1:0]      r_head, r_tail;
    logic [CNT_W-1:0]      r_count;

    wire full  = (r_count == CNT_W'(CAPACITY));
    wire empty = (r_count == '0);

    // Slave-side handshake: accept a beat whenever there's room.
    assign s_ready = ~full;

    // ---- Drain gate --------------------------------------------------------
    // Head's dwell time = current cycle minus the cycle it was admitted.
    // Drain when dwell has reached the configured delay AND the queue is
    // non-empty.
    wire [CYC_W-1:0] head_dwell      = r_cyc - r_tin[r_head];
    wire [CYC_W-1:0] delay_extended  = {{(CYC_W-DELAY_W){1'b0}}, i_delay_cycles};
    wire             head_ready      = ~empty && (head_dwell >= delay_extended);

    // ---- Output register stage ---------------------------------------------
    // The 256-deep r_data[r_head] mux is a 15-LUT-level path; driving m_data
    // and m_valid combinationally from it lets the wide select fan out to the
    // consumer's CE/load network with no flop boundary between, and stream_char's
    // 100 MHz timing closes by single-digit picoseconds without one. Register
    // the externally-visible outputs in a 1-deep stage:
    //     - stage_load fires when downstream took the previous beat (or no
    //       beat is currently held) AND the FIFO head has met its dwell. It
    //       drives the FIFO's deq, so r_head advances exactly when we latch.
    //     - the deep r_data[r_head] mux now terminates at a flop's D, not at
    //       the external m_data port.
    // Latency adds 1 aclk cycle, which is invisible to the test-side delay
    // model: i_delay_cycles is "min dwell"; the configured value can be
    // decremented by 1 if the absolute count matters.
    logic [DATA_WIDTH-1:0] r_out_data;
    logic                  r_out_valid;

    wire stage_consume = r_out_valid && m_ready;
    wire stage_load    = head_ready  && (!r_out_valid || stage_consume);

    assign m_data  = r_out_data;
    assign m_valid = r_out_valid;

    wire enq = s_valid & s_ready;
    wire deq = stage_load;

    // ---- Pointer / count update -------------------------------------------
    `ALWAYS_FF_RST(aclk, aresetn,
        if (`RST_ASSERTED(aresetn)) begin
            r_head      <= '0;
            r_tail      <= '0;
            r_count     <= '0;
            r_out_data  <= '0;
            r_out_valid <= 1'b0;
        end else begin
            if (enq) begin
                r_data[r_tail] <= s_data;
                r_tin [r_tail] <= r_cyc;
                r_tail         <= r_tail + 1'b1;  // power-of-2 truncation wrap
            end
            if (deq) begin
                r_head <= r_head + 1'b1;          // power-of-2 truncation wrap
            end
            unique case ({enq, deq})
                2'b10:   r_count <= r_count + 1'b1;
                2'b01:   r_count <= r_count - 1'b1;
                default: r_count <= r_count;      // 2'b00 or 2'b11
            endcase

            // Output register stage: load on stage_load, drop r_out_valid on
            // a consume that isn't immediately followed by another load.
            if (stage_load) begin
                r_out_data  <= r_data[r_head];
                r_out_valid <= 1'b1;
            end else if (stage_consume) begin
                r_out_valid <= 1'b0;
            end
        end
    )

endmodule : axi_response_delay
