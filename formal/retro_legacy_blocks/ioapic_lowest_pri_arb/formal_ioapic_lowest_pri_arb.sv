// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2024-2025 sean galloway
//
// Formal proof for ioapic_lowest_pri_arb -- the consumer half of
// LowestPriority delivery (RLB-008).
//
// Every property here is on PORTS. That is not a limitation in this case: the
// module is combinational decision logic and its entire contract is visible at
// the boundary. (For rtc_config_regs it WAS a limitation -- see that proof's
// header for the four routes to internal signals that fail on a PeakRDL-backed
// block. This module has no generated package, so the question does not arise.)
//
//   P1  retry means exactly "nobody took it": deliv_retry is asserted if and
//       only if the message is valid and no CPU was granted. This is the
//       condition ioapic_core's w_deliv_accept tests, so getting it wrong
//       either loses an interrupt or replays an accepted one.
//   P2  LowestPriority grants AT MOST ONE CPU. "Lowest priority" names a
//       single winner; granting two would deliver one interrupt twice.
//   P3  a granted CPU was in the destination set -- never deliver to a CPU the
//       message was not addressed to.
//   P4  a granted CPU could accept -- never deliver to a CPU that refused.
//   P5  no grant at all unless the message is valid.

module formal_ioapic_lowest_pri_arb (
    input logic clk,
    input logic rst_n
);

    localparam int NC = 4;

    (* anyseq *) reg         deliv_valid;
    (* anyseq *) reg [7:0]   deliv_vector;
    (* anyseq *) reg [7:0]   deliv_dest;
    (* anyseq *) reg         deliv_dest_mode;
    (* anyseq *) reg [2:0]   deliv_deliv_mode;
    // PACKED, not unpacked: sv2v flattens the DUT's `logic [7:0] x [NUM_CPUS]`
    // ports into `[(NUM_CPUS*8)-1:0]`, and sby reads that flattened file. An
    // unpacked harness signal here gives
    // "ERROR: Insufficient number of array indices".
    (* anyseq *) reg [NC*8-1:0] cpu_apic_id;
    (* anyseq *) reg [NC*8-1:0] cpu_logical_dest;
    (* anyseq *) reg [NC*8-1:0] cpu_priority;
    (* anyseq *) reg [NC-1:0]   cpu_can_accept;

    wire            deliv_ready;
    wire            deliv_retry;
    wire [NC-1:0]   cpu_irq_valid;
    wire [7:0]      cpu_irq_vector;
    wire [2:0]      cpu_irq_deliv_mode;

    ioapic_lowest_pri_arb #(.NUM_CPUS(NC)) dut (
        .deliv_valid        (deliv_valid),
        .deliv_vector       (deliv_vector),
        .deliv_dest         (deliv_dest),
        .deliv_dest_mode    (deliv_dest_mode),
        .deliv_deliv_mode   (deliv_deliv_mode),
        .deliv_ready        (deliv_ready),
        .deliv_retry        (deliv_retry),
        .cpu_apic_id        (cpu_apic_id),
        .cpu_logical_dest   (cpu_logical_dest),
        .cpu_priority       (cpu_priority),
        .cpu_can_accept     (cpu_can_accept),
        .cpu_irq_valid      (cpu_irq_valid),
        .cpu_irq_vector     (cpu_irq_vector),
        .cpu_irq_deliv_mode (cpu_irq_deliv_mode)
    );

    // The destination set, restated independently of the DUT. Restating the
    // DUT's own expression would be tautological -- the trap the handbook
    // records for the old block_ready property.
    wire [NC-1:0] f_in_set;
    genvar g;
    generate
        for (g = 0; g < NC; g++) begin : g_set
            // sv2v packs element i of an unpacked array port at
            // [((N-1)-i)*8 +: 8] -- REVERSE order. Slicing [g*8 +: 8] here
            // mirrored the wrong CPUs and ap_grant_in_set failed on a design
            // that was correct. Restating a contract independently is right;
            // restating it against a flattened array means matching the
            // flattener's element order.
            assign f_in_set[g] = deliv_dest_mode
                               ? ((cpu_logical_dest[((NC-1)-g)*8 +: 8] & deliv_dest) != 8'h00)
                               : (cpu_apic_id[((NC-1)-g)*8 +: 8] == deliv_dest);
        end
    endgenerate

    always @(posedge clk) begin
        if (rst_n) begin
            // P1
            ap_retry_iff_nobody: assert (deliv_retry == (deliv_valid && (cpu_irq_valid == '0)));
            // P2
            if (deliv_deliv_mode == 3'b001)
                ap_lowest_pri_onehot0: assert ($onehot0(cpu_irq_valid));
            // P3 / P4 / P5
            ap_grant_in_set:     assert ((cpu_irq_valid & ~f_in_set)       == '0);
            ap_grant_can_accept: assert ((cpu_irq_valid & ~cpu_can_accept) == '0);
            if (!deliv_valid)
                ap_no_grant_idle: assert (cpu_irq_valid == '0);
        end
    end

    // Reachability. Without these the asserts can pass vacuously.
    always @(posedge clk) begin
        if (rst_n) begin
            cp_grant_physical: cover (deliv_valid && !deliv_dest_mode && (cpu_irq_valid != '0));
            cp_grant_logical:  cover (deliv_valid &&  deliv_dest_mode && (cpu_irq_valid != '0));
            cp_retry:          cover (deliv_retry);
            cp_lowest_pri_win: cover (deliv_valid && (deliv_deliv_mode == 3'b001)
                                      && $onehot(cpu_irq_valid));
            cp_fixed_multi:    cover (deliv_valid && (deliv_deliv_mode == 3'b000)
                                      && ($countones(cpu_irq_valid) > 1));
        end
    end

endmodule
