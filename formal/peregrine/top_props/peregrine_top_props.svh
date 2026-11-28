// peregrine_top_props.svh -- spliced into
// projects/components/riscv-ip/peregrine-rv32im/rtl/top/peregrine_top.sv
// before endmodule by formal/peregrine/top_props/Makefile (FLAT_SPLICE), so
// the properties see the wrapper's internal nets while the RTL carries no
// assertions (owner rule).  riscv-ip/peregrine-rv32im TASK-001 stage 5.
//
// The D-side wrapper contract (TASK-001 stages 4 and 7): every load or
// store the core retires was accepted exactly once by its target, and a
// load retires with the word its target answered.  Stage 7 lets an access
// be accepted while the core is held for the I$ (r_mem_done) and parks an
// early response (r_mem_have, r_have); the two mutants that survived the
// stage-7 simulation pass (MEM's early response dropped, or captured as
// WB's) and the lane-select mutant live exactly here.  Stated as a shadow
// queue of accepted accesses:
//
//   - every accept (w_dhs) pushes {address, store?, lane}; the response
//     that ends it (w_rsp_valid while r_outstanding) records the data,
//     taken from the target's own output (amber's whole beat, lane chosen
//     here from the accepted address; the CLINT's or the uncached port's
//     word), not from the wrapper's response mux;
//   - every retire with a memory access pops the head: the same address,
//     the same direction, and for a load, a response already in and
//     rvfi_mem_rdata equal to it;
//   - at most two accepted accesses are not yet retired (MEM and WB), and
//     no memory retire happens with nothing accepted;
//   - bus errors (TASK-005; the slave's RRESP / BRESP and the amber stub's
//     error bit are free): an access whose response was an error retires
//     as a load / store access-fault trap beat (mcause 5 for a load, 7 for
//     a store), with its response already in, and pops it like a memory
//     retire; an access answered OKAY never retires as an access fault,
//     and one answered with an error never retires as a completed access.
//
// The harness (formal_peregrine_top.sv) replaces amber with a stub whose
// response word is free on every cycle, valid or not, so nothing here can
// pass by reading a held response late.

`ifdef FORMAL
    typedef struct packed {
        logic [31:0] addr;
        logic        we;
        logic        have;
        logic        err;
        logic [31:0] data;
    } f_acc_t;

    f_acc_t     f_a0, f_a1;
    logic [1:0] f_an;

    // The access a response belongs to: the youngest accepted one (one is
    // in flight at a time).
    logic       f_lane_of_head;
    assign f_lane_of_head = (f_an == 2'd2) ? f_a1.addr[2] : f_a0.addr[2];

    // The target's own word for the access in flight.
    logic [31:0] f_rsp_word;
    always_comb begin
        unique case (r_tgt)
            T_CLINT: f_rsp_word = w_clint_rsp_rdata;
            T_UC:    f_rsp_word = w_uc_rsp_rdata;
            default: f_rsp_word = w_dc_rsp_data[32 * f_lane_of_head +: 32];
        endcase
    end

    logic   f_rsp;
    f_acc_t f_new;
    assign f_rsp        = w_rsp_valid & r_outstanding;
    assign f_new.addr   = w_daddr;
    assign f_new.we     = |w_dwstrb;
    assign f_new.have   = 1'b0;
    assign f_new.err    = 1'b0;
    assign f_new.data   = 32'd0;

    logic f_mem_retire;
    logic f_fault_retire;   // a load / store access fault (TASK-005)
    logic f_pop;
    assign f_mem_retire   = rvfi_valid & ((rvfi_mem_rmask != 4'd0) | (rvfi_mem_wmask != 4'd0));
    assign f_fault_retire = rvfi_valid & rvfi_trap &
                            ((rvfi_trap_cause == 32'd5) | (rvfi_trap_cause == 32'd7));
    assign f_pop          = f_mem_retire | f_fault_retire;

    // Order within a cycle: the response lands on the in-flight entry, the
    // retire pops the head, the accept pushes behind.
    f_acc_t f_b0, f_b1;
    logic [1:0] f_bn;
    always_comb begin
        f_b0 = f_a0;
        f_b1 = f_a1;
        if (f_rsp) begin
            if (f_an == 2'd2) begin
                f_b1.have = 1'b1;
                f_b1.err  = w_rsp_err;
                f_b1.data = f_rsp_word;
            end else begin
                f_b0.have = 1'b1;
                f_b0.err  = w_rsp_err;
                f_b0.data = f_rsp_word;
            end
        end
        f_bn = f_an;
        if (f_pop && f_an != 2'd0) begin
            f_b0 = f_b1;
            f_bn = f_an - 2'd1;
        end
    end

    always_ff @(posedge clk) begin
        if (!w_aresetn) begin
            f_an <= 2'd0;
        end else begin
            f_a0 <= f_b0;
            f_a1 <= f_b1;
            f_an <= f_bn;
            if (w_dhs) begin
                if (f_bn == 2'd0) f_a0 <= f_new;
                else              f_a1 <= f_new;
                f_an <= f_bn + 2'd1;
            end
        end
    end

    always_comb begin
        if (w_aresetn) begin
            ap_d_inflight_bound: assert (f_an <= 2'd2);
            if (w_dhs)
                ap_d_no_third_accept: assert (f_bn != 2'd2);
            if (f_rsp) begin
                ap_d_rsp_has_access: assert (f_an != 2'd0);
                ap_d_one_rsp:        assert (!((f_an == 2'd2) ? f_a1.have : f_a0.have));
            end
            if (f_fault_retire) begin
                ap_d_fault_was_accepted: assert (f_an != 2'd0);
                ap_d_fault_had_err:      assert (f_a0.have && f_a0.err);
                ap_d_fault_cause:        assert ((rvfi_trap_cause == 32'd7) == f_a0.we);
            end
            if (f_mem_retire) begin
                ap_d_retire_no_err:  assert (!(f_a0.have && f_a0.err) &&
                                             !(f_rsp && w_rsp_err && (f_an == 2'd1)));
                ap_d_retire_was_accepted: assert (f_an != 2'd0);
                ap_d_retire_addr:  assert (f_a0.addr == rvfi_mem_addr);
                ap_d_retire_dir:   assert (f_a0.we == (rvfi_mem_wmask != 4'd0));
            end
            if (f_mem_retire && (rvfi_mem_rmask != 4'd0)) begin
                // Its response is in, or arriving now (then it is the
                // only access in the queue).
                ap_d_load_has_rsp: assert (f_a0.have || (f_rsp && (f_an == 2'd1)));
                ap_d_load_data:    assert (f_a0.have ? (rvfi_mem_rdata == f_a0.data)
                                                     : (rvfi_mem_rdata == f_rsp_word));
            end
        end
    end

    // Reachability: an accept under an I$ hold, its response parked, a
    // response for WB parked, both lanes, all three targets.
    always_comb begin
        if (w_aresetn) begin
            cp_d_accept_under_ic_hold: cover (w_dhs && w_ic_stall);
            cp_d_mem_have:             cover (r_mem_have && f_mem_retire);
            cp_d_have_retire:          cover (r_have && f_mem_retire && (rvfi_mem_rmask != 4'd0));
            cp_d_two_inflight:         cover (f_an == 2'd2 && f_mem_retire);
            cp_d_load_hi_lane:         cover (f_mem_retire && (rvfi_mem_rmask[3:2] != 2'b00) &&
                                              (r_tgt == T_DC));
            cp_d_uc_load:              cover (f_mem_retire && (rvfi_mem_rmask != 4'd0) &&
                                              (rvfi_mem_addr[31:28] == 4'h1));
            cp_d_clint_load:           cover (f_mem_retire && (rvfi_mem_rmask != 4'd0) &&
                                              (rvfi_mem_addr[31:16] == 16'h0200));
            // TASK-005: each fault path
            cp_d_fault_load:           cover (f_fault_retire && (rvfi_trap_cause == 32'd5));
            cp_d_fault_store:          cover (f_fault_retire && (rvfi_trap_cause == 32'd7));
            cp_d_fault_parked:         cover (r_mem_have && r_mem_err);
            cp_d_fault_dc:             cover (f_fault_retire && (r_tgt == T_DC));
        end
    end
`endif
