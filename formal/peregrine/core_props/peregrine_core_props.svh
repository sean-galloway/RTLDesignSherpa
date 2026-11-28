// peregrine_core_props.svh -- spliced into
// projects/components/riscv-ip/peregrine-rv32im/rtl/top/peregrine_core.sv
// before endmodule by formal/peregrine/core_props/Makefile (FLAT_SPLICE), so
// the properties see the core's internal nets while the RTL carries no
// assertions (owner rule).  riscv-ip/peregrine-rv32im TASK-001 stage 5.
//
// The predictor training rule (PRD §4.2, TASK-001 stage 3).  riscv-formal
// cannot see it: the predictor never changes an architectural result, so a
// predictor written twice, or for a killed instruction, or with the wrong
// outcome, passes every RVFI check and only costs cycles.  The rule the DV
// model relies on is "written once per instruction as it leaves EX, in
// program order, with the resolved outcome, and every instruction that
// leaves EX retires".  Stated here as a shadow queue:
//
//   - every predictor update (ex_leaves, the core's u_bpred.upd_valid)
//     pushes {pc, kind, taken, target};
//   - every retire pops the head and must be the same instruction
//     (pc equal): no retire without exactly one update, no update for an
//     instruction that never retires, never two updates for one;
//   - at most two updated instructions are past EX (EX/MEM and MEM/WB);
//   - for a retire that did not trap, the recorded kind matches the
//     instruction, and for a branch, JAL or JALR the recorded outcome is
//     the architectural one (taken -> target is rvfi_pc_wdata; not taken
//     -> pc_wdata = pc + 4);
//   - the mispredict flag reported at retire is "guess != outcome".
//
// Commit precision (PRD §5: "no memory, regfile or CSR write by an
// instruction younger than a trapping one"; and the memory half of "no
// instruction from the wrong path retires", whose RVFI half is
// riscv-formal's pc_fwd / pc_bwd).  Every architectural side effect
// belongs to the next instruction to retire, and that instruction did it:
//   - a data write (MEM, dmem_req with strobes) is followed by the retire
//     of a non-trapping store with the same address, strobes and data, and
//     every retiring store made exactly one write;
//   - a CSR write (MEM) is followed by the retire of a non-trapping CSR
//     instruction naming that CSR, and every retiring CSR instruction that
//     writes made one;
//   - trap entry (MEM) is followed by a trap beat from the same PC, and
//     every trap beat entered a trap;
//   - a register-file write (WB) is the retiring instruction's rd write.
// The interrupt lines are free in this harness, so interrupts are among
// the traps.
//
// Interrupting an M instruction (TASK-007):
//   - the retire after an mret is never an interrupt (the progress rule);
//   - an M instruction interrupted in EX leaves the M unit idle the cycle
//     after its trap (cancelled), and its trap beat is checked by the
//     commit-precision rules above (mepc = its PC, no rd write).

`ifdef FORMAL
    localparam logic [6:0] F_OP_BRANCH = 7'b1100011;
    localparam logic [6:0] F_OP_JAL    = 7'b1101111;
    localparam logic [6:0] F_OP_JALR   = 7'b1100111;

    typedef struct packed {
        logic [31:0] pc;
        logic        cond;
        logic        uncond;
        logic        taken;
        logic [31:0] target;
    } f_upd_t;

    f_upd_t     f_q0, f_q1;
    logic [1:0] f_n;
    f_upd_t     f_push;

    assign f_push.pc     = id_ex_q.pc;
    assign f_push.cond   = id_ex_q.branch;
    assign f_push.uncond = id_ex_q.jump | id_ex_q.jalr;
    assign f_push.taken  = ex_taken;
    assign f_push.target = ex_target;

    // Pop the head on a retire, then push behind what is left.
    always_ff @(posedge clk) begin
        if (!w_aresetn) begin
            f_n <= 2'd0;
        end else begin
            unique case ({ex_leaves, rvfi_valid})
                2'b10: begin
                    if (f_n == 2'd0) f_q0 <= f_push;
                    else             f_q1 <= f_push;
                    f_n <= f_n + 2'd1;
                end
                2'b01: begin
                    f_q0 <= f_q1;
                    f_n  <= f_n - 2'd1;
                end
                2'b11: begin
                    if (f_n == 2'd1) f_q0 <= f_push;
                    else begin
                        f_q0 <= f_q1;
                        f_q1 <= f_push;
                    end
                end
                default: ;
            endcase
        end
    end

    wire [6:0] f_rop = rvfi_insn[6:0];

    always_comb begin
        if (w_aresetn) begin
            ap_bp_inflight_bound: assert (f_n <= 2'd2);
            if (ex_leaves && !rvfi_valid)
                ap_bp_no_overflow: assert (f_n != 2'd2);
            if (rvfi_valid) begin
                ap_bp_retire_had_update: assert (f_n != 2'd0);
                ap_bp_retire_is_head:    assert (f_q0.pc == rvfi_pc_rdata);
                if (!rvfi_trap) begin
                    ap_bp_kind_cond:   assert (f_q0.cond == (f_rop == F_OP_BRANCH));
                    ap_bp_kind_uncond: assert (f_q0.uncond == ((f_rop == F_OP_JAL) ||
                                                               (f_rop == F_OP_JALR)));
                    // (no if/else around labelled asserts: sv2v folds the
                    // else into the first label's block)
                    // Outcome, for control transfers only (an mret's next
                    // PC is mepc, not a predictor outcome).
                    if (f_q0.taken)
                        ap_bp_taken_target: assert (f_q0.target == rvfi_pc_wdata);
                    if (!f_q0.taken && (f_q0.cond || f_q0.uncond))
                        ap_bp_not_taken_seq: assert (rvfi_pc_wdata == rvfi_pc_rdata + 32'd4);
                    ap_bp_mispredict_flag: assert (rvfi_bp_mispredict ==
                        ((rvfi_bp_pred_taken != f_q0.taken) ||
                         (f_q0.taken && (rvfi_bp_pred_target != f_q0.target))));
                end
            end
        end
    end

    // Reachability: each kind of event the rule is about.
    logic f_prev_wait, f_prev_mhold;
    always_ff @(posedge clk) begin
        f_prev_wait  <= mem_wait;
        f_prev_mhold <= ex_m_stall;
    end

    always_comb begin
        if (w_aresetn) begin
            cp_bp_two_inflight:   cover (f_n == 2'd2 && ex_leaves && rvfi_valid);
            cp_bp_leave_after_wait:  cover (ex_leaves && f_prev_wait && id_ex_q.branch);
            cp_bp_leave_after_mhold: cover (ex_leaves && f_prev_mhold);
            cp_bp_ex_killed:      cover (id_ex_q.valid && mem_redirect_nw && !mem_wait &&
                                         id_ex_q.branch);
            cp_bp_taken_retire:   cover (rvfi_valid && !rvfi_trap && f_q0.taken &&
                                         f_q0.cond && rvfi_bp_pred_taken);
            cp_bp_mispredict_retire: cover (rvfi_valid && rvfi_bp_mispredict && f_q0.uncond);
            cp_bp_irq_retire:     cover (rvfi_valid && rvfi_trap && rvfi_trap_cause[31]);
        end
    end

    // -----------------------------------------------------------------
    // Commit precision
    // -----------------------------------------------------------------
    localparam logic [6:0] F_OP_STORE  = 7'b0100011;
    localparam logic [6:0] F_OP_SYSTEM = 7'b1110011;

    logic        f_st_pend, f_csr_pend, f_trap_pend;
    logic [31:0] f_st_addr, f_st_data, f_trap_pc;
    logic [3:0]  f_st_strb;
    logic [11:0] f_csr_addr;
    logic        f_st_write;
    logic [31:0] f_st_bytes;

    assign f_st_write = dmem_req & (dmem_wstrb != 4'd0);
    assign f_st_bytes = {{8{f_st_strb[3]}}, {8{f_st_strb[2]}}, {8{f_st_strb[1]}}, {8{f_st_strb[0]}}};

    always_ff @(posedge clk) begin
        if (!w_aresetn) begin
            f_st_pend   <= 1'b0;
            f_csr_pend  <= 1'b0;
            f_trap_pend <= 1'b0;
        end else begin
            if (rvfi_valid) begin
                f_st_pend   <= 1'b0;
                f_csr_pend  <= 1'b0;
                f_trap_pend <= 1'b0;
            end
            if (f_st_write) begin
                f_st_pend <= 1'b1;
                f_st_addr <= dmem_addr;
                f_st_strb <= dmem_wstrb;
                f_st_data <= dmem_wdata;
            end
            if (mem_csr_wen) begin
                f_csr_pend <= 1'b1;
                f_csr_addr <= ex_mem_q.insn[31:20];
            end
            if (mem_trap) begin
                f_trap_pend <= 1'b1;
                f_trap_pc   <= ex_mem_q.pc;
            end
        end
    end

    wire f_r_store = (f_rop == F_OP_STORE);
    wire f_r_csr   = (f_rop == F_OP_SYSTEM) && (rvfi_insn[13:12] != 2'b00);
    wire f_r_csr_w = f_r_csr && ((rvfi_insn[13:12] == 2'b01) || (rvfi_insn[19:15] != 5'd0));

    always_comb begin
        if (w_aresetn) begin
            // One side effect of each kind per retire.
            if (f_st_write && !rvfi_valid)
                ap_c_one_store_per_retire: assert (!f_st_pend);
            if (mem_csr_wen && !rvfi_valid)
                ap_c_one_csr_per_retire:   assert (!f_csr_pend);
            if (mem_trap && !rvfi_valid)
                ap_c_one_trap_per_retire:  assert (!f_trap_pend);
            if (rvfi_valid) begin
                if (f_st_pend) begin
                    ap_c_store_retires:  assert (!rvfi_trap && f_r_store);
                    ap_c_store_addr:     assert (rvfi_mem_addr == f_st_addr);
                    ap_c_store_strb:     assert (rvfi_mem_wmask == f_st_strb);
                    ap_c_store_data:     assert ((rvfi_mem_wdata & f_st_bytes) ==
                                                 (f_st_data & f_st_bytes));
                end
                if (rvfi_mem_wmask != 4'd0)
                    ap_c_store_wrote:    assert (f_st_pend);
                if (f_csr_pend)
                    ap_c_csr_retires:    assert (!rvfi_trap && f_r_csr &&
                                                 (rvfi_insn[31:20] == f_csr_addr));
                if (!rvfi_trap && f_r_csr_w)
                    ap_c_csr_wrote:      assert (f_csr_pend);
                if (f_trap_pend)
                    ap_c_trap_retires:   assert (rvfi_trap && (rvfi_pc_rdata == f_trap_pc));
                if (rvfi_trap)
                    ap_c_trap_entered:   assert (f_trap_pend);
            end
            if (wb_rd_wen_eff && (wb_rd_addr != 5'd0))
                ap_c_rf_write_retires: assert (rvfi_valid && !rvfi_trap &&
                                               (rvfi_rd_addr == wb_rd_addr) &&
                                               (rvfi_rd_wdata == wb_rd_wdata));
        end
    end

    always_comb begin
        if (w_aresetn) begin
            cp_c_trap_kills_store: cover (mem_trap && id_ex_q.valid && id_ex_q.dmem_we);
            cp_c_irq_kills_csr:    cover (mem_trap && mem_irq && id_ex_q.valid && id_ex_q.csr_op);
            cp_c_store_retire:     cover (rvfi_valid && f_st_pend && f_prev_wait);
            cp_c_csr_retire:       cover (rvfi_valid && f_csr_pend);
        end
    end

    // -----------------------------------------------------------------
    // Interrupting an M instruction (TASK-007)
    // -----------------------------------------------------------------
    localparam logic [31:0] F_MRET = 32'h3020_0073;

    logic f_mret_retired;   // the last retire was an mret
    logic f_m_irq_trap;     // last cycle a tagged M instruction trapped
    always_ff @(posedge clk) begin
        if (!w_aresetn) begin
            f_mret_retired <= 1'b0;
            f_m_irq_trap   <= 1'b0;
        end else begin
            if (rvfi_valid)
                f_mret_retired <= !rvfi_trap && (rvfi_insn == F_MRET);
            f_m_irq_trap <= mem_trap && ex_mem_q.valid && ex_mem_q.irq_take;
        end
    end

    wire f_r_m = (rvfi_insn[6:0] == 7'b0110011) && (rvfi_insn[31:25] == 7'b0000001);

    always_comb begin
        if (w_aresetn) begin
            if (rvfi_valid && f_mret_retired)
                ap_i_after_mret_not_irq: assert (!(rvfi_trap && rvfi_trap_cause[31]));
            if (f_m_irq_trap)
                ap_i_m_cancelled:        assert (mdu_idle);
            cp_i_irq_on_m:      cover (rvfi_valid && rvfi_trap && rvfi_trap_cause[31] && f_r_m);
            cp_i_after_mret_irq_up: cover (rvfi_valid && f_mret_retired && !rvfi_trap &&
                                           irq_timer && csr_irq_pending == 1'b0);
        end
    end
`endif
