// Flat-port wrapper around idma_desc64_synth (the iDMA descriptor-chain
// frontend) for cocotb. Exposes the register-programming port, the descriptor-
// fetch AXI read channels, and the emitted 1D request as plain logic vectors,
// so a cocotb testbench can program a descriptor-chain head address, serve the
// descriptor reads, and time the descriptor-fetch overhead (kick -> first
// idma_req). The backend response is faked (instant completion) so a chain
// advances.  AddrWidth/DataWidth/IdWidth are fixed by idma_desc64_synth_pkg
// (64/64/8).
`timescale 1ns / 1ps

module idma_desc64_fe_flat
    import idma_desc64_synth_pkg::*;
(
    input  logic              clk_i,
    input  logic              rst_ni,
    // ---- register programming (reg_req/reg_rsp, flattened) ----
    input  logic [AddrWidth-1:0] reg_addr_i,
    input  logic [DataWidth-1:0] reg_wdata_i,
    input  logic                 reg_write_i,
    input  logic                 reg_valid_i,
    output logic [DataWidth-1:0] reg_rdata_o,
    output logic                 reg_ready_o,
    output logic                 reg_error_o,
    // ---- descriptor-fetch AXI (read-only manager, flattened) ----
    output logic [AddrWidth-1:0] ar_addr_o,
    output logic [7:0]           ar_len_o,
    output logic [2:0]           ar_size_o,
    output logic [IdWidth-1:0]   ar_id_o,
    output logic                 ar_valid_o,
    input  logic                 ar_ready_i,
    input  logic [DataWidth-1:0] r_data_i,
    input  logic [IdWidth-1:0]   r_id_i,
    input  logic [1:0]           r_resp_i,
    input  logic                 r_last_i,
    input  logic                 r_valid_i,
    output logic                 r_ready_o,
    // ---- emitted 1D request (observed; accepted immediately) ----
    output logic                 idma_req_valid_o,
    output logic [AddrWidth-1:0] idma_req_src_o,
    output logic [AddrWidth-1:0] idma_req_dst_o,
    output logic [31:0]          idma_req_length_o,
    output logic                 busy_o,
    output logic                 irq_o
);

    reg_req_t  s_reg_req;
    reg_rsp_t  s_reg_rsp;
    axi_req_t  m_axi_req;
    axi_rsp_t  m_axi_rsp;
    idma_req_t idma_req;
    idma_rsp_t idma_rsp;
    logic      idma_req_valid, idma_req_ready, idma_rsp_valid, idma_rsp_ready;

    // ---- register port pack/unpack ----
    always_comb begin
        s_reg_req         = '0;
        s_reg_req.addr    = reg_addr_i;
        s_reg_req.wdata   = reg_wdata_i;
        s_reg_req.write   = reg_write_i;
        s_reg_req.wstrb   = '1;
        s_reg_req.valid   = reg_valid_i;
    end
    assign reg_rdata_o = s_reg_rsp.rdata;
    assign reg_ready_o = s_reg_rsp.ready;
    assign reg_error_o = s_reg_rsp.error;

    // ---- descriptor-fetch AXI: drive AR/R from/to the struct ----
    assign ar_addr_o  = m_axi_req.ar.addr;
    assign ar_len_o   = m_axi_req.ar.len;
    assign ar_size_o  = m_axi_req.ar.size;
    assign ar_id_o    = m_axi_req.ar.id;
    assign ar_valid_o = m_axi_req.ar_valid;
    assign r_ready_o  = m_axi_req.r_ready;
    always_comb begin
        m_axi_rsp           = '0;
        m_axi_rsp.ar_ready  = ar_ready_i;
        m_axi_rsp.r_valid   = r_valid_i;
        m_axi_rsp.r.data    = r_data_i;
        m_axi_rsp.r.id      = r_id_i;
        m_axi_rsp.r.resp    = r_resp_i;
        m_axi_rsp.r.last    = r_last_i;
        // frontend never writes; tie AW/W/B accept high so it never stalls.
        m_axi_rsp.aw_ready  = 1'b1;
        m_axi_rsp.w_ready   = 1'b1;
    end

    // ---- emitted 1D request: observe + accept immediately, fake completion ----
    assign idma_req_valid_o  = idma_req_valid;
    assign idma_req_src_o    = idma_req.src_addr;
    assign idma_req_dst_o    = idma_req.dst_addr;
    assign idma_req_length_o = idma_req.length;
    assign idma_req_ready    = 1'b1;                 // always accept
    // Fake an instant, successful backend: one response per accepted request,
    // held valid until the frontend accepts it (proper ready/valid handshake)
    // so the chain advances. Outstanding = (#req fired) - (#rsp accepted).
    logic [7:0] outstanding_q;
    wire  req_fire = idma_req_valid & idma_req_ready;
    wire  rsp_fire = idma_rsp_valid & idma_rsp_ready;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) outstanding_q <= '0;
        else         outstanding_q <= outstanding_q + (req_fire ? 8'd1 : 8'd0)
                                                    - (rsp_fire ? 8'd1 : 8'd0);
    end
    always_comb begin
        idma_rsp       = '0;
        idma_rsp_valid = (outstanding_q != '0);
    end

    idma_desc64_synth u_fe (
        .clk_i            (clk_i),
        .rst_ni           (rst_ni),
        .master_req_o     (m_axi_req),
        .master_rsp_i     (m_axi_rsp),
        .axi_ar_id_i      ('0),
        .axi_aw_id_i      ('0),
        .slave_req_i      (s_reg_req),
        .slave_rsp_o      (s_reg_rsp),
        .idma_req_o       (idma_req),
        .idma_req_valid_o (idma_req_valid),
        .idma_req_ready_i (idma_req_ready),
        .idma_rsp_i       (idma_rsp),
        .idma_rsp_valid_i (idma_rsp_valid),
        .idma_rsp_ready_o (idma_rsp_ready),
        .idma_busy_i      (1'b0),
        .irq_o            (irq_o)
    );
    assign busy_o = 1'b0;

endmodule
