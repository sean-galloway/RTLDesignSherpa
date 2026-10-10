// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Formal wrapper for amber_snoop_resp (yosys-compatible)
// Run with: sby amber_snoop_resp.sby
//
// Task 13 proof (MAS ch02_blocks/07): AC/CR/CD ordering -- CR only after
// CDLAST, exactly one closed response per AC -- over the real responder
// including its axi4ace_snoop_slave skid-buffered transport. The control
// side (ctrl_*) is driven as a free-but-fair environment model.
//
// Structure: the wrapper top instantiates the DUT with free inputs; all
// properties and environment assumptions live in amber_snoop_resp_props,
// instantiated at the top and fed by the DUT's ports plus the SR FSM state
// and the FUB-side handshake wires, which amber_snoop_resp.sby exposes as
// DUT output ports (yosys has no hierarchical references and no working
// bind in this build; expose over a parameter-specialized flat is the
// mechanism -- see the Task 13 report, Toolchain findings).
//
// Assumption inventory (recorded; each is an environment obligation):
//   - reset protocol: house pattern.
//   - AXI AC: acvalid is held until acready.
//   - fair control grant: in SR_LOOKUP ctrl_snoop_ready is forced within 2
//     cycles (amber_control only delays it to safe boundaries).
//   - fair control data: in SR_DATA ctrl_cdvalid is forced within 2 cycles,
//     and ctrl_cdlast marks exactly the 8th beat of the DATA phase (the
//     amber_control CD contract: FILL_BEATS=8 beats, cdlast on the last).
//   - fair manager: crready / cdready each forced within 2 cycles of the
//     corresponding valid.
//   - ctrl_crresp is free (any response content; the sequencing must be
//     right for ALL of it). m_axi_acaddr / m_axi_acprot / ctrl_cddata are
//     tied off: no property claims those payload values.
//
// Abstraction: the ACE manager and amber_control are environment (free
// inputs); the transport + SR FSM are the DUT. No memories inside.

module formal_amber_snoop_resp (
    input  logic        aclk,
    input  logic        aresetn,

    // ACE snoop slave pins (manager side, free with AXI assumptions)
    input  logic [31:0] m_axi_acaddr,
    input  logic [3:0]  m_axi_acsnoop,
    input  logic [2:0]  m_axi_acprot,
    input  logic        m_axi_acvalid,
    input  logic        m_axi_crready,
    input  logic        m_axi_cdready,

    // control side (amber_control model, free with fair assumptions)
    input  logic        ctrl_snoop_ready,
    input  logic [4:0]  ctrl_crresp,
    input  logic [63:0] ctrl_cddata,
    input  logic        ctrl_cdlast,
    input  logic        ctrl_cdvalid
);

    localparam ADDR_WIDTH = 32;
    localparam DATA_WIDTH = 64;

    // ACE snoop slave pins (cache side outputs)
    logic        m_axi_acready;
    logic [4:0]  m_axi_crresp;
    logic        m_axi_crvalid;
    logic [DATA_WIDTH-1:0] m_axi_cddata;
    logic        m_axi_cdlast;
    logic        m_axi_cdvalid;

    // control side outputs
    logic        ctrl_snoop_req;
    logic [ADDR_WIDTH-1:0] ctrl_snoop_addr;
    logic [2:0]  ctrl_snoop_type;
    logic        ctrl_cdready;

    logic obs_fub_acvalid;
    logic obs_fub_acready;
    logic obs_fub_crvalid;
    logic [4:0] obs_fub_crresp;
    logic obs_fub_crready;
    logic obs_fub_cdvalid;
    logic obs_fub_cdready;
    logic obs_fub_cdlast;
    logic [1:0]        obs_r_state;

    // Instantiated without parameter overrides: the committed flat is
    // pre-specialized (geometry pinned, parameters stripped) by
    // specialize_params so yosys bind fires on the DUT scope.
    amber_snoop_resp dut (
        .aclk           (aclk),
        .aresetn        (aresetn),
        .m_axi_acaddr   (32'd0), // tied: no property claims the address value (only handshake timing)
        .m_axi_acsnoop  (m_axi_acsnoop),
        .m_axi_acprot   (3'd0), // tied
        .m_axi_acvalid  (m_axi_acvalid),
        .m_axi_acready  (m_axi_acready),
        .m_axi_crresp   (m_axi_crresp),
        .m_axi_crvalid  (m_axi_crvalid),
        .m_axi_crready  (m_axi_crready),
        .m_axi_cddata   (m_axi_cddata),
        .m_axi_cdlast   (m_axi_cdlast),
        .m_axi_cdvalid  (m_axi_cdvalid),
        .m_axi_cdready  (m_axi_cdready),
        .ctrl_snoop_req  (ctrl_snoop_req),
        .ctrl_snoop_addr (ctrl_snoop_addr),
        .ctrl_snoop_type (ctrl_snoop_type),
        .ctrl_snoop_ready(ctrl_snoop_ready),
        .ctrl_crresp     (ctrl_crresp),
        .ctrl_cddata     (64'd0), // tied: CD payload values are never claimed (ordering + payload-of-CR only)
        .ctrl_cdlast     (ctrl_cdlast),
        .ctrl_cdvalid    (ctrl_cdvalid),
        .ctrl_cdready    (ctrl_cdready),
        .fub_acvalid              (obs_fub_acvalid),
        .fub_acready              (obs_fub_acready),
        .fub_crvalid              (obs_fub_crvalid),
        .fub_crresp               (obs_fub_crresp),
        .fub_crready              (obs_fub_crready),
        .fub_cdvalid              (obs_fub_cdvalid),
        .fub_cdready              (obs_fub_cdready),
        .fub_cdlast               (obs_fub_cdlast),
        .r_state                  (obs_r_state)
    );

    // ------------------------------------------------------------------
    // Internal observability: amber_snoop_resp.sby exposes the SR FSM
    // state and the FUB-side handshake wires as DUT output ports (yosys
    // has no hierarchical references and bind never fires -- see the
    // Task 13 report); they are observed here and handed to the props.
    // ------------------------------------------------------------------

    amber_snoop_resp_props props (
        .aclk                     (aclk),
        .aresetn                  (aresetn),
        .m_axi_acvalid            (m_axi_acvalid),
        .m_axi_acready            (m_axi_acready),
        .m_axi_crresp             (m_axi_crresp),
        .m_axi_crvalid            (m_axi_crvalid),
        .m_axi_crready            (m_axi_crready),
        .m_axi_cdvalid            (m_axi_cdvalid),
        .m_axi_cdready            (m_axi_cdready),
        .fub_acvalid              (obs_fub_acvalid),
        .fub_acready              (obs_fub_acready),
        .fub_crvalid              (obs_fub_crvalid),
        .fub_crresp               (obs_fub_crresp),
        .fub_crready              (obs_fub_crready),
        .fub_cdvalid              (obs_fub_cdvalid),
        .fub_cdready              (obs_fub_cdready),
        .fub_cdlast               (obs_fub_cdlast),
        .r_state                  (obs_r_state),
        .ctrl_snoop_req           (ctrl_snoop_req),
        .ctrl_snoop_ready         (ctrl_snoop_ready),
        .ctrl_crresp              (ctrl_crresp),
        .ctrl_cdvalid             (ctrl_cdvalid),
        .ctrl_cdready             (ctrl_cdready)
    );

endmodule

// ===========================================================================
// Property module: bound into amber_snoop_resp (ports resolve in DUT scope)
// ===========================================================================
module amber_snoop_resp_props (
    input  logic        aclk,
    input  logic        aresetn,
    input  logic        m_axi_acvalid,
    input  logic        m_axi_acready,
    input  logic [4:0]  m_axi_crresp,
    input  logic        m_axi_crvalid,
    input  logic        m_axi_crready,
    input  logic        m_axi_cdvalid,
    input  logic        m_axi_cdready,
    input  logic        fub_acvalid,
    input  logic        fub_acready,
    input  logic        fub_crvalid,
    input  logic        fub_crready,
    input  logic [4:0]  fub_crresp,
    input  logic        fub_cdvalid,
    input  logic        fub_cdready,
    input  logic        fub_cdlast,
    input  logic [1:0]  r_state,
    input  logic        ctrl_snoop_req,
    input  logic        ctrl_snoop_ready,
    input  logic [4:0]  ctrl_crresp,
    input  logic        ctrl_cdvalid,
    input  logic        ctrl_cdready
);

    localparam FILL_BEATS = 8;

    // SR FSM encodings (amber_snoop_resp sr_state_t)
    localparam [1:0] SR_IDLE   = 2'd0;
    localparam [1:0] SR_LOOKUP = 2'd1;
    localparam [1:0] SR_DATA   = 2'd2;
    localparam [1:0] SR_RESP   = 2'd3;

    // =========================================================================
    // Formal infrastructure (house pattern)
    // =========================================================================
    reg [7:0] f_past_valid = 0;
    always @(posedge aclk)
        f_past_valid <= f_past_valid + (f_past_valid < 8'hFF);

    initial assume (!aresetn);
    always @(posedge aclk) begin
        if (f_past_valid >= 2) assume (aresetn);
    end

    // =========================================================================
    // Environment assumptions
    // =========================================================================

    // AXI AC: valid held until accepted (payload stability is not needed by
    // these properties; the skid latches at the handshake)
    always @(posedge aclk) begin
        if (aresetn && f_past_valid > 0 && $past(aresetn)
            && $past(m_axi_acvalid) && !$past(m_axi_acready)) begin
            as_ac_hold: assume (m_axi_acvalid);
        end
    end

    // fair control grant + data, fair manager ready (bounded stalls)
    reg [1:0] f_ready_wait, f_cdv_wait, f_crr_wait, f_cdr_wait;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_ready_wait <= 0; f_cdv_wait <= 0;
            f_crr_wait   <= 0; f_cdr_wait <= 0;
        end else begin
            if (r_state == SR_LOOKUP && !ctrl_snoop_ready) begin
                if (f_ready_wait != 2'h3) f_ready_wait <= f_ready_wait + 1;
            end else f_ready_wait <= 0;

            if (r_state == SR_DATA && !ctrl_cdvalid) begin
                if (f_cdv_wait != 2'h3) f_cdv_wait <= f_cdv_wait + 1;
            end else f_cdv_wait <= 0;

            if (m_axi_crvalid && !m_axi_crready) begin
                if (f_crr_wait != 2'h3) f_crr_wait <= f_crr_wait + 1;
            end else f_crr_wait <= 0;

            if (m_axi_cdvalid && !m_axi_cdready) begin
                if (f_cdr_wait != 2'h3) f_cdr_wait <= f_cdr_wait + 1;
            end else f_cdr_wait <= 0;
        end
    end

    always @(posedge aclk) begin
        if (aresetn) begin
            as_fair_ready: assume (!(r_state == SR_LOOKUP && !ctrl_snoop_ready)
                                   || (f_ready_wait < 2) || ctrl_snoop_ready);
            as_fair_cdvalid: assume (!(r_state == SR_DATA && !ctrl_cdvalid)
                                     || (f_cdv_wait < 2) || ctrl_cdvalid);
            as_fair_crready: assume (!(m_axi_crvalid && !m_axi_crready)
                                     || (f_crr_wait < 2) || m_axi_crready);
            as_fair_cdready: assume (!(m_axi_cdvalid && !m_axi_cdready)
                                     || (f_cdr_wait < 2) || m_axi_cdready);
        end
    end

    // beats handshaken in the current DATA phase (control-side counting)
    reg [3:0] f_data_beats;
    always @(posedge aclk) begin
        if (!aresetn) f_data_beats <= 0;
        else if (r_state != SR_DATA) f_data_beats <= 0;
        else if (ctrl_cdvalid && ctrl_cdready && (f_data_beats != 4'hF))
            f_data_beats <= f_data_beats + 1;
    end

    // ctrl_cdlast marks exactly the final beat of an 8-beat line
    always @(posedge aclk) begin
        if (aresetn)
            as_cdlast_is_last: assume (!(ctrl_cdvalid && ctrl_cdready)
                || (fub_cdlast == (f_data_beats == FILL_BEATS-1)));
    end

    // =========================================================================
    // Ghost bookkeeping
    // =========================================================================
    wire f_fub_ac_hs  = fub_acvalid  && fub_acready;   // AC accepted by SR FSM
    wire f_pin_ac_hs  = m_axi_acvalid  && m_axi_acready;
    wire f_pin_cr_hs  = m_axi_crvalid  && m_axi_crready;
    wire f_fub_last   = fub_cdvalid  && fub_cdready && fub_cdlast;
    // the CRRESP payload and its DT bit are latched by the SR FSM at the
    // CONTROL handshake (ctrl_snoop_req && ctrl_snoop_ready) -- one state
    // after the FUB accept -- and the DT branch decision uses that same
    // cycle's ctrl_crresp. Latch the ghost copy at the same handshake.
    wire f_gnt_hs     = ctrl_snoop_req && ctrl_snoop_ready;

    reg        f_outstanding;   // unused legacy flag, see f_out_n
    reg [3:0]  f_out_n;         // AC pin handshakes minus CR pin handshakes
    reg        f_cr_closed;     // a CR handshake happened since the last AC
    reg [4:0]  f_crresp_q;      // CRRESP latched at the control handshake
    reg        f_dt_q;          // its DataTransfer bit
    reg        f_last_beat;     // final CD beat seen at FUB since the grant

    always @(posedge aclk) begin
        if (!aresetn) begin
            f_outstanding <= 1'b0;
            f_out_n       <= 2'd0;
            f_cr_closed   <= 1'b0;
            f_crresp_q    <= 5'b0;
            f_dt_q        <= 1'b0;
            f_last_beat   <= 1'b0;
        end else begin
            // outstanding-response count: ACs in, CRs out (simultaneous nets
            // to zero). Two ACs can pipeline through the AC skid while a CR
            // drains, so a single flag undercounts.
            // 4 bits, clamped: the AC skid (depth 2) bounds legitimately
            // outstanding requests to ~3, so the clamp region is unreachable
            case ({f_pin_ac_hs, f_pin_cr_hs})
                2'b10: f_out_n <= (f_out_n == 4'd15) ? 4'd15 : f_out_n + 4'd1;
                2'b01: f_out_n <= (f_out_n == 4'd0) ? 4'd0 : f_out_n - 4'd1;
                default: ;
            endcase
            f_outstanding <= (f_out_n != 4'd0);
            if (f_pin_cr_hs) f_cr_closed <= 1'b1;
            if (f_pin_ac_hs) f_cr_closed <= 1'b0;
            if (f_gnt_hs) begin
                f_crresp_q  <= ctrl_crresp;
                f_dt_q      <= ctrl_crresp[0];
                f_last_beat <= 1'b0;
            end
            if (f_fub_last) f_last_beat <= 1'b1;
        end
    end

    // =========================================================================
    // Safety properties
    // =========================================================================

    // R1 every pin-level CR belongs to an accepted AC request that has not
    // yet closed (the AC/CR count is strictly positive while any CR shows).
    always @(posedge aclk) begin
        if (aresetn)
            ap_cr_has_request: assert (!m_axi_crvalid || (f_out_n != 4'd0));
    end

    // R2 CR only after CDLAST: with DataTransfer set, the final CD beat must
    // have been accepted at the FUB before the CR is presented (the
    // responder's ordering contract; the skid then preserves FIFO order).
    always @(posedge aclk) begin
        if (aresetn)
            ap_cr_after_cdlast_fub: assert (!fub_crvalid || !f_dt_q || f_last_beat);
    end

    // R3 CR payload integrity. A ghost model of the CR skid (depth 4, FIFO):
    // whatever the pins show is exactly the response that entered the skid
    // at the FUB, and that payload is the CRRESP latched at the control
    // handshake. (Responses can interleave with the skid contents -- response
    // N may still be draining when grant N+1 latches a new CRRESP -- so a
    // single latched copy is not enough at the pins; the queue model is.)
    reg [4:0] f_cr_q [0:3];
    reg [2:0] f_cr_n;
    integer ci;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_cr_n <= 0;
            for (ci = 0; ci < 4; ci = ci + 1) f_cr_q[ci] <= 5'b0;
        end else begin
            case ({(fub_crvalid && fub_crready), (f_pin_cr_hs)})
                2'b10: begin   // push
                    if (f_cr_n != 3'd4) begin
                        f_cr_q[f_cr_n] <= fub_crresp;
                        f_cr_n <= f_cr_n + 3'd1;
                    end
                end
                2'b01: begin   // pop (shift down)
                    if (f_cr_n != 0) begin
                        f_cr_q[0] <= f_cr_q[1];
                        f_cr_q[1] <= f_cr_q[2];
                        f_cr_q[2] <= f_cr_q[3];
                        f_cr_q[3] <= 5'b0;
                        f_cr_n <= f_cr_n - 3'd1;
                    end
                end
                2'b11: begin   // simultaneous: head drains, new entry lands
                    if (f_cr_n != 0) begin
                        f_cr_q[f_cr_n - 3'd1] <= fub_crresp;
                    end
                end
                default: ;
            endcase
        end
    end

    // R3a the FUB CR payload is the grant-latched CRRESP.
    always @(posedge aclk) begin
        if (aresetn)
            ap_crresp_fub: assert (!fub_crvalid || (fub_crresp == f_crresp_q));
    end

    // R3b the pin CR payload is the FIFO head of FUB-presented CRs.
    always @(posedge aclk) begin
        if (aresetn)
            ap_crresp_pin: assert (!m_axi_crvalid
                || ((f_cr_n != 0) && (m_axi_crresp == f_cr_q[0])));
    end

    // R4 one closed response per AC: CR handshakes never outnumber AC
    // handshakes (the responder can never close more responses than the
    // manager requested).
    always @(posedge aclk) begin
        if (aresetn)
            ap_one_response: assert (!(f_pin_cr_hs && (f_out_n == 4'd0)));
    end

    // R5 FSM/transport coherence: the FUB CR is only presented in SR_RESP,
    // the FUB CD only in SR_DATA, the control request only in SR_LOOKUP.
    always @(posedge aclk) begin
        if (aresetn) begin
            ap_cr_in_resp: assert (!fub_crvalid || (r_state == SR_RESP));
            ap_cd_in_data: assert (!fub_cdvalid || (r_state == SR_DATA));
            ap_req_in_lookup: assert (!ctrl_snoop_req || (r_state == SR_LOOKUP));
        end
    end

    // =========================================================================
    // Liveness (bounded, per fair assumptions): from the FUB AC accept to
    // the pin-level CR handshake is bounded -- the response always closes.
    // =========================================================================
    reg [7:0] f_serv_wait;
    reg       f_serv_active;
    always @(posedge aclk) begin
        if (!aresetn) begin
            f_serv_wait <= 0;
            f_serv_active <= 1'b0;
        end else if (f_fub_ac_hs) begin
            f_serv_wait <= 1;
            f_serv_active <= 1'b1;
        end else if (f_pin_cr_hs) begin
            f_serv_wait <= 0;
            f_serv_active <= 1'b0;
        end else if (f_serv_active && (f_serv_wait != 8'hFF)) begin
            f_serv_wait <= f_serv_wait + 1;
        end
    end

    always @(posedge aclk) begin
        if (aresetn)
            ap_service_bounded: assert (f_serv_wait < 64);
    end

    // =========================================================================
    // Cover properties
    // =========================================================================

    always @(posedge aclk) begin
        if (aresetn)
            cp_dt_response: cover (f_pin_cr_hs && f_dt_q);
    end

    always @(posedge aclk) begin
        if (aresetn)
            cp_cr_only_response: cover (f_pin_cr_hs && !f_dt_q);
    end

    always @(posedge aclk) begin
        if (aresetn)
            cp_back_to_back: cover (f_fub_ac_hs && $past(f_pin_cr_hs));
    end

endmodule
