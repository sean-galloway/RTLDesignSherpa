// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// RTL Design Sherpa - Industry-Standard RTL Design and Verification
// https://github.com/sean-galloway/RTLDesignSherpa
//
// Module: chi_pkg
// Purpose: CHI (Coherent Hub Interface, Arm IHI 0050 Issue H) flit widths,
//          the field offsets the link layer reads, and property legality
//
// Documentation: docs/markdown/rtl-amba/chi/README.md
// Subsystem: amba
//
// The link layer never looks inside a flit except for two fields: the
// Opcode (zero = a Link flit, LCrdReturn, B13.11) and the TxnID (zero in an
// LCrdReturn). Everything else is payload the Protocol layer owns. The flit
// widths and the two offsets come from Tables B13.6 to B13.9, read from bit
// 0 upward, and are the same arithmetic the RDS-DV CHIConfig uses, so a DUT
// built from these parameters and a BFM built from that config agree on
// every bit.
//
//   REQ  93 + RAW + Y + M + PB + S + max(E, R)  at NodeID_Width 7,
//        plus (NodeID_Width - 7) for each of TgtID, SrcID, ReturnNID
//   RSP  71 plus TgtID and SrcID growth
//   SNP  53 + SAW + M + E plus SrcID and FwdNID growth, SAW = RAW - 3
//   DAT  240 / 389 / 687 (DW 128 / 256 / 512) + Y + DC + P + E plus TgtID,
//        SrcID and HomeNID growth
//
// config_error numbers its rules exactly as CHIConfig.CONFIG_RULES does
// (rule 1, the spec issue, is not a parameter here: this RTL is Issue H).
//
// Author: sean galloway
// Created: 2026-10-30

`timescale 1ns / 1ps

package chi_pkg;

    // Constants a given port top may not reference (an RN-F never reads an
    // SNP opcode, an HN-F never a REQ one); they are the family's vocabulary
    /* verilator lint_off UNUSEDPARAM */

    // Node interface types (B13.6), for documentation and the port tops
    localparam int CHI_NODE_RN_F = 1;
    localparam int CHI_NODE_RN_D = 2;
    localparam int CHI_NODE_RN_I = 3;
    localparam int CHI_NODE_HN_F = 4;
    localparam int CHI_NODE_HN_I = 5;
    localparam int CHI_NODE_SN_F = 6;

    // Link states as the {LINKACTIVEREQ, LINKACTIVEACK} pair (Table B14.1)
    localparam logic [1:0] CHI_LINK_STOP       = 2'b00;
    localparam logic [1:0] CHI_LINK_ACTIVATE   = 2'b10;
    localparam logic [1:0] CHI_LINK_RUN        = 2'b11;
    localparam logic [1:0] CHI_LINK_DEACTIVATE = 2'b01;

    // B14.2.1.1: a receiver provides 1 to 15 L-Credits per channel
    localparam int CHI_MAX_LCREDIT = 15;

    function automatic int max2(int a, int b);
        return (a > b) ? a : b;
    endfunction

    // A port of zero width is carried as one tied bit
    function automatic int port_w(int w);
        return (w > 0) ? w : 1;
    endfunction

    // ------------------------------------------------------------------
    // Flit widths (Tables B13.6 to B13.9)
    // ------------------------------------------------------------------
    function automatic int req_flit_w(int nid_w, int addr_w, int req_rsvdc_w, int mpam_w,
                                      int pbha_w, int mecid_w, int streamid_w, int secsid1_w);
        return 93 + addr_w + req_rsvdc_w + mpam_w + pbha_w + secsid1_w +
               max2(mecid_w, streamid_w) + 3 * (nid_w - 7);
    endfunction

    function automatic int rsp_flit_w(int nid_w);
        return 71 + 2 * (nid_w - 7);
    endfunction

    function automatic int snp_flit_w(int nid_w, int addr_w, int mpam_w, int mecid_w);
        return 53 + (addr_w - 3) + mpam_w + mecid_w + 2 * (nid_w - 7);
    endfunction

    function automatic int dat_base_w(int data_w);
        return (data_w == 128) ? 240 : (data_w == 256) ? 389 : 687;
    endfunction

    function automatic int dat_flit_w(int nid_w, int data_w, int dat_rsvdc_w,
                                      bit data_check, bit poison, int mecid_w);
        return dat_base_w(data_w) + dat_rsvdc_w + (data_check ? data_w / 8 : 0) +
               (poison ? data_w / 64 : 0) + mecid_w + 3 * (nid_w - 7);
    endfunction

    // ------------------------------------------------------------------
    // Field offsets the link layer reads (LSB positions, bit 0 first)
    // ------------------------------------------------------------------
    // REQ: QoS 4 | TgtID n | SrcID n | TxnID 12 | ReturnNID n | StashNIDValid 1 |
    //      ReturnTxnID 12 | Opcode 7 ...
    function automatic int req_txnid_lsb(int nid_w);  return 4 + 2 * nid_w;  endfunction
    function automatic int req_opcode_lsb(int nid_w); return 29 + 3 * nid_w; endfunction
    localparam int REQ_OPCODE_W = 7;

    // RSP: QoS 4 | TgtID n | SrcID n | TxnID 12 | Opcode 5 ...
    function automatic int rsp_txnid_lsb(int nid_w);  return 4 + 2 * nid_w;  endfunction
    function automatic int rsp_opcode_lsb(int nid_w); return 16 + 2 * nid_w; endfunction
    localparam int RSP_OPCODE_W = 5;

    // SNP: QoS 4 | SrcID n | TxnID 12 | FwdNID n | FwdTxnID 12 | Opcode 5 ...
    function automatic int snp_txnid_lsb(int nid_w);  return 4 + nid_w;      endfunction
    function automatic int snp_opcode_lsb(int nid_w); return 28 + 2 * nid_w; endfunction
    localparam int SNP_OPCODE_W = 5;

    // DAT: QoS 4 | TgtID n | SrcID n | TxnID 12 | HomeNID n | Opcode 4 ...
    function automatic int dat_txnid_lsb(int nid_w);  return 4 + 2 * nid_w;  endfunction
    function automatic int dat_opcode_lsb(int nid_w); return 16 + 3 * nid_w; endfunction
    localparam int DAT_OPCODE_W = 4;

    localparam int CHI_TXNID_W = 12;

    // The further fields a monitor reads. REQ, continuing the row above:
    // MultiReq 1 | Size 3 | NumReq_hi 3 | Addr RAW | PAS 3 | LikelyShared 1 |
    // AllowRetry 1 | Order 2 | PCrdType 4 | MemAttr 4 | SnpAttr 1 | LPID 8 |
    // Excl 1 | ExpCompAck 1 ...
    function automatic int req_size_lsb(int nid_w);               return 37 + 3 * nid_w;          endfunction
    function automatic int req_pcrdtype_lsb(int nid_w, int addr_w); return 50 + 3 * nid_w + addr_w; endfunction
    function automatic int req_expcompack_lsb(int nid_w, int addr_w); return 68 + 3 * nid_w + addr_w; endfunction
    // RSP, continuing: RespErr 2 | Resp 3 | FwdState 3 | CBusy 3 | DBID 12 | PCrdType 4
    function automatic int rsp_resperr_lsb(int nid_w);  return 21 + 2 * nid_w; endfunction
    function automatic int rsp_dbid_lsb(int nid_w);     return 32 + 2 * nid_w; endfunction
    function automatic int rsp_pcrdtype_lsb(int nid_w); return 44 + 2 * nid_w; endfunction
    // DAT, continuing: RespErr 2 | Resp 3 | DataSource 8 | DataPull 1 | CBusy 3 | MECID E |
    // {4'b0, DBID 12} 16
    function automatic int dat_resperr_lsb(int nid_w);            return 20 + 3 * nid_w;           endfunction
    function automatic int dat_dbid_lsb(int nid_w, int mecid_w);  return 37 + 3 * nid_w + mecid_w; endfunction

    // Opcodes the link-layer monitor decodes (Tables B13.12, B13.14, B13.16)
    localparam logic [6:0] CHI_REQ_PCRD_RETURN     = 7'h05;
    localparam logic [6:0] CHI_REQ_MAKE_READ_UNIQUE = 7'h41;
    localparam logic [6:0] CHI_REQ_PREFETCH_TGT    = 7'h3A;   // no response at all (B2.3.1); TxnID is 0
    localparam logic [4:0] CHI_RSP_SNP_RESP        = 5'h01;
    localparam logic [4:0] CHI_RSP_COMP_ACK        = 5'h02;
    localparam logic [4:0] CHI_RSP_RETRY_ACK       = 5'h03;
    localparam logic [4:0] CHI_RSP_COMP            = 5'h04;
    localparam logic [4:0] CHI_RSP_COMP_DBID_RESP  = 5'h05;
    localparam logic [4:0] CHI_RSP_DBID_RESP       = 5'h06;
    localparam logic [4:0] CHI_RSP_PCRD_GRANT      = 5'h07;
    localparam logic [4:0] CHI_RSP_READ_RECEIPT    = 5'h08;
    localparam logic [4:0] CHI_RSP_SNP_RESP_FWDED  = 5'h09;
    localparam logic [4:0] CHI_RSP_TAG_MATCH       = 5'h0A;
    localparam logic [4:0] CHI_RSP_RESP_SEP_DATA   = 5'h0B;
    localparam logic [4:0] CHI_RSP_PERSIST         = 5'h0C;
    localparam logic [4:0] CHI_RSP_COMP_PERSIST    = 5'h0D;
    localparam logic [4:0] CHI_RSP_DBID_RESP_ORD   = 5'h0E;
    localparam logic [4:0] CHI_RSP_STASH_DONE      = 5'h10;
    localparam logic [4:0] CHI_RSP_COMP_STASH_DONE = 5'h11;
    localparam logic [4:0] CHI_RSP_COMP_CMO        = 5'h14;
    localparam logic [3:0] CHI_DAT_SNP_RESP_DATA   = 4'h1;
    localparam logic [3:0] CHI_DAT_COPYBACK_WDATA  = 4'h2;
    localparam logic [3:0] CHI_DAT_NONCOPYBACK_WDATA = 4'h3;
    localparam logic [3:0] CHI_DAT_COMP_DATA       = 4'h4;
    localparam logic [3:0] CHI_DAT_SNP_RESP_DATA_PTL = 4'h5;
    localparam logic [3:0] CHI_DAT_SNP_RESP_DATA_FWDED = 4'h6;
    localparam logic [3:0] CHI_DAT_WRITE_DATA_CANCEL = 4'h7;
    localparam logic [3:0] CHI_DAT_DATA_SEP_RESP   = 4'hB;
    localparam logic [3:0] CHI_DAT_NONCOPYBACK_WDATA_COMP_ACK = 4'hC;

    // Read requests: the ones answered with read data (Table B13.12, B2.3.1)
    function automatic bit is_read_opcode(logic [6:0] op);
        case (op)
            7'h01, 7'h02, 7'h03, 7'h04, 7'h07, 7'h11, 7'h24, 7'h25, 7'h26, 7'h41, 7'h4C: return 1'b1;
            default: return 1'b0;
        endcase
    endfunction

    // Requests pulled by a DBID response (CompDBIDResp, DBIDResp or DBIDRespOrd):
    // the writes, the atomics, DVMOp. WriteEvictOrEvict may be answered by a
    // plain Comp instead (B2.3.2.3 alt 1a), which the monitor treats specially.
    function automatic bit owes_dbid(logic [6:0] op);
        case (op)
            7'h14, 7'h15, 7'h17, 7'h18, 7'h19, 7'h1A, 7'h1B, 7'h1C, 7'h1D, 7'h20, 7'h21,
            7'h42, 7'h43, 7'h44, 7'h4E: return 1'b1;
            default: return (op[6:4] == 3'b010) || (op[6:3] == 4'b0111);   // 28-2F AtomicStore, 30-37 AtomicLoad, 38/39 Swap/Compare
        endcase
    endfunction

    // The subset of owes_dbid that then sends write data (the Zero writes do not)
    function automatic bit owes_wdata(logic [6:0] op);
        return owes_dbid(op) && (op != 7'h43) && (op != 7'h44);
    endfunction

    // CopyBack writes: a Comp instead of CompDBIDResp means no data and a CompAck owed (B2.3.2.3)
    function automatic bit is_copyback(logic [6:0] op);
        case (op)
            7'h15, 7'h17, 7'h1A, 7'h1B, 7'h42: return 1'b1;
            default: return 1'b0;
        endcase
    endfunction

    // DAT packets a transfer of 1 << size bytes needs on a DW-bit bus (B2.9.4)
    function automatic int data_packets(int size_enc, int data_w);
        int bytes;
        bytes = 1 << size_enc;
        return (bytes * 8 <= data_w) ? 1 : (bytes * 8) / data_w;
    endfunction

    // ------------------------------------------------------------------
    // Property legality (rule numbers shared with RDS-DV CHIConfig.CONFIG_RULES)
    // Returns 0 when legal, else the number of the first rule broken.
    // ------------------------------------------------------------------
    function automatic int config_error(int nid_w, int addr_w, int data_w,
                                        int req_rsvdc_w, int dat_rsvdc_w, int mpam_w,
                                        int pbha_w, int mecid_w, int streamid_w,
                                        int secsid1_w, int max_lcredit);
        if (nid_w < 7 || nid_w > 16)                                      return 2;
        if (addr_w < 44 || addr_w > 52)                                   return 3;
        if (!(data_w == 128 || data_w == 256 || data_w == 512))           return 4;
        if (!(req_rsvdc_w == 0 || req_rsvdc_w == 4 || req_rsvdc_w == 8 || req_rsvdc_w == 12 ||
              req_rsvdc_w == 16 || req_rsvdc_w == 24 || req_rsvdc_w == 32)) return 5;
        if (!(dat_rsvdc_w == 0 || dat_rsvdc_w == 4 || dat_rsvdc_w == 8 || dat_rsvdc_w == 12 ||
              dat_rsvdc_w == 16 || dat_rsvdc_w == 24 || dat_rsvdc_w == 32)) return 6;
        if (!(mpam_w == 0 || mpam_w == 12 || mpam_w == 15))               return 7;
        if (!(pbha_w == 0 || pbha_w == 4))                                return 8;
        if (!(mecid_w == 0 || mecid_w == 16))                             return 9;
        if (!(streamid_w == 0 || streamid_w == 16))                       return 10;
        if (!(secsid1_w == 0 || secsid1_w == 1))                          return 11;
        if (max_lcredit < 1 || max_lcredit > CHI_MAX_LCREDIT)             return 12;
        return 0;
    endfunction

    /* verilator lint_on UNUSEDPARAM */

endpackage : chi_pkg
