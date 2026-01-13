// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtop.h for the primary calling header

#ifndef VERILATED_VTOP_MONBUS_ARBITER__C2_H_
#define VERILATED_VTOP_MONBUS_ARBITER__C2_H_  // guard

#include "verilated.h"


class Vtop__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vtop_monbus_arbiter__C2 final : public VerilatedModule {
  public:

    // DESIGN SPECIFIC STATE
    // Anonymous structures to workaround compiler member-count bugs
    struct {
        VL_IN8(axi_aclk,0,0);
        VL_IN8(axi_aresetn,0,0);
        VL_IN8(block_arb,0,0);
        VL_OUT8(monbus_valid,0,0);
        VL_IN8(monbus_ready,0,0);
        VL_OUT8(grant_valid,0,0);
        VL_OUT8(grant,1,0);
        VL_OUT8(grant_id,0,0);
        VL_OUT8(last_grant,1,0);
        CData/*0:0*/ int_monbus_valid;
        CData/*0:0*/ int_monbus_ready;
        CData/*1:0*/ request;
        CData/*1:0*/ grant_ack;
        CData/*0:0*/ u_arbiter__DOT__clk;
        CData/*0:0*/ u_arbiter__DOT__rst_n;
        CData/*0:0*/ u_arbiter__DOT__block_arb;
        CData/*1:0*/ u_arbiter__DOT__request;
        CData/*1:0*/ u_arbiter__DOT__grant_ack;
        CData/*0:0*/ u_arbiter__DOT__grant_valid;
        CData/*1:0*/ u_arbiter__DOT__grant;
        CData/*0:0*/ u_arbiter__DOT__grant_id;
        CData/*1:0*/ u_arbiter__DOT__last_grant;
        CData/*0:0*/ u_arbiter__DOT__r_last_grant_id;
        CData/*0:0*/ u_arbiter__DOT__r_last_valid;
        CData/*0:0*/ u_arbiter__DOT__r_pending_ack;
        CData/*0:0*/ u_arbiter__DOT__r_pending_client;
        CData/*1:0*/ u_arbiter__DOT__w_requests_gated;
        CData/*1:0*/ u_arbiter__DOT__w_requests_masked;
        CData/*1:0*/ u_arbiter__DOT__w_requests_unmasked;
        CData/*0:0*/ u_arbiter__DOT__w_any_requests;
        CData/*0:0*/ u_arbiter__DOT__w_any_masked_requests;
        CData/*1:0*/ u_arbiter__DOT__w_curr_mask_decode;
        CData/*0:0*/ u_arbiter__DOT__w_winner;
        CData/*0:0*/ u_arbiter__DOT__w_winner_valid;
        CData/*0:0*/ u_arbiter__DOT__w_ack_received;
        CData/*0:0*/ u_arbiter__DOT__w_can_grant;
        CData/*1:0*/ u_arbiter__DOT__w_other_requests;
        CData/*0:0*/ u_arbiter__DOT__w_should_grant;
        CData/*1:0*/ u_arbiter__DOT__w_next_grant;
        CData/*0:0*/ u_arbiter__DOT__w_next_grant_id;
        CData/*0:0*/ u_arbiter__DOT__w_next_grant_valid;
        CData/*1:0*/ u_arbiter__DOT__u_priority_encoder__DOT__requests_masked;
        CData/*1:0*/ u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked;
        CData/*0:0*/ u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests;
        CData/*0:0*/ u_arbiter__DOT__u_priority_encoder__DOT__winner;
        CData/*0:0*/ u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
        CData/*1:0*/ u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests;
        CData/*0:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aclk;
        CData/*0:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aresetn;
        CData/*0:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_valid;
        CData/*0:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
        CData/*3:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count;
        CData/*0:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
        CData/*0:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready;
        CData/*3:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count;
        CData/*3:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
        CData/*0:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer;
        CData/*0:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer;
        CData/*0:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aclk;
        CData/*0:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aresetn;
        CData/*0:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_valid;
        CData/*0:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
        CData/*3:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count;
        CData/*0:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    };
    struct {
        CData/*0:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready;
        CData/*3:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count;
        CData/*3:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
        CData/*0:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer;
        CData/*0:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer;
        CData/*0:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__axi_aclk;
        CData/*0:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__axi_aresetn;
        CData/*0:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid;
        CData/*0:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
        CData/*3:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__count;
        CData/*0:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid;
        CData/*0:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_ready;
        CData/*3:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count;
        CData/*3:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
        CData/*0:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer;
        CData/*0:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer;
        IData/*31:0*/ unnamedblk1__DOT__i;
        IData/*31:0*/ unnamedblk2__DOT__i;
        IData/*31:0*/ unnamedblk3__DOT__i;
        IData/*31:0*/ unnamedblk4__DOT__i;
        IData/*31:0*/ u_arbiter__DOT__u_priority_encoder__DOT__gen_pe_generic__DOT__unnamedblk1__DOT__i;
        VlWide<4>/*127:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
        VlWide<4>/*127:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
        VlWide<4>/*127:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data;
        VL_OUT64(monbus_packet,63,0);
        QData/*63:0*/ int_monbus_packet;
        QData/*63:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_data;
        QData/*63:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
        QData/*63:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros;
        QData/*63:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_data;
        QData/*63:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
        QData/*63:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros;
        QData/*63:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data;
        QData/*63:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data;
        QData/*63:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros;
        VL_IN8(monbus_valid_in[2],0,0);
        VL_OUT8(monbus_ready_in[2],0,0);
        VL_IN64(monbus_packet_in[2],63,0);
        VlUnpacked<CData/*0:0*/, 2> int_monbus_valid_in;
        VlUnpacked<CData/*0:0*/, 2> int_monbus_ready_in;
        VlUnpacked<QData/*63:0*/, 2> int_monbus_packet_in;
        VlUnpacked<CData/*1:0*/, 2> u_arbiter__DOT__w_mask_decode;
        VlUnpacked<CData/*1:0*/, 2> u_arbiter__DOT__w_win_mask_decode;
    };

    // INTERNAL VARIABLES
    Vtop__Syms* const vlSymsp;

    // PARAMETERS
    static constexpr CData/*0:0*/ INPUT_SKID_EN = 1U;
    static constexpr CData/*0:0*/ OUTPUT_SKID_EN = 1U;
    static constexpr IData/*31:0*/ CLIENTS = 2U;
    static constexpr IData/*31:0*/ INPUT_SKID_ENABLE = 1U;
    static constexpr IData/*31:0*/ OUTPUT_SKID_ENABLE = 1U;
    static constexpr IData/*31:0*/ INPUT_SKID_DEPTH = 2U;
    static constexpr IData/*31:0*/ OUTPUT_SKID_DEPTH = 2U;
    static constexpr IData/*31:0*/ N = 1U;
    static constexpr IData/*31:0*/ u_arbiter__DOT__CLIENTS = 2U;
    static constexpr IData/*31:0*/ u_arbiter__DOT__WAIT_GNT_ACK = 1U;
    static constexpr IData/*31:0*/ u_arbiter__DOT__N = 1U;
    static constexpr IData/*31:0*/ u_arbiter__DOT__u_priority_encoder__DOT__CLIENTS = 2U;
    static constexpr IData/*31:0*/ u_arbiter__DOT__u_priority_encoder__DOT__N = 1U;
    static constexpr IData/*31:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DATA_WIDTH = 0x00000040U;
    static constexpr IData/*31:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DEPTH = 2U;
    static constexpr VlWide<3>/*95:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__INSTANCE_NAME = {{
        0x00000000, 0x00000000, 0x00000000
    }};
    static constexpr IData/*31:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DW = 0x00000040U;
    static constexpr IData/*31:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__BUF_WIDTH = 0x00000080U;
    static constexpr IData/*31:0*/ gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__BW = 0x00000080U;
    static constexpr IData/*31:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DATA_WIDTH = 0x00000040U;
    static constexpr IData/*31:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DEPTH = 2U;
    static constexpr VlWide<3>/*95:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__INSTANCE_NAME = {{
        0x00000000, 0x00000000, 0x00000000
    }};
    static constexpr IData/*31:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DW = 0x00000040U;
    static constexpr IData/*31:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__BUF_WIDTH = 0x00000080U;
    static constexpr IData/*31:0*/ gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__BW = 0x00000080U;
    static constexpr IData/*31:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__DATA_WIDTH = 0x00000040U;
    static constexpr IData/*31:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__DEPTH = 2U;
    static constexpr VlWide<3>/*87:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__INSTANCE_NAME = {{
        0x534b4944, 0x5055545f, 0x004f5554
    }};
    static constexpr IData/*31:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__DW = 0x00000040U;
    static constexpr IData/*31:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__BUF_WIDTH = 0x00000080U;
    static constexpr IData/*31:0*/ gen_output_skid_enabled__DOT__u_output_skid__DOT__BW = 0x00000080U;

    // CONSTRUCTORS
    Vtop_monbus_arbiter__C2(Vtop__Syms* symsp, const char* v__name);
    ~Vtop_monbus_arbiter__C2();
    VL_UNCOPYABLE(Vtop_monbus_arbiter__C2);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
