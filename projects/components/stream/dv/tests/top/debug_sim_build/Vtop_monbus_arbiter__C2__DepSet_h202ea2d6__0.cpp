// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop_monbus_arbiter__C2.h"

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___ico_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___ico_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.u_arbiter__DOT__block_arb = vlSelfRef.block_arb;
    vlSelfRef.last_grant = vlSelfRef.u_arbiter__DOT__last_grant;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    if (vlSelfRef.u_arbiter__DOT__grant_valid) {
        vlSelfRef.grant_valid = 1U;
        vlSelfRef.int_monbus_ready = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
        vlSelfRef.monbus_ready_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
        vlSelfRef.monbus_ready_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
        vlSelfRef.grant = vlSelfRef.u_arbiter__DOT__grant;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = vlSelfRef.u_arbiter__DOT__w_win_mask_decode
            [vlSelfRef.u_arbiter__DOT__grant_id];
    } else {
        vlSelfRef.grant_valid = 0U;
        vlSelfRef.int_monbus_ready = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
        vlSelfRef.monbus_ready_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
        vlSelfRef.monbus_ready_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
        vlSelfRef.grant = vlSelfRef.u_arbiter__DOT__grant;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = ((IData)(vlSelfRef.u_arbiter__DOT__r_last_valid)
                ? vlSelfRef.u_arbiter__DOT__w_win_mask_decode
               [vlSelfRef.u_arbiter__DOT__r_last_grant_id]
                : 1U);
    }
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U])));
    vlSelfRef.monbus_valid = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid;
    vlSelfRef.int_monbus_valid_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.int_monbus_valid_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.u_arbiter__DOT__clk = vlSelfRef.axi_aclk;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aclk 
        = vlSelfRef.axi_aclk;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aclk 
        = vlSelfRef.axi_aclk;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__axi_aclk 
        = vlSelfRef.axi_aclk;
    vlSelfRef.u_arbiter__DOT__rst_n = vlSelfRef.axi_aresetn;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aresetn 
        = vlSelfRef.axi_aresetn;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aresetn 
        = vlSelfRef.axi_aresetn;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__axi_aresetn 
        = vlSelfRef.axi_aresetn;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_data 
        = vlSelfRef.monbus_packet_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_data 
        = vlSelfRef.monbus_packet_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_valid 
        = vlSelfRef.monbus_valid_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_valid 
        = vlSelfRef.monbus_valid_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready) 
           & vlSelfRef.monbus_valid_in[0U]);
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready) 
           & vlSelfRef.monbus_valid_in[1U]);
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_ready 
        = vlSelfRef.monbus_ready;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid) 
           & (IData)(vlSelfRef.monbus_ready));
    vlSelfRef.int_monbus_packet_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.int_monbus_packet_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.int_monbus_valid = vlSelfRef.grant_valid;
    vlSelfRef.int_monbus_ready_in[0U] = ((IData)(vlSelfRef.grant) 
                                         & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.int_monbus_ready_in[1U] = (((IData)(vlSelfRef.grant) 
                                          >> 1U) & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.monbus_packet = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data;
    vlSelfRef.grant_ack = ((0xfffffffeU & ((IData)(vlSelfRef.grant) 
                                           & (vlSelfRef.int_monbus_valid_in
                                              [1U] 
                                              << 1U))) 
                           | ((IData)(vlSelfRef.grant) 
                              & vlSelfRef.int_monbus_valid_in
                              [0U]));
    vlSelfRef.request = ((vlSelfRef.int_monbus_valid_in
                          [1U] << 1U) | vlSelfRef.int_monbus_valid_in
                         [0U]);
    vlSelfRef.int_monbus_packet = 0ULL;
    if (vlSelfRef.grant_valid) {
        vlSelfRef.int_monbus_packet = vlSelfRef.int_monbus_packet_in
            [vlSelfRef.grant_id];
    }
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid 
        = vlSelfRef.int_monbus_valid;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready) 
           & (IData)(vlSelfRef.int_monbus_valid));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[0U] & (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[1U] & (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.u_arbiter__DOT__grant_ack = vlSelfRef.grant_ack;
    vlSelfRef.u_arbiter__DOT__w_ack_received = ((IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack) 
                                                & ((IData)(vlSelfRef.grant_ack) 
                                                   >> (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client)));
    vlSelfRef.u_arbiter__DOT__request = vlSelfRef.request;
    vlSelfRef.u_arbiter__DOT__w_any_requests = ((~ (IData)(vlSelfRef.block_arb)) 
                                                & (0U 
                                                   != (IData)(vlSelfRef.request)));
    vlSelfRef.u_arbiter__DOT__w_requests_unmasked = 
        ((IData)(vlSelfRef.block_arb) ? 0U : (IData)(vlSelfRef.request));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data 
        = vlSelfRef.int_monbus_packet;
    vlSelfRef.u_arbiter__DOT__w_can_grant = (1U & (
                                                   (~ (IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack)) 
                                                   | (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)));
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked 
        = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_requests_gated = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_other_requests = ((~ 
                                                   ((IData)(1U) 
                                                    << (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client))) 
                                                  & (IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked));
    vlSelfRef.u_arbiter__DOT__w_requests_masked = ((IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_curr_mask_decode));
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_masked 
        = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    vlSelfRef.u_arbiter__DOT__w_any_masked_requests 
        = (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_requests_masked));
    if (vlSelfRef.u_arbiter__DOT__w_any_masked_requests) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    } else {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    }
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 0U;
    if ((1U & ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
               & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    if ((IData)((((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
                  >> 1U) & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    vlSelfRef.u_arbiter__DOT__w_winner = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner;
    vlSelfRef.u_arbiter__DOT__w_winner_valid = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
    vlSelfRef.u_arbiter__DOT__w_should_grant = ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid) 
                                                & ((IData)(vlSelfRef.u_arbiter__DOT__w_any_requests) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_can_grant)));
    if (vlSelfRef.u_arbiter__DOT__w_should_grant) {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = ((IData)(vlSelfRef.u_arbiter__DOT__w_next_grant) 
                                                  | (3U 
                                                     & ((IData)(1U) 
                                                        << (IData)(vlSelfRef.u_arbiter__DOT__w_winner))));
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = vlSelfRef.u_arbiter__DOT__w_winner;
    } else {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
    }
}

extern const VlUnpacked<CData/*0:0*/, 128> Vtop__ConstPool__TABLE_hf86e662f_0;
extern const VlUnpacked<CData/*0:0*/, 128> Vtop__ConstPool__TABLE_h875710dc_0;

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    CData/*6:0*/ __Vtableidx1;
    __Vtableidx1 = 0;
    CData/*6:0*/ __Vtableidx2;
    __Vtableidx2 = 0;
    CData/*6:0*/ __Vtableidx3;
    __Vtableidx3 = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_valid;
    __Vdly__u_arbiter__DOT__grant_valid = 0;
    CData/*1:0*/ __Vdly__u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_id = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0;
    // Body
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_valid = vlSelfRef.u_arbiter__DOT__grant_valid;
    if (vlSelfRef.axi_aresetn) {
        vlSelfRef.unnamedblk4__DOT__i = 1U;
        vlSelfRef.unnamedblk4__DOT__i = 2U;
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
        }
        if (vlSelfRef.u_arbiter__DOT__grant_valid) {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 1U;
            if ((1U & (~ ((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                          & (~ (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)))))) {
                if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                      & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                     & (0U == (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    __Vdly__u_arbiter__DOT__grant_valid = 0U;
                    vlSelfRef.u_arbiter__DOT__last_grant 
                        = vlSelfRef.u_arbiter__DOT__grant;
                    vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                        = vlSelfRef.u_arbiter__DOT__grant_id;
                    vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                    vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    __Vdly__u_arbiter__DOT__grant = 0U;
                    __Vdly__u_arbiter__DOT__grant_id = 0U;
                } else if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                             & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                            & (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                        __Vdly__u_arbiter__DOT__grant_valid 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_valid;
                        vlSelfRef.u_arbiter__DOT__last_grant 
                            = vlSelfRef.u_arbiter__DOT__grant;
                        vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                            = vlSelfRef.u_arbiter__DOT__grant_id;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                        __Vdly__u_arbiter__DOT__grant 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant;
                        __Vdly__u_arbiter__DOT__grant_id 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                    } else {
                        __Vdly__u_arbiter__DOT__grant = 0U;
                        __Vdly__u_arbiter__DOT__grant_id = 0U;
                        __Vdly__u_arbiter__DOT__grant_valid = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    }
                }
            }
        } else {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
            if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                __Vdly__u_arbiter__DOT__grant_valid = 1U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
                vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                vlSelfRef.u_arbiter__DOT__r_pending_client 
                    = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
            } else {
                __Vdly__u_arbiter__DOT__grant_valid = 0U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
            }
            __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__w_next_grant;
            __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
        }
    } else {
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] = 0U;
        __Vdly__u_arbiter__DOT__grant = 0U;
        __Vdly__u_arbiter__DOT__grant_id = 0U;
        __Vdly__u_arbiter__DOT__grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__last_grant = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
    }
    __Vtableidx3 = (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer) 
                     << 6U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                                << 5U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                           << 1U) | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx3];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx3];
    __Vtableidx2 = (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                     << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                           << 1U) | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx2];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx2];
    __Vtableidx1 = (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                     << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                           << 1U) | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx1];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx1];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.u_arbiter__DOT__grant = __Vdly__u_arbiter__DOT__grant;
    vlSelfRef.u_arbiter__DOT__grant_id = __Vdly__u_arbiter__DOT__grant_id;
    vlSelfRef.u_arbiter__DOT__grant_valid = __Vdly__u_arbiter__DOT__grant_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.int_monbus_ready = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
    vlSelfRef.monbus_valid = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.last_grant = vlSelfRef.u_arbiter__DOT__last_grant;
    vlSelfRef.grant = vlSelfRef.u_arbiter__DOT__grant;
    vlSelfRef.grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    if (vlSelfRef.u_arbiter__DOT__grant_valid) {
        vlSelfRef.grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = vlSelfRef.u_arbiter__DOT__w_win_mask_decode
            [vlSelfRef.u_arbiter__DOT__grant_id];
    } else {
        vlSelfRef.grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = ((IData)(vlSelfRef.u_arbiter__DOT__r_last_valid)
                ? vlSelfRef.u_arbiter__DOT__w_win_mask_decode
               [vlSelfRef.u_arbiter__DOT__r_last_grant_id]
                : 1U);
    }
    vlSelfRef.int_monbus_packet_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.int_monbus_packet_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.monbus_packet = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data;
    vlSelfRef.request = ((vlSelfRef.int_monbus_valid_in
                          [1U] << 1U) | vlSelfRef.int_monbus_valid_in
                         [0U]);
    vlSelfRef.int_monbus_ready_in[0U] = ((IData)(vlSelfRef.grant) 
                                         & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.int_monbus_ready_in[1U] = (((IData)(vlSelfRef.grant) 
                                          >> 1U) & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.grant_ack = ((0xfffffffeU & ((IData)(vlSelfRef.grant) 
                                           & (vlSelfRef.int_monbus_valid_in
                                              [1U] 
                                              << 1U))) 
                           | ((IData)(vlSelfRef.grant) 
                              & vlSelfRef.int_monbus_valid_in
                              [0U]));
    if (vlSelfRef.grant_valid) {
        vlSelfRef.int_monbus_valid = 1U;
        vlSelfRef.int_monbus_packet = 0ULL;
        vlSelfRef.int_monbus_packet = vlSelfRef.int_monbus_packet_in
            [vlSelfRef.grant_id];
    } else {
        vlSelfRef.int_monbus_valid = 0U;
        vlSelfRef.int_monbus_packet = 0ULL;
    }
    vlSelfRef.u_arbiter__DOT__request = vlSelfRef.request;
    vlSelfRef.u_arbiter__DOT__w_any_requests = ((~ (IData)(vlSelfRef.block_arb)) 
                                                & (0U 
                                                   != (IData)(vlSelfRef.request)));
    vlSelfRef.u_arbiter__DOT__w_requests_unmasked = 
        ((IData)(vlSelfRef.block_arb) ? 0U : (IData)(vlSelfRef.request));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[0U] & (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[1U] & (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.u_arbiter__DOT__grant_ack = vlSelfRef.grant_ack;
    vlSelfRef.u_arbiter__DOT__w_ack_received = ((IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack) 
                                                & ((IData)(vlSelfRef.grant_ack) 
                                                   >> (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client)));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid 
        = vlSelfRef.int_monbus_valid;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready) 
           & (IData)(vlSelfRef.int_monbus_valid));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data 
        = vlSelfRef.int_monbus_packet;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked 
        = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_requests_gated = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_other_requests = ((~ 
                                                   ((IData)(1U) 
                                                    << (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client))) 
                                                  & (IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked));
    vlSelfRef.u_arbiter__DOT__w_requests_masked = ((IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_curr_mask_decode));
    vlSelfRef.u_arbiter__DOT__w_can_grant = (1U & (
                                                   (~ (IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack)) 
                                                   | (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)));
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_masked 
        = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    vlSelfRef.u_arbiter__DOT__w_any_masked_requests 
        = (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_requests_masked));
    if (vlSelfRef.u_arbiter__DOT__w_any_masked_requests) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    } else {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    }
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 0U;
    if ((1U & ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
               & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    if ((IData)((((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
                  >> 1U) & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    vlSelfRef.u_arbiter__DOT__w_winner = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner;
    vlSelfRef.u_arbiter__DOT__w_winner_valid = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
    vlSelfRef.u_arbiter__DOT__w_should_grant = ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid) 
                                                & ((IData)(vlSelfRef.u_arbiter__DOT__w_any_requests) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_can_grant)));
    if (vlSelfRef.u_arbiter__DOT__w_should_grant) {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = ((IData)(vlSelfRef.u_arbiter__DOT__w_next_grant) 
                                                  | (3U 
                                                     & ((IData)(1U) 
                                                        << (IData)(vlSelfRef.u_arbiter__DOT__w_winner))));
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = vlSelfRef.u_arbiter__DOT__w_winner;
    } else {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
    }
}

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__1(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__1\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_data 
        = vlSelfRef.monbus_packet_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_data 
        = vlSelfRef.monbus_packet_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_valid 
        = vlSelfRef.monbus_valid_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_valid 
        = vlSelfRef.monbus_valid_in[1U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_ready 
        = vlSelfRef.monbus_ready;
}

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___nba_comb__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___nba_comb__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready) 
           & vlSelfRef.monbus_valid_in[0U]);
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready) 
           & vlSelfRef.monbus_valid_in[1U]);
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid) 
           & (IData)(vlSelfRef.monbus_ready));
}

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    CData/*6:0*/ __Vtableidx4;
    __Vtableidx4 = 0;
    CData/*6:0*/ __Vtableidx5;
    __Vtableidx5 = 0;
    CData/*6:0*/ __Vtableidx6;
    __Vtableidx6 = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_valid;
    __Vdly__u_arbiter__DOT__grant_valid = 0;
    CData/*1:0*/ __Vdly__u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_id = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0;
    // Body
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_valid = vlSelfRef.u_arbiter__DOT__grant_valid;
    if (vlSelfRef.axi_aresetn) {
        vlSelfRef.unnamedblk4__DOT__i = 1U;
        vlSelfRef.unnamedblk4__DOT__i = 2U;
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
        }
        if (vlSelfRef.u_arbiter__DOT__grant_valid) {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 1U;
            if ((1U & (~ ((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                          & (~ (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)))))) {
                if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                      & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                     & (0U == (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    __Vdly__u_arbiter__DOT__grant_valid = 0U;
                    vlSelfRef.u_arbiter__DOT__last_grant 
                        = vlSelfRef.u_arbiter__DOT__grant;
                    vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                        = vlSelfRef.u_arbiter__DOT__grant_id;
                    vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                    vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    __Vdly__u_arbiter__DOT__grant = 0U;
                    __Vdly__u_arbiter__DOT__grant_id = 0U;
                } else if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                             & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                            & (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                        __Vdly__u_arbiter__DOT__grant_valid 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_valid;
                        vlSelfRef.u_arbiter__DOT__last_grant 
                            = vlSelfRef.u_arbiter__DOT__grant;
                        vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                            = vlSelfRef.u_arbiter__DOT__grant_id;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                        __Vdly__u_arbiter__DOT__grant 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant;
                        __Vdly__u_arbiter__DOT__grant_id 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                    } else {
                        __Vdly__u_arbiter__DOT__grant = 0U;
                        __Vdly__u_arbiter__DOT__grant_id = 0U;
                        __Vdly__u_arbiter__DOT__grant_valid = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    }
                }
            }
        } else {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
            if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                __Vdly__u_arbiter__DOT__grant_valid = 1U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
                vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                vlSelfRef.u_arbiter__DOT__r_pending_client 
                    = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
            } else {
                __Vdly__u_arbiter__DOT__grant_valid = 0U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
            }
            __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__w_next_grant;
            __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
        }
    } else {
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] = 0U;
        __Vdly__u_arbiter__DOT__grant = 0U;
        __Vdly__u_arbiter__DOT__grant_id = 0U;
        __Vdly__u_arbiter__DOT__grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__last_grant = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
    }
    __Vtableidx6 = (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer) 
                     << 6U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                                << 5U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                           << 1U) | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx6];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx6];
    __Vtableidx5 = (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                     << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                           << 1U) | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx5];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx5];
    __Vtableidx4 = (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                     << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                           << 1U) | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx4];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx4];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.u_arbiter__DOT__grant = __Vdly__u_arbiter__DOT__grant;
    vlSelfRef.u_arbiter__DOT__grant_id = __Vdly__u_arbiter__DOT__grant_id;
    vlSelfRef.u_arbiter__DOT__grant_valid = __Vdly__u_arbiter__DOT__grant_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.int_monbus_ready = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
    vlSelfRef.monbus_valid = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.last_grant = vlSelfRef.u_arbiter__DOT__last_grant;
    vlSelfRef.grant = vlSelfRef.u_arbiter__DOT__grant;
    vlSelfRef.grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    if (vlSelfRef.u_arbiter__DOT__grant_valid) {
        vlSelfRef.grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = vlSelfRef.u_arbiter__DOT__w_win_mask_decode
            [vlSelfRef.u_arbiter__DOT__grant_id];
    } else {
        vlSelfRef.grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = ((IData)(vlSelfRef.u_arbiter__DOT__r_last_valid)
                ? vlSelfRef.u_arbiter__DOT__w_win_mask_decode
               [vlSelfRef.u_arbiter__DOT__r_last_grant_id]
                : 1U);
    }
    vlSelfRef.int_monbus_packet_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.int_monbus_packet_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.monbus_packet = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data;
    vlSelfRef.request = ((vlSelfRef.int_monbus_valid_in
                          [1U] << 1U) | vlSelfRef.int_monbus_valid_in
                         [0U]);
    vlSelfRef.int_monbus_ready_in[0U] = ((IData)(vlSelfRef.grant) 
                                         & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.int_monbus_ready_in[1U] = (((IData)(vlSelfRef.grant) 
                                          >> 1U) & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.grant_ack = ((0xfffffffeU & ((IData)(vlSelfRef.grant) 
                                           & (vlSelfRef.int_monbus_valid_in
                                              [1U] 
                                              << 1U))) 
                           | ((IData)(vlSelfRef.grant) 
                              & vlSelfRef.int_monbus_valid_in
                              [0U]));
    if (vlSelfRef.grant_valid) {
        vlSelfRef.int_monbus_valid = 1U;
        vlSelfRef.int_monbus_packet = 0ULL;
        vlSelfRef.int_monbus_packet = vlSelfRef.int_monbus_packet_in
            [vlSelfRef.grant_id];
    } else {
        vlSelfRef.int_monbus_valid = 0U;
        vlSelfRef.int_monbus_packet = 0ULL;
    }
    vlSelfRef.u_arbiter__DOT__request = vlSelfRef.request;
    vlSelfRef.u_arbiter__DOT__w_any_requests = ((~ (IData)(vlSelfRef.block_arb)) 
                                                & (0U 
                                                   != (IData)(vlSelfRef.request)));
    vlSelfRef.u_arbiter__DOT__w_requests_unmasked = 
        ((IData)(vlSelfRef.block_arb) ? 0U : (IData)(vlSelfRef.request));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[0U] & (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[1U] & (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.u_arbiter__DOT__grant_ack = vlSelfRef.grant_ack;
    vlSelfRef.u_arbiter__DOT__w_ack_received = ((IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack) 
                                                & ((IData)(vlSelfRef.grant_ack) 
                                                   >> (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client)));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid 
        = vlSelfRef.int_monbus_valid;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready) 
           & (IData)(vlSelfRef.int_monbus_valid));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data 
        = vlSelfRef.int_monbus_packet;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked 
        = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_requests_gated = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_other_requests = ((~ 
                                                   ((IData)(1U) 
                                                    << (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client))) 
                                                  & (IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked));
    vlSelfRef.u_arbiter__DOT__w_requests_masked = ((IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_curr_mask_decode));
    vlSelfRef.u_arbiter__DOT__w_can_grant = (1U & (
                                                   (~ (IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack)) 
                                                   | (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)));
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_masked 
        = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    vlSelfRef.u_arbiter__DOT__w_any_masked_requests 
        = (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_requests_masked));
    if (vlSelfRef.u_arbiter__DOT__w_any_masked_requests) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    } else {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    }
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 0U;
    if ((1U & ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
               & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    if ((IData)((((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
                  >> 1U) & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    vlSelfRef.u_arbiter__DOT__w_winner = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner;
    vlSelfRef.u_arbiter__DOT__w_winner_valid = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
    vlSelfRef.u_arbiter__DOT__w_should_grant = ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid) 
                                                & ((IData)(vlSelfRef.u_arbiter__DOT__w_any_requests) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_can_grant)));
    if (vlSelfRef.u_arbiter__DOT__w_should_grant) {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = ((IData)(vlSelfRef.u_arbiter__DOT__w_next_grant) 
                                                  | (3U 
                                                     & ((IData)(1U) 
                                                        << (IData)(vlSelfRef.u_arbiter__DOT__w_winner))));
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = vlSelfRef.u_arbiter__DOT__w_winner;
    } else {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
    }
}

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    CData/*6:0*/ __Vtableidx7;
    __Vtableidx7 = 0;
    CData/*6:0*/ __Vtableidx8;
    __Vtableidx8 = 0;
    CData/*6:0*/ __Vtableidx9;
    __Vtableidx9 = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_valid;
    __Vdly__u_arbiter__DOT__grant_valid = 0;
    CData/*1:0*/ __Vdly__u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_id = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0;
    // Body
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_valid = vlSelfRef.u_arbiter__DOT__grant_valid;
    if (vlSelfRef.axi_aresetn) {
        vlSelfRef.unnamedblk4__DOT__i = 1U;
        vlSelfRef.unnamedblk4__DOT__i = 2U;
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
        }
        if (vlSelfRef.u_arbiter__DOT__grant_valid) {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 1U;
            if ((1U & (~ ((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                          & (~ (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)))))) {
                if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                      & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                     & (0U == (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    __Vdly__u_arbiter__DOT__grant_valid = 0U;
                    vlSelfRef.u_arbiter__DOT__last_grant 
                        = vlSelfRef.u_arbiter__DOT__grant;
                    vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                        = vlSelfRef.u_arbiter__DOT__grant_id;
                    vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                    vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    __Vdly__u_arbiter__DOT__grant = 0U;
                    __Vdly__u_arbiter__DOT__grant_id = 0U;
                } else if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                             & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                            & (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                        __Vdly__u_arbiter__DOT__grant_valid 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_valid;
                        vlSelfRef.u_arbiter__DOT__last_grant 
                            = vlSelfRef.u_arbiter__DOT__grant;
                        vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                            = vlSelfRef.u_arbiter__DOT__grant_id;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                        __Vdly__u_arbiter__DOT__grant 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant;
                        __Vdly__u_arbiter__DOT__grant_id 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                    } else {
                        __Vdly__u_arbiter__DOT__grant = 0U;
                        __Vdly__u_arbiter__DOT__grant_id = 0U;
                        __Vdly__u_arbiter__DOT__grant_valid = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    }
                }
            }
        } else {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
            if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                __Vdly__u_arbiter__DOT__grant_valid = 1U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
                vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                vlSelfRef.u_arbiter__DOT__r_pending_client 
                    = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
            } else {
                __Vdly__u_arbiter__DOT__grant_valid = 0U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
            }
            __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__w_next_grant;
            __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
        }
    } else {
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] = 0U;
        __Vdly__u_arbiter__DOT__grant = 0U;
        __Vdly__u_arbiter__DOT__grant_id = 0U;
        __Vdly__u_arbiter__DOT__grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__last_grant = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
    }
    __Vtableidx9 = (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer) 
                     << 6U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                                << 5U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                           << 1U) | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx9];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx9];
    __Vtableidx8 = (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                     << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                           << 1U) | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx8];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx8];
    __Vtableidx7 = (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                     << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                           << 1U) | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx7];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx7];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.u_arbiter__DOT__grant = __Vdly__u_arbiter__DOT__grant;
    vlSelfRef.u_arbiter__DOT__grant_id = __Vdly__u_arbiter__DOT__grant_id;
    vlSelfRef.u_arbiter__DOT__grant_valid = __Vdly__u_arbiter__DOT__grant_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.int_monbus_ready = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
    vlSelfRef.monbus_valid = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.last_grant = vlSelfRef.u_arbiter__DOT__last_grant;
    vlSelfRef.grant = vlSelfRef.u_arbiter__DOT__grant;
    vlSelfRef.grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    if (vlSelfRef.u_arbiter__DOT__grant_valid) {
        vlSelfRef.grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = vlSelfRef.u_arbiter__DOT__w_win_mask_decode
            [vlSelfRef.u_arbiter__DOT__grant_id];
    } else {
        vlSelfRef.grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = ((IData)(vlSelfRef.u_arbiter__DOT__r_last_valid)
                ? vlSelfRef.u_arbiter__DOT__w_win_mask_decode
               [vlSelfRef.u_arbiter__DOT__r_last_grant_id]
                : 1U);
    }
    vlSelfRef.int_monbus_packet_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.int_monbus_packet_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.monbus_packet = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data;
    vlSelfRef.request = ((vlSelfRef.int_monbus_valid_in
                          [1U] << 1U) | vlSelfRef.int_monbus_valid_in
                         [0U]);
    vlSelfRef.int_monbus_ready_in[0U] = ((IData)(vlSelfRef.grant) 
                                         & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.int_monbus_ready_in[1U] = (((IData)(vlSelfRef.grant) 
                                          >> 1U) & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.grant_ack = ((0xfffffffeU & ((IData)(vlSelfRef.grant) 
                                           & (vlSelfRef.int_monbus_valid_in
                                              [1U] 
                                              << 1U))) 
                           | ((IData)(vlSelfRef.grant) 
                              & vlSelfRef.int_monbus_valid_in
                              [0U]));
    if (vlSelfRef.grant_valid) {
        vlSelfRef.int_monbus_valid = 1U;
        vlSelfRef.int_monbus_packet = 0ULL;
        vlSelfRef.int_monbus_packet = vlSelfRef.int_monbus_packet_in
            [vlSelfRef.grant_id];
    } else {
        vlSelfRef.int_monbus_valid = 0U;
        vlSelfRef.int_monbus_packet = 0ULL;
    }
    vlSelfRef.u_arbiter__DOT__request = vlSelfRef.request;
    vlSelfRef.u_arbiter__DOT__w_any_requests = ((~ (IData)(vlSelfRef.block_arb)) 
                                                & (0U 
                                                   != (IData)(vlSelfRef.request)));
    vlSelfRef.u_arbiter__DOT__w_requests_unmasked = 
        ((IData)(vlSelfRef.block_arb) ? 0U : (IData)(vlSelfRef.request));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[0U] & (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[1U] & (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.u_arbiter__DOT__grant_ack = vlSelfRef.grant_ack;
    vlSelfRef.u_arbiter__DOT__w_ack_received = ((IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack) 
                                                & ((IData)(vlSelfRef.grant_ack) 
                                                   >> (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client)));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid 
        = vlSelfRef.int_monbus_valid;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready) 
           & (IData)(vlSelfRef.int_monbus_valid));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data 
        = vlSelfRef.int_monbus_packet;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked 
        = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_requests_gated = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_other_requests = ((~ 
                                                   ((IData)(1U) 
                                                    << (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client))) 
                                                  & (IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked));
    vlSelfRef.u_arbiter__DOT__w_requests_masked = ((IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_curr_mask_decode));
    vlSelfRef.u_arbiter__DOT__w_can_grant = (1U & (
                                                   (~ (IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack)) 
                                                   | (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)));
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_masked 
        = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    vlSelfRef.u_arbiter__DOT__w_any_masked_requests 
        = (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_requests_masked));
    if (vlSelfRef.u_arbiter__DOT__w_any_masked_requests) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    } else {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    }
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 0U;
    if ((1U & ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
               & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    if ((IData)((((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
                  >> 1U) & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    vlSelfRef.u_arbiter__DOT__w_winner = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner;
    vlSelfRef.u_arbiter__DOT__w_winner_valid = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
    vlSelfRef.u_arbiter__DOT__w_should_grant = ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid) 
                                                & ((IData)(vlSelfRef.u_arbiter__DOT__w_any_requests) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_can_grant)));
    if (vlSelfRef.u_arbiter__DOT__w_should_grant) {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = ((IData)(vlSelfRef.u_arbiter__DOT__w_next_grant) 
                                                  | (3U 
                                                     & ((IData)(1U) 
                                                        << (IData)(vlSelfRef.u_arbiter__DOT__w_winner))));
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = vlSelfRef.u_arbiter__DOT__w_winner;
    } else {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
    }
}

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    CData/*6:0*/ __Vtableidx10;
    __Vtableidx10 = 0;
    CData/*6:0*/ __Vtableidx11;
    __Vtableidx11 = 0;
    CData/*6:0*/ __Vtableidx12;
    __Vtableidx12 = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_valid;
    __Vdly__u_arbiter__DOT__grant_valid = 0;
    CData/*1:0*/ __Vdly__u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_id = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0;
    // Body
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_valid = vlSelfRef.u_arbiter__DOT__grant_valid;
    if (vlSelfRef.axi_aresetn) {
        vlSelfRef.unnamedblk4__DOT__i = 1U;
        vlSelfRef.unnamedblk4__DOT__i = 2U;
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
        }
        if (vlSelfRef.u_arbiter__DOT__grant_valid) {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 1U;
            if ((1U & (~ ((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                          & (~ (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)))))) {
                if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                      & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                     & (0U == (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    __Vdly__u_arbiter__DOT__grant_valid = 0U;
                    vlSelfRef.u_arbiter__DOT__last_grant 
                        = vlSelfRef.u_arbiter__DOT__grant;
                    vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                        = vlSelfRef.u_arbiter__DOT__grant_id;
                    vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                    vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    __Vdly__u_arbiter__DOT__grant = 0U;
                    __Vdly__u_arbiter__DOT__grant_id = 0U;
                } else if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                             & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                            & (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                        __Vdly__u_arbiter__DOT__grant_valid 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_valid;
                        vlSelfRef.u_arbiter__DOT__last_grant 
                            = vlSelfRef.u_arbiter__DOT__grant;
                        vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                            = vlSelfRef.u_arbiter__DOT__grant_id;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                        __Vdly__u_arbiter__DOT__grant 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant;
                        __Vdly__u_arbiter__DOT__grant_id 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                    } else {
                        __Vdly__u_arbiter__DOT__grant = 0U;
                        __Vdly__u_arbiter__DOT__grant_id = 0U;
                        __Vdly__u_arbiter__DOT__grant_valid = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    }
                }
            }
        } else {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
            if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                __Vdly__u_arbiter__DOT__grant_valid = 1U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
                vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                vlSelfRef.u_arbiter__DOT__r_pending_client 
                    = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
            } else {
                __Vdly__u_arbiter__DOT__grant_valid = 0U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
            }
            __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__w_next_grant;
            __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
        }
    } else {
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] = 0U;
        __Vdly__u_arbiter__DOT__grant = 0U;
        __Vdly__u_arbiter__DOT__grant_id = 0U;
        __Vdly__u_arbiter__DOT__grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__last_grant = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
    }
    __Vtableidx12 = (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx12];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx12];
    __Vtableidx11 = (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx11];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx11];
    __Vtableidx10 = (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx10];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx10];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.u_arbiter__DOT__grant = __Vdly__u_arbiter__DOT__grant;
    vlSelfRef.u_arbiter__DOT__grant_id = __Vdly__u_arbiter__DOT__grant_id;
    vlSelfRef.u_arbiter__DOT__grant_valid = __Vdly__u_arbiter__DOT__grant_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.int_monbus_ready = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
    vlSelfRef.monbus_valid = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.last_grant = vlSelfRef.u_arbiter__DOT__last_grant;
    vlSelfRef.grant = vlSelfRef.u_arbiter__DOT__grant;
    vlSelfRef.grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    if (vlSelfRef.u_arbiter__DOT__grant_valid) {
        vlSelfRef.grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = vlSelfRef.u_arbiter__DOT__w_win_mask_decode
            [vlSelfRef.u_arbiter__DOT__grant_id];
    } else {
        vlSelfRef.grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = ((IData)(vlSelfRef.u_arbiter__DOT__r_last_valid)
                ? vlSelfRef.u_arbiter__DOT__w_win_mask_decode
               [vlSelfRef.u_arbiter__DOT__r_last_grant_id]
                : 1U);
    }
    vlSelfRef.int_monbus_packet_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.int_monbus_packet_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.monbus_packet = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data;
    vlSelfRef.request = ((vlSelfRef.int_monbus_valid_in
                          [1U] << 1U) | vlSelfRef.int_monbus_valid_in
                         [0U]);
    vlSelfRef.int_monbus_ready_in[0U] = ((IData)(vlSelfRef.grant) 
                                         & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.int_monbus_ready_in[1U] = (((IData)(vlSelfRef.grant) 
                                          >> 1U) & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.grant_ack = ((0xfffffffeU & ((IData)(vlSelfRef.grant) 
                                           & (vlSelfRef.int_monbus_valid_in
                                              [1U] 
                                              << 1U))) 
                           | ((IData)(vlSelfRef.grant) 
                              & vlSelfRef.int_monbus_valid_in
                              [0U]));
    if (vlSelfRef.grant_valid) {
        vlSelfRef.int_monbus_valid = 1U;
        vlSelfRef.int_monbus_packet = 0ULL;
        vlSelfRef.int_monbus_packet = vlSelfRef.int_monbus_packet_in
            [vlSelfRef.grant_id];
    } else {
        vlSelfRef.int_monbus_valid = 0U;
        vlSelfRef.int_monbus_packet = 0ULL;
    }
    vlSelfRef.u_arbiter__DOT__request = vlSelfRef.request;
    vlSelfRef.u_arbiter__DOT__w_any_requests = ((~ (IData)(vlSelfRef.block_arb)) 
                                                & (0U 
                                                   != (IData)(vlSelfRef.request)));
    vlSelfRef.u_arbiter__DOT__w_requests_unmasked = 
        ((IData)(vlSelfRef.block_arb) ? 0U : (IData)(vlSelfRef.request));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[0U] & (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[1U] & (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.u_arbiter__DOT__grant_ack = vlSelfRef.grant_ack;
    vlSelfRef.u_arbiter__DOT__w_ack_received = ((IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack) 
                                                & ((IData)(vlSelfRef.grant_ack) 
                                                   >> (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client)));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid 
        = vlSelfRef.int_monbus_valid;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready) 
           & (IData)(vlSelfRef.int_monbus_valid));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data 
        = vlSelfRef.int_monbus_packet;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked 
        = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_requests_gated = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_other_requests = ((~ 
                                                   ((IData)(1U) 
                                                    << (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client))) 
                                                  & (IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked));
    vlSelfRef.u_arbiter__DOT__w_requests_masked = ((IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_curr_mask_decode));
    vlSelfRef.u_arbiter__DOT__w_can_grant = (1U & (
                                                   (~ (IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack)) 
                                                   | (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)));
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_masked 
        = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    vlSelfRef.u_arbiter__DOT__w_any_masked_requests 
        = (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_requests_masked));
    if (vlSelfRef.u_arbiter__DOT__w_any_masked_requests) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    } else {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    }
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 0U;
    if ((1U & ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
               & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    if ((IData)((((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
                  >> 1U) & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    vlSelfRef.u_arbiter__DOT__w_winner = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner;
    vlSelfRef.u_arbiter__DOT__w_winner_valid = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
    vlSelfRef.u_arbiter__DOT__w_should_grant = ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid) 
                                                & ((IData)(vlSelfRef.u_arbiter__DOT__w_any_requests) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_can_grant)));
    if (vlSelfRef.u_arbiter__DOT__w_should_grant) {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = ((IData)(vlSelfRef.u_arbiter__DOT__w_next_grant) 
                                                  | (3U 
                                                     & ((IData)(1U) 
                                                        << (IData)(vlSelfRef.u_arbiter__DOT__w_winner))));
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = vlSelfRef.u_arbiter__DOT__w_winner;
    } else {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
    }
}

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    CData/*6:0*/ __Vtableidx13;
    __Vtableidx13 = 0;
    CData/*6:0*/ __Vtableidx14;
    __Vtableidx14 = 0;
    CData/*6:0*/ __Vtableidx15;
    __Vtableidx15 = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_valid;
    __Vdly__u_arbiter__DOT__grant_valid = 0;
    CData/*1:0*/ __Vdly__u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_id = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0;
    // Body
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_valid = vlSelfRef.u_arbiter__DOT__grant_valid;
    if (vlSelfRef.axi_aresetn) {
        vlSelfRef.unnamedblk4__DOT__i = 1U;
        vlSelfRef.unnamedblk4__DOT__i = 2U;
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
        }
        if (vlSelfRef.u_arbiter__DOT__grant_valid) {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 1U;
            if ((1U & (~ ((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                          & (~ (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)))))) {
                if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                      & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                     & (0U == (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    __Vdly__u_arbiter__DOT__grant_valid = 0U;
                    vlSelfRef.u_arbiter__DOT__last_grant 
                        = vlSelfRef.u_arbiter__DOT__grant;
                    vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                        = vlSelfRef.u_arbiter__DOT__grant_id;
                    vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                    vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    __Vdly__u_arbiter__DOT__grant = 0U;
                    __Vdly__u_arbiter__DOT__grant_id = 0U;
                } else if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                             & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                            & (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                        __Vdly__u_arbiter__DOT__grant_valid 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_valid;
                        vlSelfRef.u_arbiter__DOT__last_grant 
                            = vlSelfRef.u_arbiter__DOT__grant;
                        vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                            = vlSelfRef.u_arbiter__DOT__grant_id;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                        __Vdly__u_arbiter__DOT__grant 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant;
                        __Vdly__u_arbiter__DOT__grant_id 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                    } else {
                        __Vdly__u_arbiter__DOT__grant = 0U;
                        __Vdly__u_arbiter__DOT__grant_id = 0U;
                        __Vdly__u_arbiter__DOT__grant_valid = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    }
                }
            }
        } else {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
            if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                __Vdly__u_arbiter__DOT__grant_valid = 1U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
                vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                vlSelfRef.u_arbiter__DOT__r_pending_client 
                    = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
            } else {
                __Vdly__u_arbiter__DOT__grant_valid = 0U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
            }
            __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__w_next_grant;
            __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
        }
    } else {
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] = 0U;
        __Vdly__u_arbiter__DOT__grant = 0U;
        __Vdly__u_arbiter__DOT__grant_id = 0U;
        __Vdly__u_arbiter__DOT__grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__last_grant = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
    }
    __Vtableidx15 = (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx15];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx15];
    __Vtableidx14 = (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx14];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx14];
    __Vtableidx13 = (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx13];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx13];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.u_arbiter__DOT__grant = __Vdly__u_arbiter__DOT__grant;
    vlSelfRef.u_arbiter__DOT__grant_id = __Vdly__u_arbiter__DOT__grant_id;
    vlSelfRef.u_arbiter__DOT__grant_valid = __Vdly__u_arbiter__DOT__grant_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.int_monbus_ready = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
    vlSelfRef.monbus_valid = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.last_grant = vlSelfRef.u_arbiter__DOT__last_grant;
    vlSelfRef.grant = vlSelfRef.u_arbiter__DOT__grant;
    vlSelfRef.grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    if (vlSelfRef.u_arbiter__DOT__grant_valid) {
        vlSelfRef.grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = vlSelfRef.u_arbiter__DOT__w_win_mask_decode
            [vlSelfRef.u_arbiter__DOT__grant_id];
    } else {
        vlSelfRef.grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = ((IData)(vlSelfRef.u_arbiter__DOT__r_last_valid)
                ? vlSelfRef.u_arbiter__DOT__w_win_mask_decode
               [vlSelfRef.u_arbiter__DOT__r_last_grant_id]
                : 1U);
    }
    vlSelfRef.int_monbus_packet_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.int_monbus_packet_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.monbus_packet = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data;
    vlSelfRef.request = ((vlSelfRef.int_monbus_valid_in
                          [1U] << 1U) | vlSelfRef.int_monbus_valid_in
                         [0U]);
    vlSelfRef.int_monbus_ready_in[0U] = ((IData)(vlSelfRef.grant) 
                                         & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.int_monbus_ready_in[1U] = (((IData)(vlSelfRef.grant) 
                                          >> 1U) & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.grant_ack = ((0xfffffffeU & ((IData)(vlSelfRef.grant) 
                                           & (vlSelfRef.int_monbus_valid_in
                                              [1U] 
                                              << 1U))) 
                           | ((IData)(vlSelfRef.grant) 
                              & vlSelfRef.int_monbus_valid_in
                              [0U]));
    if (vlSelfRef.grant_valid) {
        vlSelfRef.int_monbus_valid = 1U;
        vlSelfRef.int_monbus_packet = 0ULL;
        vlSelfRef.int_monbus_packet = vlSelfRef.int_monbus_packet_in
            [vlSelfRef.grant_id];
    } else {
        vlSelfRef.int_monbus_valid = 0U;
        vlSelfRef.int_monbus_packet = 0ULL;
    }
    vlSelfRef.u_arbiter__DOT__request = vlSelfRef.request;
    vlSelfRef.u_arbiter__DOT__w_any_requests = ((~ (IData)(vlSelfRef.block_arb)) 
                                                & (0U 
                                                   != (IData)(vlSelfRef.request)));
    vlSelfRef.u_arbiter__DOT__w_requests_unmasked = 
        ((IData)(vlSelfRef.block_arb) ? 0U : (IData)(vlSelfRef.request));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[0U] & (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[1U] & (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.u_arbiter__DOT__grant_ack = vlSelfRef.grant_ack;
    vlSelfRef.u_arbiter__DOT__w_ack_received = ((IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack) 
                                                & ((IData)(vlSelfRef.grant_ack) 
                                                   >> (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client)));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid 
        = vlSelfRef.int_monbus_valid;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready) 
           & (IData)(vlSelfRef.int_monbus_valid));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data 
        = vlSelfRef.int_monbus_packet;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked 
        = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_requests_gated = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_other_requests = ((~ 
                                                   ((IData)(1U) 
                                                    << (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client))) 
                                                  & (IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked));
    vlSelfRef.u_arbiter__DOT__w_requests_masked = ((IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_curr_mask_decode));
    vlSelfRef.u_arbiter__DOT__w_can_grant = (1U & (
                                                   (~ (IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack)) 
                                                   | (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)));
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_masked 
        = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    vlSelfRef.u_arbiter__DOT__w_any_masked_requests 
        = (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_requests_masked));
    if (vlSelfRef.u_arbiter__DOT__w_any_masked_requests) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    } else {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    }
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 0U;
    if ((1U & ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
               & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    if ((IData)((((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
                  >> 1U) & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    vlSelfRef.u_arbiter__DOT__w_winner = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner;
    vlSelfRef.u_arbiter__DOT__w_winner_valid = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
    vlSelfRef.u_arbiter__DOT__w_should_grant = ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid) 
                                                & ((IData)(vlSelfRef.u_arbiter__DOT__w_any_requests) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_can_grant)));
    if (vlSelfRef.u_arbiter__DOT__w_should_grant) {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = ((IData)(vlSelfRef.u_arbiter__DOT__w_next_grant) 
                                                  | (3U 
                                                     & ((IData)(1U) 
                                                        << (IData)(vlSelfRef.u_arbiter__DOT__w_winner))));
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = vlSelfRef.u_arbiter__DOT__w_winner;
    } else {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
    }
}

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    CData/*6:0*/ __Vtableidx16;
    __Vtableidx16 = 0;
    CData/*6:0*/ __Vtableidx17;
    __Vtableidx17 = 0;
    CData/*6:0*/ __Vtableidx18;
    __Vtableidx18 = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_valid;
    __Vdly__u_arbiter__DOT__grant_valid = 0;
    CData/*1:0*/ __Vdly__u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_id = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0;
    // Body
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_valid = vlSelfRef.u_arbiter__DOT__grant_valid;
    if (vlSelfRef.axi_aresetn) {
        vlSelfRef.unnamedblk4__DOT__i = 1U;
        vlSelfRef.unnamedblk4__DOT__i = 2U;
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
        }
        if (vlSelfRef.u_arbiter__DOT__grant_valid) {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 1U;
            if ((1U & (~ ((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                          & (~ (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)))))) {
                if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                      & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                     & (0U == (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    __Vdly__u_arbiter__DOT__grant_valid = 0U;
                    vlSelfRef.u_arbiter__DOT__last_grant 
                        = vlSelfRef.u_arbiter__DOT__grant;
                    vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                        = vlSelfRef.u_arbiter__DOT__grant_id;
                    vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                    vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    __Vdly__u_arbiter__DOT__grant = 0U;
                    __Vdly__u_arbiter__DOT__grant_id = 0U;
                } else if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                             & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                            & (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                        __Vdly__u_arbiter__DOT__grant_valid 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_valid;
                        vlSelfRef.u_arbiter__DOT__last_grant 
                            = vlSelfRef.u_arbiter__DOT__grant;
                        vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                            = vlSelfRef.u_arbiter__DOT__grant_id;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                        __Vdly__u_arbiter__DOT__grant 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant;
                        __Vdly__u_arbiter__DOT__grant_id 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                    } else {
                        __Vdly__u_arbiter__DOT__grant = 0U;
                        __Vdly__u_arbiter__DOT__grant_id = 0U;
                        __Vdly__u_arbiter__DOT__grant_valid = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    }
                }
            }
        } else {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
            if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                __Vdly__u_arbiter__DOT__grant_valid = 1U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
                vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                vlSelfRef.u_arbiter__DOT__r_pending_client 
                    = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
            } else {
                __Vdly__u_arbiter__DOT__grant_valid = 0U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
            }
            __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__w_next_grant;
            __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
        }
    } else {
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] = 0U;
        __Vdly__u_arbiter__DOT__grant = 0U;
        __Vdly__u_arbiter__DOT__grant_id = 0U;
        __Vdly__u_arbiter__DOT__grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__last_grant = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
    }
    __Vtableidx18 = (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx18];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx18];
    __Vtableidx17 = (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx17];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx17];
    __Vtableidx16 = (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx16];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx16];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.u_arbiter__DOT__grant = __Vdly__u_arbiter__DOT__grant;
    vlSelfRef.u_arbiter__DOT__grant_id = __Vdly__u_arbiter__DOT__grant_id;
    vlSelfRef.u_arbiter__DOT__grant_valid = __Vdly__u_arbiter__DOT__grant_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.int_monbus_ready = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
    vlSelfRef.monbus_valid = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.last_grant = vlSelfRef.u_arbiter__DOT__last_grant;
    vlSelfRef.grant = vlSelfRef.u_arbiter__DOT__grant;
    vlSelfRef.grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    if (vlSelfRef.u_arbiter__DOT__grant_valid) {
        vlSelfRef.grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = vlSelfRef.u_arbiter__DOT__w_win_mask_decode
            [vlSelfRef.u_arbiter__DOT__grant_id];
    } else {
        vlSelfRef.grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = ((IData)(vlSelfRef.u_arbiter__DOT__r_last_valid)
                ? vlSelfRef.u_arbiter__DOT__w_win_mask_decode
               [vlSelfRef.u_arbiter__DOT__r_last_grant_id]
                : 1U);
    }
    vlSelfRef.int_monbus_packet_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.int_monbus_packet_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.monbus_packet = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data;
    vlSelfRef.request = ((vlSelfRef.int_monbus_valid_in
                          [1U] << 1U) | vlSelfRef.int_monbus_valid_in
                         [0U]);
    vlSelfRef.int_monbus_ready_in[0U] = ((IData)(vlSelfRef.grant) 
                                         & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.int_monbus_ready_in[1U] = (((IData)(vlSelfRef.grant) 
                                          >> 1U) & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.grant_ack = ((0xfffffffeU & ((IData)(vlSelfRef.grant) 
                                           & (vlSelfRef.int_monbus_valid_in
                                              [1U] 
                                              << 1U))) 
                           | ((IData)(vlSelfRef.grant) 
                              & vlSelfRef.int_monbus_valid_in
                              [0U]));
    if (vlSelfRef.grant_valid) {
        vlSelfRef.int_monbus_valid = 1U;
        vlSelfRef.int_monbus_packet = 0ULL;
        vlSelfRef.int_monbus_packet = vlSelfRef.int_monbus_packet_in
            [vlSelfRef.grant_id];
    } else {
        vlSelfRef.int_monbus_valid = 0U;
        vlSelfRef.int_monbus_packet = 0ULL;
    }
    vlSelfRef.u_arbiter__DOT__request = vlSelfRef.request;
    vlSelfRef.u_arbiter__DOT__w_any_requests = ((~ (IData)(vlSelfRef.block_arb)) 
                                                & (0U 
                                                   != (IData)(vlSelfRef.request)));
    vlSelfRef.u_arbiter__DOT__w_requests_unmasked = 
        ((IData)(vlSelfRef.block_arb) ? 0U : (IData)(vlSelfRef.request));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[0U] & (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[1U] & (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.u_arbiter__DOT__grant_ack = vlSelfRef.grant_ack;
    vlSelfRef.u_arbiter__DOT__w_ack_received = ((IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack) 
                                                & ((IData)(vlSelfRef.grant_ack) 
                                                   >> (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client)));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid 
        = vlSelfRef.int_monbus_valid;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready) 
           & (IData)(vlSelfRef.int_monbus_valid));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data 
        = vlSelfRef.int_monbus_packet;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked 
        = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_requests_gated = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_other_requests = ((~ 
                                                   ((IData)(1U) 
                                                    << (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client))) 
                                                  & (IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked));
    vlSelfRef.u_arbiter__DOT__w_requests_masked = ((IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_curr_mask_decode));
    vlSelfRef.u_arbiter__DOT__w_can_grant = (1U & (
                                                   (~ (IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack)) 
                                                   | (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)));
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_masked 
        = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    vlSelfRef.u_arbiter__DOT__w_any_masked_requests 
        = (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_requests_masked));
    if (vlSelfRef.u_arbiter__DOT__w_any_masked_requests) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    } else {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    }
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 0U;
    if ((1U & ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
               & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    if ((IData)((((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
                  >> 1U) & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    vlSelfRef.u_arbiter__DOT__w_winner = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner;
    vlSelfRef.u_arbiter__DOT__w_winner_valid = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
    vlSelfRef.u_arbiter__DOT__w_should_grant = ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid) 
                                                & ((IData)(vlSelfRef.u_arbiter__DOT__w_any_requests) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_can_grant)));
    if (vlSelfRef.u_arbiter__DOT__w_should_grant) {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = ((IData)(vlSelfRef.u_arbiter__DOT__w_next_grant) 
                                                  | (3U 
                                                     & ((IData)(1U) 
                                                        << (IData)(vlSelfRef.u_arbiter__DOT__w_winner))));
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = vlSelfRef.u_arbiter__DOT__w_winner;
    } else {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
    }
}

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    CData/*6:0*/ __Vtableidx19;
    __Vtableidx19 = 0;
    CData/*6:0*/ __Vtableidx20;
    __Vtableidx20 = 0;
    CData/*6:0*/ __Vtableidx21;
    __Vtableidx21 = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_valid;
    __Vdly__u_arbiter__DOT__grant_valid = 0;
    CData/*1:0*/ __Vdly__u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_id = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0;
    // Body
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_valid = vlSelfRef.u_arbiter__DOT__grant_valid;
    if (vlSelfRef.axi_aresetn) {
        vlSelfRef.unnamedblk4__DOT__i = 1U;
        vlSelfRef.unnamedblk4__DOT__i = 2U;
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
        }
        if (vlSelfRef.u_arbiter__DOT__grant_valid) {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 1U;
            if ((1U & (~ ((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                          & (~ (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)))))) {
                if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                      & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                     & (0U == (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    __Vdly__u_arbiter__DOT__grant_valid = 0U;
                    vlSelfRef.u_arbiter__DOT__last_grant 
                        = vlSelfRef.u_arbiter__DOT__grant;
                    vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                        = vlSelfRef.u_arbiter__DOT__grant_id;
                    vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                    vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    __Vdly__u_arbiter__DOT__grant = 0U;
                    __Vdly__u_arbiter__DOT__grant_id = 0U;
                } else if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                             & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                            & (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                        __Vdly__u_arbiter__DOT__grant_valid 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_valid;
                        vlSelfRef.u_arbiter__DOT__last_grant 
                            = vlSelfRef.u_arbiter__DOT__grant;
                        vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                            = vlSelfRef.u_arbiter__DOT__grant_id;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                        __Vdly__u_arbiter__DOT__grant 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant;
                        __Vdly__u_arbiter__DOT__grant_id 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                    } else {
                        __Vdly__u_arbiter__DOT__grant = 0U;
                        __Vdly__u_arbiter__DOT__grant_id = 0U;
                        __Vdly__u_arbiter__DOT__grant_valid = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    }
                }
            }
        } else {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
            if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                __Vdly__u_arbiter__DOT__grant_valid = 1U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
                vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                vlSelfRef.u_arbiter__DOT__r_pending_client 
                    = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
            } else {
                __Vdly__u_arbiter__DOT__grant_valid = 0U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
            }
            __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__w_next_grant;
            __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
        }
    } else {
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] = 0U;
        __Vdly__u_arbiter__DOT__grant = 0U;
        __Vdly__u_arbiter__DOT__grant_id = 0U;
        __Vdly__u_arbiter__DOT__grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__last_grant = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
    }
    __Vtableidx21 = (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx21];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx21];
    __Vtableidx20 = (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx20];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx20];
    __Vtableidx19 = (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx19];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx19];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.u_arbiter__DOT__grant = __Vdly__u_arbiter__DOT__grant;
    vlSelfRef.u_arbiter__DOT__grant_id = __Vdly__u_arbiter__DOT__grant_id;
    vlSelfRef.u_arbiter__DOT__grant_valid = __Vdly__u_arbiter__DOT__grant_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.int_monbus_ready = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
    vlSelfRef.monbus_valid = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.last_grant = vlSelfRef.u_arbiter__DOT__last_grant;
    vlSelfRef.grant = vlSelfRef.u_arbiter__DOT__grant;
    vlSelfRef.grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    if (vlSelfRef.u_arbiter__DOT__grant_valid) {
        vlSelfRef.grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = vlSelfRef.u_arbiter__DOT__w_win_mask_decode
            [vlSelfRef.u_arbiter__DOT__grant_id];
    } else {
        vlSelfRef.grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = ((IData)(vlSelfRef.u_arbiter__DOT__r_last_valid)
                ? vlSelfRef.u_arbiter__DOT__w_win_mask_decode
               [vlSelfRef.u_arbiter__DOT__r_last_grant_id]
                : 1U);
    }
    vlSelfRef.int_monbus_packet_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.int_monbus_packet_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.monbus_packet = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data;
    vlSelfRef.request = ((vlSelfRef.int_monbus_valid_in
                          [1U] << 1U) | vlSelfRef.int_monbus_valid_in
                         [0U]);
    vlSelfRef.int_monbus_ready_in[0U] = ((IData)(vlSelfRef.grant) 
                                         & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.int_monbus_ready_in[1U] = (((IData)(vlSelfRef.grant) 
                                          >> 1U) & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.grant_ack = ((0xfffffffeU & ((IData)(vlSelfRef.grant) 
                                           & (vlSelfRef.int_monbus_valid_in
                                              [1U] 
                                              << 1U))) 
                           | ((IData)(vlSelfRef.grant) 
                              & vlSelfRef.int_monbus_valid_in
                              [0U]));
    if (vlSelfRef.grant_valid) {
        vlSelfRef.int_monbus_valid = 1U;
        vlSelfRef.int_monbus_packet = 0ULL;
        vlSelfRef.int_monbus_packet = vlSelfRef.int_monbus_packet_in
            [vlSelfRef.grant_id];
    } else {
        vlSelfRef.int_monbus_valid = 0U;
        vlSelfRef.int_monbus_packet = 0ULL;
    }
    vlSelfRef.u_arbiter__DOT__request = vlSelfRef.request;
    vlSelfRef.u_arbiter__DOT__w_any_requests = ((~ (IData)(vlSelfRef.block_arb)) 
                                                & (0U 
                                                   != (IData)(vlSelfRef.request)));
    vlSelfRef.u_arbiter__DOT__w_requests_unmasked = 
        ((IData)(vlSelfRef.block_arb) ? 0U : (IData)(vlSelfRef.request));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[0U] & (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[1U] & (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.u_arbiter__DOT__grant_ack = vlSelfRef.grant_ack;
    vlSelfRef.u_arbiter__DOT__w_ack_received = ((IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack) 
                                                & ((IData)(vlSelfRef.grant_ack) 
                                                   >> (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client)));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid 
        = vlSelfRef.int_monbus_valid;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready) 
           & (IData)(vlSelfRef.int_monbus_valid));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data 
        = vlSelfRef.int_monbus_packet;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked 
        = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_requests_gated = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_other_requests = ((~ 
                                                   ((IData)(1U) 
                                                    << (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client))) 
                                                  & (IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked));
    vlSelfRef.u_arbiter__DOT__w_requests_masked = ((IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_curr_mask_decode));
    vlSelfRef.u_arbiter__DOT__w_can_grant = (1U & (
                                                   (~ (IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack)) 
                                                   | (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)));
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_masked 
        = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    vlSelfRef.u_arbiter__DOT__w_any_masked_requests 
        = (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_requests_masked));
    if (vlSelfRef.u_arbiter__DOT__w_any_masked_requests) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    } else {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    }
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 0U;
    if ((1U & ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
               & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    if ((IData)((((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
                  >> 1U) & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    vlSelfRef.u_arbiter__DOT__w_winner = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner;
    vlSelfRef.u_arbiter__DOT__w_winner_valid = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
    vlSelfRef.u_arbiter__DOT__w_should_grant = ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid) 
                                                & ((IData)(vlSelfRef.u_arbiter__DOT__w_any_requests) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_can_grant)));
    if (vlSelfRef.u_arbiter__DOT__w_should_grant) {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = ((IData)(vlSelfRef.u_arbiter__DOT__w_next_grant) 
                                                  | (3U 
                                                     & ((IData)(1U) 
                                                        << (IData)(vlSelfRef.u_arbiter__DOT__w_winner))));
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = vlSelfRef.u_arbiter__DOT__w_winner;
    } else {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
    }
}

VL_INLINE_OPT void Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    CData/*6:0*/ __Vtableidx22;
    __Vtableidx22 = 0;
    CData/*6:0*/ __Vtableidx23;
    __Vtableidx23 = 0;
    CData/*6:0*/ __Vtableidx24;
    __Vtableidx24 = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_valid;
    __Vdly__u_arbiter__DOT__grant_valid = 0;
    CData/*1:0*/ __Vdly__u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant = 0;
    CData/*0:0*/ __Vdly__u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_id = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0;
    VlWide<4>/*127:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data;
    VL_ZERO_W(128, __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data);
    CData/*3:0*/ __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0;
    // Body
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__grant;
    __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    __Vdly__u_arbiter__DOT__grant_valid = vlSelfRef.u_arbiter__DOT__grant_valid;
    if (vlSelfRef.axi_aresetn) {
        vlSelfRef.unnamedblk4__DOT__i = 1U;
        vlSelfRef.unnamedblk4__DOT__i = 2U;
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [1U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros);
            __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data, 
                            vlSelfRef.monbus_packet_in
                            [0U]);
        }
        if ((2U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                     << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(1U) + (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count)));
        } else if ((1U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
                = (0xfU & ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                           - (IData)(1U)));
        } else if ((3U == (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                            << 1U) | (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer)))) {
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
                = (IData)((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                            << 0x20U) | (QData)((IData)(
                                                        vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
                = (IData)(((((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U])) 
                             << 0x20U) | (QData)((IData)(
                                                         vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U]))) 
                           >> 0x20U));
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
                = (IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros);
            __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
                = (IData)((vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros 
                           >> 0x20U));
            VL_ASSIGNSEL_WQ(128,64,(0x7fU & VL_SHIFTL_III(7,32,32, 
                                                          ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                                           - (IData)(1U)), 6U)), __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data, vlSelfRef.int_monbus_packet);
        }
        if (vlSelfRef.u_arbiter__DOT__grant_valid) {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 1U;
            if ((1U & (~ ((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                          & (~ (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)))))) {
                if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                      & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                     & (0U == (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    __Vdly__u_arbiter__DOT__grant_valid = 0U;
                    vlSelfRef.u_arbiter__DOT__last_grant 
                        = vlSelfRef.u_arbiter__DOT__grant;
                    vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                        = vlSelfRef.u_arbiter__DOT__grant_id;
                    vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                    vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    __Vdly__u_arbiter__DOT__grant = 0U;
                    __Vdly__u_arbiter__DOT__grant_id = 0U;
                } else if ((((IData)(vlSelfRef.u_arbiter__DOT__grant_valid) 
                             & (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)) 
                            & (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_other_requests)))) {
                    if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                        __Vdly__u_arbiter__DOT__grant_valid 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_valid;
                        vlSelfRef.u_arbiter__DOT__last_grant 
                            = vlSelfRef.u_arbiter__DOT__grant;
                        vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                            = vlSelfRef.u_arbiter__DOT__grant_id;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                        __Vdly__u_arbiter__DOT__grant 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant;
                        __Vdly__u_arbiter__DOT__grant_id 
                            = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
                    } else {
                        __Vdly__u_arbiter__DOT__grant = 0U;
                        __Vdly__u_arbiter__DOT__grant_id = 0U;
                        __Vdly__u_arbiter__DOT__grant_valid = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
                        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
                    }
                }
            }
        } else {
            vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
            if (vlSelfRef.u_arbiter__DOT__w_next_grant_valid) {
                __Vdly__u_arbiter__DOT__grant_valid = 1U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
                vlSelfRef.u_arbiter__DOT__r_pending_ack = 1U;
                vlSelfRef.u_arbiter__DOT__r_pending_client 
                    = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
            } else {
                __Vdly__u_arbiter__DOT__grant_valid = 0U;
                vlSelfRef.u_arbiter__DOT__last_grant 
                    = vlSelfRef.u_arbiter__DOT__grant;
                vlSelfRef.u_arbiter__DOT__r_last_grant_id 
                    = vlSelfRef.u_arbiter__DOT__grant_id;
            }
            __Vdly__u_arbiter__DOT__grant = vlSelfRef.u_arbiter__DOT__w_next_grant;
            __Vdly__u_arbiter__DOT__grant_id = vlSelfRef.u_arbiter__DOT__w_next_grant_id;
        }
    } else {
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] = 0U;
        __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] = 0U;
        __Vdly__u_arbiter__DOT__grant = 0U;
        __Vdly__u_arbiter__DOT__grant_id = 0U;
        __Vdly__u_arbiter__DOT__grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__last_grant = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__r_last_valid = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_ack = 0U;
        vlSelfRef.u_arbiter__DOT__r_pending_client = 0U;
    }
    __Vtableidx24 = (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx24];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx24];
    __Vtableidx23 = (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx23];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx23];
    __Vtableidx22 = (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer) 
                      << 6U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer) 
                                 << 5U) | (((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count) 
                                            << 1U) 
                                           | (IData)(vlSelfRef.axi_aresetn))));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready 
        = Vtop__ConstPool__TABLE_hf86e662f_0[__Vtableidx22];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid 
        = Vtop__ConstPool__TABLE_h875710dc_0[__Vtableidx22];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[2U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U] 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[2U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U] 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[3U];
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count 
        = __Vdly__gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count 
        = __Vdly__gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.u_arbiter__DOT__grant = __Vdly__u_arbiter__DOT__grant;
    vlSelfRef.u_arbiter__DOT__grant_id = __Vdly__u_arbiter__DOT__grant_id;
    vlSelfRef.u_arbiter__DOT__grant_valid = __Vdly__u_arbiter__DOT__grant_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data 
        = (((QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[1U])) 
            << 0x20U) | (QData)((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data[0U])));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count 
        = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count;
    vlSelfRef.int_monbus_ready = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready;
    vlSelfRef.monbus_valid = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count 
        = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count;
    vlSelfRef.monbus_ready_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready;
    vlSelfRef.int_monbus_valid_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid;
    vlSelfRef.last_grant = vlSelfRef.u_arbiter__DOT__last_grant;
    vlSelfRef.grant = vlSelfRef.u_arbiter__DOT__grant;
    vlSelfRef.grant_id = vlSelfRef.u_arbiter__DOT__grant_id;
    if (vlSelfRef.u_arbiter__DOT__grant_valid) {
        vlSelfRef.grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = vlSelfRef.u_arbiter__DOT__w_win_mask_decode
            [vlSelfRef.u_arbiter__DOT__grant_id];
    } else {
        vlSelfRef.grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_curr_mask_decode 
            = ((IData)(vlSelfRef.u_arbiter__DOT__r_last_valid)
                ? vlSelfRef.u_arbiter__DOT__w_win_mask_decode
               [vlSelfRef.u_arbiter__DOT__r_last_grant_id]
                : 1U);
    }
    vlSelfRef.int_monbus_packet_in[1U] = vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.int_monbus_packet_in[0U] = vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data;
    vlSelfRef.monbus_packet = vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data;
    vlSelfRef.request = ((vlSelfRef.int_monbus_valid_in
                          [1U] << 1U) | vlSelfRef.int_monbus_valid_in
                         [0U]);
    vlSelfRef.int_monbus_ready_in[0U] = ((IData)(vlSelfRef.grant) 
                                         & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.int_monbus_ready_in[1U] = (((IData)(vlSelfRef.grant) 
                                          >> 1U) & (IData)(vlSelfRef.int_monbus_ready));
    vlSelfRef.grant_ack = ((0xfffffffeU & ((IData)(vlSelfRef.grant) 
                                           & (vlSelfRef.int_monbus_valid_in
                                              [1U] 
                                              << 1U))) 
                           | ((IData)(vlSelfRef.grant) 
                              & vlSelfRef.int_monbus_valid_in
                              [0U]));
    if (vlSelfRef.grant_valid) {
        vlSelfRef.int_monbus_valid = 1U;
        vlSelfRef.int_monbus_packet = 0ULL;
        vlSelfRef.int_monbus_packet = vlSelfRef.int_monbus_packet_in
            [vlSelfRef.grant_id];
    } else {
        vlSelfRef.int_monbus_valid = 0U;
        vlSelfRef.int_monbus_packet = 0ULL;
    }
    vlSelfRef.u_arbiter__DOT__request = vlSelfRef.request;
    vlSelfRef.u_arbiter__DOT__w_any_requests = ((~ (IData)(vlSelfRef.block_arb)) 
                                                & (0U 
                                                   != (IData)(vlSelfRef.request)));
    vlSelfRef.u_arbiter__DOT__w_requests_unmasked = 
        ((IData)(vlSelfRef.block_arb) ? 0U : (IData)(vlSelfRef.request));
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[0U];
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready 
        = vlSelfRef.int_monbus_ready_in[1U];
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[0U] & (IData)(vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer 
        = (vlSelfRef.int_monbus_ready_in[1U] & (IData)(vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid));
    vlSelfRef.u_arbiter__DOT__grant_ack = vlSelfRef.grant_ack;
    vlSelfRef.u_arbiter__DOT__w_ack_received = ((IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack) 
                                                & ((IData)(vlSelfRef.grant_ack) 
                                                   >> (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client)));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid 
        = vlSelfRef.int_monbus_valid;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer 
        = ((IData)(vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready) 
           & (IData)(vlSelfRef.int_monbus_valid));
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data 
        = vlSelfRef.int_monbus_packet;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked 
        = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_requests_gated = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.u_arbiter__DOT__w_other_requests = ((~ 
                                                   ((IData)(1U) 
                                                    << (IData)(vlSelfRef.u_arbiter__DOT__r_pending_client))) 
                                                  & (IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked));
    vlSelfRef.u_arbiter__DOT__w_requests_masked = ((IData)(vlSelfRef.u_arbiter__DOT__w_requests_unmasked) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_curr_mask_decode));
    vlSelfRef.u_arbiter__DOT__w_can_grant = (1U & (
                                                   (~ (IData)(vlSelfRef.u_arbiter__DOT__r_pending_ack)) 
                                                   | (IData)(vlSelfRef.u_arbiter__DOT__w_ack_received)));
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__requests_masked 
        = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    vlSelfRef.u_arbiter__DOT__w_any_masked_requests 
        = (0U != (IData)(vlSelfRef.u_arbiter__DOT__w_requests_masked));
    if (vlSelfRef.u_arbiter__DOT__w_any_masked_requests) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_masked;
    } else {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.u_arbiter__DOT__w_requests_unmasked;
    }
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 0U;
    if ((1U & ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
               & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 0U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    if ((IData)((((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests) 
                  >> 1U) & (~ (IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid))))) {
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner = 1U;
        vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = 1U;
    }
    vlSelfRef.u_arbiter__DOT__w_winner = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner;
    vlSelfRef.u_arbiter__DOT__w_winner_valid = vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
    vlSelfRef.u_arbiter__DOT__w_should_grant = ((IData)(vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__winner_valid) 
                                                & ((IData)(vlSelfRef.u_arbiter__DOT__w_any_requests) 
                                                   & (IData)(vlSelfRef.u_arbiter__DOT__w_can_grant)));
    if (vlSelfRef.u_arbiter__DOT__w_should_grant) {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 1U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = ((IData)(vlSelfRef.u_arbiter__DOT__w_next_grant) 
                                                  | (3U 
                                                     & ((IData)(1U) 
                                                        << (IData)(vlSelfRef.u_arbiter__DOT__w_winner))));
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = vlSelfRef.u_arbiter__DOT__w_winner;
    } else {
        vlSelfRef.u_arbiter__DOT__w_next_grant_valid = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.u_arbiter__DOT__w_next_grant_id = 0U;
    }
}
