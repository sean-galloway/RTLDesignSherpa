// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop_monbus_arbiter__C2.h"

VL_ATTR_COLD void Vtop_monbus_arbiter__C2___eval_initial__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___eval_initial__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.unnamedblk1__DOT__i = 1U;
    vlSelfRef.unnamedblk1__DOT__i = 2U;
    vlSelfRef.unnamedblk2__DOT__i = 1U;
    vlSelfRef.unnamedblk2__DOT__i = 2U;
    vlSelfRef.unnamedblk3__DOT__i = 1U;
    vlSelfRef.unnamedblk3__DOT__i = 2U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__gen_pe_generic__DOT__unnamedblk1__DOT__i = 1U;
    vlSelfRef.u_arbiter__DOT__u_priority_encoder__DOT__gen_pe_generic__DOT__unnamedblk1__DOT__i = 2U;
    vlSelfRef.u_arbiter__DOT__w_win_mask_decode[0U] = 2U;
    vlSelfRef.u_arbiter__DOT__w_win_mask_decode[1U] = 0U;
    vlSelfRef.u_arbiter__DOT__w_mask_decode[0U] = 0U;
    vlSelfRef.u_arbiter__DOT__w_mask_decode[1U] = 1U;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros = 0ULL;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros = 0ULL;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros = 0ULL;
}

VL_ATTR_COLD void Vtop_monbus_arbiter__C2___stl_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___stl_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator__0\n"); );
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
    vlSelfRef.u_arbiter__DOT__rst_n = vlSelfRef.axi_aresetn;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aresetn 
        = vlSelfRef.axi_aresetn;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aresetn 
        = vlSelfRef.axi_aresetn;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__axi_aresetn 
        = vlSelfRef.axi_aresetn;
    vlSelfRef.u_arbiter__DOT__clk = vlSelfRef.axi_aclk;
    vlSelfRef.gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aclk 
        = vlSelfRef.axi_aclk;
    vlSelfRef.gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aclk 
        = vlSelfRef.axi_aclk;
    vlSelfRef.gen_output_skid_enabled__DOT__u_output_skid__DOT__axi_aclk 
        = vlSelfRef.axi_aclk;
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

VL_ATTR_COLD void Vtop_monbus_arbiter__C2___ctor_var_reset(Vtop_monbus_arbiter__C2* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+              Vtop_monbus_arbiter__C2___ctor_var_reset\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelf->axi_aclk = VL_RAND_RESET_I(1);
    vlSelf->axi_aresetn = VL_RAND_RESET_I(1);
    vlSelf->block_arb = VL_RAND_RESET_I(1);
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->monbus_valid_in[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->monbus_ready_in[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->monbus_packet_in[__Vi0] = VL_RAND_RESET_Q(64);
    }
    vlSelf->monbus_valid = VL_RAND_RESET_I(1);
    vlSelf->monbus_ready = VL_RAND_RESET_I(1);
    vlSelf->monbus_packet = VL_RAND_RESET_Q(64);
    vlSelf->grant_valid = VL_RAND_RESET_I(1);
    vlSelf->grant = VL_RAND_RESET_I(2);
    vlSelf->grant_id = VL_RAND_RESET_I(1);
    vlSelf->last_grant = VL_RAND_RESET_I(2);
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->int_monbus_valid_in[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->int_monbus_ready_in[__Vi0] = VL_RAND_RESET_I(1);
    }
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->int_monbus_packet_in[__Vi0] = VL_RAND_RESET_Q(64);
    }
    vlSelf->int_monbus_valid = VL_RAND_RESET_I(1);
    vlSelf->int_monbus_ready = VL_RAND_RESET_I(1);
    vlSelf->int_monbus_packet = VL_RAND_RESET_Q(64);
    vlSelf->request = VL_RAND_RESET_I(2);
    vlSelf->grant_ack = VL_RAND_RESET_I(2);
    vlSelf->unnamedblk1__DOT__i = 0;
    vlSelf->unnamedblk2__DOT__i = 0;
    vlSelf->unnamedblk3__DOT__i = 0;
    vlSelf->unnamedblk4__DOT__i = 0;
    vlSelf->u_arbiter__DOT__clk = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__rst_n = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__block_arb = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__request = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__grant_ack = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__grant_valid = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__grant = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__grant_id = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__last_grant = VL_RAND_RESET_I(2);
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->u_arbiter__DOT__w_mask_decode[__Vi0] = VL_RAND_RESET_I(2);
    }
    for (int __Vi0 = 0; __Vi0 < 2; ++__Vi0) {
        vlSelf->u_arbiter__DOT__w_win_mask_decode[__Vi0] = VL_RAND_RESET_I(2);
    }
    vlSelf->u_arbiter__DOT__r_last_grant_id = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__r_last_valid = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__r_pending_ack = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__r_pending_client = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__w_requests_gated = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__w_requests_masked = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__w_requests_unmasked = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__w_any_requests = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__w_any_masked_requests = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__w_curr_mask_decode = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__w_winner = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__w_winner_valid = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__w_ack_received = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__w_can_grant = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__w_other_requests = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__w_should_grant = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__w_next_grant = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__w_next_grant_id = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__w_next_grant_valid = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__u_priority_encoder__DOT__requests_masked = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__u_priority_encoder__DOT__winner = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__u_priority_encoder__DOT__winner_valid = VL_RAND_RESET_I(1);
    vlSelf->u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests = VL_RAND_RESET_I(2);
    vlSelf->u_arbiter__DOT__u_priority_encoder__DOT__gen_pe_generic__DOT__unnamedblk1__DOT__i = 0;
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aclk = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aresetn = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_valid = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_data = VL_RAND_RESET_Q(64);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count = VL_RAND_RESET_I(4);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count = VL_RAND_RESET_I(4);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data = VL_RAND_RESET_Q(64);
    VL_RAND_RESET_W(128, vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = VL_RAND_RESET_I(4);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros = VL_RAND_RESET_Q(64);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aclk = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__axi_aresetn = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_valid = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_ready = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__wr_data = VL_RAND_RESET_Q(64);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__count = VL_RAND_RESET_I(4);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_valid = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_ready = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_count = VL_RAND_RESET_I(4);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__rd_data = VL_RAND_RESET_Q(64);
    VL_RAND_RESET_W(128, vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__r_data_count = VL_RAND_RESET_I(4);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_wr_xfer = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__w_rd_xfer = VL_RAND_RESET_I(1);
    vlSelf->gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__zeros = VL_RAND_RESET_Q(64);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__axi_aclk = VL_RAND_RESET_I(1);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__axi_aresetn = VL_RAND_RESET_I(1);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_valid = VL_RAND_RESET_I(1);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_ready = VL_RAND_RESET_I(1);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__wr_data = VL_RAND_RESET_Q(64);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__count = VL_RAND_RESET_I(4);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_valid = VL_RAND_RESET_I(1);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_ready = VL_RAND_RESET_I(1);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_count = VL_RAND_RESET_I(4);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__rd_data = VL_RAND_RESET_Q(64);
    VL_RAND_RESET_W(128, vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__r_data_count = VL_RAND_RESET_I(4);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__w_wr_xfer = VL_RAND_RESET_I(1);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__w_rd_xfer = VL_RAND_RESET_I(1);
    vlSelf->gen_output_skid_enabled__DOT__u_output_skid__DOT__zeros = VL_RAND_RESET_Q(64);
}
