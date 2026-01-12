// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop_sram_controller_unit__pi14.h"

VL_INLINE_OPT void Vtop_sram_controller_unit__pi14___ico_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__0(Vtop_sram_controller_unit__pi14* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vtop_sram_controller_unit__pi14___ico_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    SData/*12:0*/ u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 = 0;
    SData/*12:0*/ u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 = 0;
    CData/*0:0*/ u_channel_fifo__DOT____Vcellinp__read_pointer_inst__enable;
    u_channel_fifo__DOT____Vcellinp__read_pointer_inst__enable = 0;
    SData/*12:0*/ u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 = 0;
    CData/*0:0*/ u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__write_pointer_inst__enable;
    u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__write_pointer_inst__enable = 0;
    CData/*2:0*/ u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0;
    u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0 = 0;
    SData/*12:0*/ __VdfgRegularize_h6177457e_0_1;
    __VdfgRegularize_h6177457e_0_1 = 0;
    SData/*12:0*/ __VdfgRegularize_h6177457e_0_3;
    __VdfgRegularize_h6177457e_0_3 = 0;
    SData/*12:0*/ __VdfgRegularize_h6177457e_0_5;
    __VdfgRegularize_h6177457e_0_5 = 0;
    CData/*2:0*/ __VdfgRegularize_h6177457e_0_8;
    __VdfgRegularize_h6177457e_0_8 = 0;
    // Body
    vlSelfRef.drain_data_available = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_alloc_ctrl__DOT__r_wr_full = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_alloc_ctrl__DOT__r_rd_ptr_bin = vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_alloc_ctrl__DOT__r_rd_empty = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_alloc_ctrl__DOT__wr_full = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_alloc_ctrl__DOT__rd_empty = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wr_ptr_for_empty 
        = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed;
    vlSelfRef.u_drain_ctrl__DOT__data_available = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_drain_ctrl__DOT__r_wr_full = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_drain_ctrl__DOT__r_wr_ptr_bin = vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_drain_ctrl__DOT__r_rd_empty = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_drain_ctrl__DOT__wr_full = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_drain_ctrl__DOT__rd_empty = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_drain_ctrl__DOT__w_count = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__count 
        = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wr_ptr_for_empty 
        = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed;
    vlSelfRef.u_channel_fifo__DOT__r_wr_full = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_channel_fifo__DOT__r_rd_empty = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_channel_fifo__DOT__r_wr_ptr_bin = vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_channel_fifo__DOT__r_rd_ptr_bin = vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wr_ptr_for_empty 
        = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed;
    vlSelfRef.u_latency_bridge__DOT__dbg_r_pending 
        = vlSelfRef.u_latency_bridge__DOT__r_drain_ip;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_full 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_empty 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.fifo_count = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_channel_fifo__DOT__count = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__count 
        = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_alloc_ctrl__DOT__w_count = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__count 
        = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_alloc_ctrl__DOT__r_wr_almost_full = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_alloc_ctrl__DOT__wr_almost_full = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_alloc_ctrl__DOT__r_rd_almost_empty 
        = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_alloc_ctrl__DOT__rd_almost_empty = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_drain_ctrl__DOT__r_wr_almost_full = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_drain_ctrl__DOT__wr_almost_full = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_drain_ctrl__DOT__r_rd_almost_empty 
        = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_drain_ctrl__DOT__rd_almost_empty = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_channel_fifo__DOT__rd_data[0U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0U];
    vlSelfRef.u_channel_fifo__DOT__rd_data[1U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[1U];
    vlSelfRef.u_channel_fifo__DOT__rd_data[2U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[2U];
    vlSelfRef.u_channel_fifo__DOT__rd_data[3U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[3U];
    vlSelfRef.u_channel_fifo__DOT__rd_data[4U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[4U];
    vlSelfRef.u_channel_fifo__DOT__rd_data[5U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[5U];
    vlSelfRef.u_channel_fifo__DOT__rd_data[6U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[6U];
    vlSelfRef.u_channel_fifo__DOT__rd_data[7U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[7U];
    vlSelfRef.u_channel_fifo__DOT__rd_data[8U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[8U];
    vlSelfRef.u_channel_fifo__DOT__rd_data[9U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[9U];
    vlSelfRef.u_channel_fifo__DOT__rd_data[0xaU] = 
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xaU];
    vlSelfRef.u_channel_fifo__DOT__rd_data[0xbU] = 
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xbU];
    vlSelfRef.u_channel_fifo__DOT__rd_data[0xcU] = 
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xcU];
    vlSelfRef.u_channel_fifo__DOT__rd_data[0xdU] = 
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xdU];
    vlSelfRef.u_channel_fifo__DOT__rd_data[0xeU] = 
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xeU];
    vlSelfRef.u_channel_fifo__DOT__rd_data[0xfU] = 
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xfU];
    vlSelfRef.u_channel_fifo__DOT__r_wr_almost_full 
        = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_channel_fifo__DOT__r_rd_almost_empty 
        = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_almost_full 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_almost_empty 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_latency_bridge__DOT__skid_wr_valid 
        = vlSelfRef.u_latency_bridge__DOT__r_drain_ip;
    vlSelfRef.alloc_space_free = (0x1fffU & ((IData)(0x1000U) 
                                             - (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__r_count)));
    vlSelfRef.fifo_rd_data_internal[0U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0U];
    vlSelfRef.fifo_rd_data_internal[1U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[1U];
    vlSelfRef.fifo_rd_data_internal[2U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[2U];
    vlSelfRef.fifo_rd_data_internal[3U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[3U];
    vlSelfRef.fifo_rd_data_internal[4U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[4U];
    vlSelfRef.fifo_rd_data_internal[5U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[5U];
    vlSelfRef.fifo_rd_data_internal[6U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[6U];
    vlSelfRef.fifo_rd_data_internal[7U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[7U];
    vlSelfRef.fifo_rd_data_internal[8U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[8U];
    vlSelfRef.fifo_rd_data_internal[9U] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[9U];
    vlSelfRef.fifo_rd_data_internal[0xaU] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xaU];
    vlSelfRef.fifo_rd_data_internal[0xbU] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xbU];
    vlSelfRef.fifo_rd_data_internal[0xcU] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xcU];
    vlSelfRef.fifo_rd_data_internal[0xdU] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xdU];
    vlSelfRef.fifo_rd_data_internal[0xeU] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xeU];
    vlSelfRef.fifo_rd_data_internal[0xfU] = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xfU];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0U] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0U];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[1U] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[1U];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[2U] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[2U];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[3U] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[3U];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[4U] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[4U];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[5U] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[5U];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[6U] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[6U];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[7U] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[7U];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[8U] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[8U];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[9U] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[9U];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xaU] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xaU];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xbU] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xbU];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xcU] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xcU];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xdU] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xdU];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xeU] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xeU];
    vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xfU] 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xfU];
    vlSelfRef.dbg_bridge_pending = vlSelfRef.u_latency_bridge__DOT__r_drain_ip;
    vlSelfRef.u_channel_fifo__DOT__r_wr_addr = (0xfffU 
                                                & (IData)(vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr));
    vlSelfRef.u_channel_fifo__DOT__r_rd_addr = (0xfffU 
                                                & (IData)(vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr));
    vlSelfRef.u_latency_bridge__DOT__w_write_stalled 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__r_drain_ip) 
           & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_full));
    vlSelfRef.u_alloc_ctrl__DOT__wr_ready = (1U & (~ (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_full)));
    vlSelfRef.u_drain_ctrl__DOT__wr_ready = (1U & (~ (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_full)));
    vlSelfRef.u_drain_ctrl__DOT__rd_ready = (1U & (~ (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_empty)));
    vlSelfRef.u_alloc_ctrl__DOT__rd_ready = (1U & (~ (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_empty)));
    vlSelfRef.fifo_rd_valid_internal = (1U & (~ (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_empty)));
    vlSelfRef.axi_rd_sram_ready = (1U & (~ (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_full)));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_addr 
        = (3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr 
        = (3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr));
    vlSelfRef.u_latency_bridge__DOT__skid_wr_ready 
        = (1U & (~ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_full)));
    vlSelfRef.u_latency_bridge__DOT__m_valid = (1U 
                                                & (~ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_empty)));
    vlSelfRef.u_alloc_ctrl__DOT__axi_aresetn = vlSelfRef.rst_n;
    vlSelfRef.u_drain_ctrl__DOT__axi_aresetn = vlSelfRef.rst_n;
    vlSelfRef.u_channel_fifo__DOT__axi_aresetn = vlSelfRef.rst_n;
    vlSelfRef.u_latency_bridge__DOT__rst_n = vlSelfRef.rst_n;
    vlSelfRef.u_alloc_ctrl__DOT__axi_aclk = vlSelfRef.clk;
    vlSelfRef.u_drain_ctrl__DOT__axi_aclk = vlSelfRef.clk;
    vlSelfRef.u_channel_fifo__DOT__axi_aclk = vlSelfRef.clk;
    vlSelfRef.u_latency_bridge__DOT__clk = vlSelfRef.clk;
    vlSelfRef.u_alloc_ctrl__DOT__wr_size = vlSelfRef.axi_rd_alloc_size;
    vlSelfRef.u_channel_fifo__DOT__wr_data[0U] = vlSelfRef.axi_rd_sram_data[0U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[1U] = vlSelfRef.axi_rd_sram_data[1U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[2U] = vlSelfRef.axi_rd_sram_data[2U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[3U] = vlSelfRef.axi_rd_sram_data[3U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[4U] = vlSelfRef.axi_rd_sram_data[4U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[5U] = vlSelfRef.axi_rd_sram_data[5U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[6U] = vlSelfRef.axi_rd_sram_data[6U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[7U] = vlSelfRef.axi_rd_sram_data[7U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[8U] = vlSelfRef.axi_rd_sram_data[8U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[9U] = vlSelfRef.axi_rd_sram_data[9U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xaU] = 
        vlSelfRef.axi_rd_sram_data[0xaU];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xbU] = 
        vlSelfRef.axi_rd_sram_data[0xbU];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xcU] = 
        vlSelfRef.axi_rd_sram_data[0xcU];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xdU] = 
        vlSelfRef.axi_rd_sram_data[0xdU];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xeU] = 
        vlSelfRef.axi_rd_sram_data[0xeU];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xfU] = 
        vlSelfRef.axi_rd_sram_data[0xfU];
    vlSelfRef.u_alloc_ctrl__DOT__wr_valid = vlSelfRef.axi_rd_alloc_req;
    vlSelfRef.u_channel_fifo__DOT__wr_valid = vlSelfRef.axi_rd_sram_valid;
    vlSelfRef.u_drain_ctrl__DOT__rd_size = vlSelfRef.axi_wr_drain_size;
    vlSelfRef.u_drain_ctrl__DOT__rd_valid = vlSelfRef.axi_wr_drain_req;
    vlSelfRef.u_latency_bridge__DOT__m_ready = vlSelfRef.axi_wr_sram_ready;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_valid 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_valid;
    vlSelfRef.u_alloc_ctrl__DOT__space_free = vlSelfRef.alloc_space_free;
    vlSelfRef.u_latency_bridge__DOT__s_data[0U] = vlSelfRef.fifo_rd_data_internal[0U];
    vlSelfRef.u_latency_bridge__DOT__s_data[1U] = vlSelfRef.fifo_rd_data_internal[1U];
    vlSelfRef.u_latency_bridge__DOT__s_data[2U] = vlSelfRef.fifo_rd_data_internal[2U];
    vlSelfRef.u_latency_bridge__DOT__s_data[3U] = vlSelfRef.fifo_rd_data_internal[3U];
    vlSelfRef.u_latency_bridge__DOT__s_data[4U] = vlSelfRef.fifo_rd_data_internal[4U];
    vlSelfRef.u_latency_bridge__DOT__s_data[5U] = vlSelfRef.fifo_rd_data_internal[5U];
    vlSelfRef.u_latency_bridge__DOT__s_data[6U] = vlSelfRef.fifo_rd_data_internal[6U];
    vlSelfRef.u_latency_bridge__DOT__s_data[7U] = vlSelfRef.fifo_rd_data_internal[7U];
    vlSelfRef.u_latency_bridge__DOT__s_data[8U] = vlSelfRef.fifo_rd_data_internal[8U];
    vlSelfRef.u_latency_bridge__DOT__s_data[9U] = vlSelfRef.fifo_rd_data_internal[9U];
    vlSelfRef.u_latency_bridge__DOT__s_data[0xaU] = 
        vlSelfRef.fifo_rd_data_internal[0xaU];
    vlSelfRef.u_latency_bridge__DOT__s_data[0xbU] = 
        vlSelfRef.fifo_rd_data_internal[0xbU];
    vlSelfRef.u_latency_bridge__DOT__s_data[0xcU] = 
        vlSelfRef.fifo_rd_data_internal[0xcU];
    vlSelfRef.u_latency_bridge__DOT__s_data[0xdU] = 
        vlSelfRef.fifo_rd_data_internal[0xdU];
    vlSelfRef.u_latency_bridge__DOT__s_data[0xeU] = 
        vlSelfRef.fifo_rd_data_internal[0xeU];
    vlSelfRef.u_latency_bridge__DOT__s_data[0xfU] = 
        vlSelfRef.fifo_rd_data_internal[0xfU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[0U] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[1U] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[1U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[2U] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[2U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[3U] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[3U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[4U] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[4U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[5U] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[5U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[6U] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[6U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[7U] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[7U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[8U] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[8U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[9U] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[9U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[0xaU] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xaU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[0xbU] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xbU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[0xcU] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xcU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[0xdU] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xdU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[0xeU] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xeU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_data[0xfU] 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xfU];
    vlSelfRef.u_alloc_ctrl__DOT__w_write = ((IData)(vlSelfRef.u_alloc_ctrl__DOT__wr_ready) 
                                            & (IData)(vlSelfRef.axi_rd_alloc_req));
    vlSelfRef.u_drain_ctrl__DOT__w_read = ((IData)(vlSelfRef.u_drain_ctrl__DOT__rd_ready) 
                                           & (IData)(vlSelfRef.axi_wr_drain_req));
    vlSelfRef.u_latency_bridge__DOT__s_valid = vlSelfRef.fifo_rd_valid_internal;
    vlSelfRef.u_channel_fifo__DOT__rd_valid = vlSelfRef.fifo_rd_valid_internal;
    vlSelfRef.u_channel_fifo__DOT__wr_ready = vlSelfRef.axi_rd_sram_ready;
    vlSelfRef.u_channel_fifo__DOT__w_write = ((IData)(vlSelfRef.axi_rd_sram_ready) 
                                              & (IData)(vlSelfRef.axi_rd_sram_valid));
    vlSelfRef.u_latency_bridge__DOT__m_data[0U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0U];
    vlSelfRef.u_latency_bridge__DOT__m_data[1U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][1U];
    vlSelfRef.u_latency_bridge__DOT__m_data[2U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][2U];
    vlSelfRef.u_latency_bridge__DOT__m_data[3U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][3U];
    vlSelfRef.u_latency_bridge__DOT__m_data[4U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][4U];
    vlSelfRef.u_latency_bridge__DOT__m_data[5U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][5U];
    vlSelfRef.u_latency_bridge__DOT__m_data[6U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][6U];
    vlSelfRef.u_latency_bridge__DOT__m_data[7U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][7U];
    vlSelfRef.u_latency_bridge__DOT__m_data[8U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][8U];
    vlSelfRef.u_latency_bridge__DOT__m_data[9U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][9U];
    vlSelfRef.u_latency_bridge__DOT__m_data[0xaU] = 
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xaU];
    vlSelfRef.u_latency_bridge__DOT__m_data[0xbU] = 
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xbU];
    vlSelfRef.u_latency_bridge__DOT__m_data[0xcU] = 
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xcU];
    vlSelfRef.u_latency_bridge__DOT__m_data[0xdU] = 
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xdU];
    vlSelfRef.u_latency_bridge__DOT__m_data[0xeU] = 
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xeU];
    vlSelfRef.u_latency_bridge__DOT__m_data[0xfU] = 
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xfU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[0U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[1U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][1U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[2U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][2U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[3U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][3U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[4U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][4U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[5U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][5U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[6U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][6U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[7U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][7U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[8U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][8U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[9U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][9U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[0xaU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xaU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[0xbU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xbU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[0xcU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xcU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[0xdU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xdU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[0xeU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xeU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_data[0xfU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xfU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[0U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[1U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][1U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[2U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][2U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[3U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][3U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[4U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][4U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[5U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][5U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[6U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][6U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[7U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][7U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[8U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][8U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[9U] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][9U];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[0xaU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xaU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[0xbU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xbU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[0xcU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xcU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[0xdU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xdU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[0xeU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xeU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_data[0xfU] 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xfU];
    vlSelfRef.axi_wr_sram_data[0U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0U];
    vlSelfRef.axi_wr_sram_data[1U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][1U];
    vlSelfRef.axi_wr_sram_data[2U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][2U];
    vlSelfRef.axi_wr_sram_data[3U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][3U];
    vlSelfRef.axi_wr_sram_data[4U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][4U];
    vlSelfRef.axi_wr_sram_data[5U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][5U];
    vlSelfRef.axi_wr_sram_data[6U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][6U];
    vlSelfRef.axi_wr_sram_data[7U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][7U];
    vlSelfRef.axi_wr_sram_data[8U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][8U];
    vlSelfRef.axi_wr_sram_data[9U] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][9U];
    vlSelfRef.axi_wr_sram_data[0xaU] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xaU];
    vlSelfRef.axi_wr_sram_data[0xbU] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xbU];
    vlSelfRef.axi_wr_sram_data[0xcU] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xcU];
    vlSelfRef.axi_wr_sram_data[0xdU] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xdU];
    vlSelfRef.axi_wr_sram_data[0xeU] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xeU];
    vlSelfRef.axi_wr_sram_data[0xfU] = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem
        [vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr][0xfU];
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_ready 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_ready;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_write 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__skid_wr_ready) 
           & (IData)(vlSelfRef.u_latency_bridge__DOT__r_drain_ip));
    vlSelfRef.u_latency_bridge__DOT__dbg_r_out_valid 
        = vlSelfRef.u_latency_bridge__DOT__m_valid;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_valid 
        = vlSelfRef.u_latency_bridge__DOT__m_valid;
    vlSelfRef.dbg_bridge_out_valid = vlSelfRef.u_latency_bridge__DOT__m_valid;
    vlSelfRef.axi_wr_sram_valid = vlSelfRef.u_latency_bridge__DOT__m_valid;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__m_valid) 
           & (IData)(vlSelfRef.axi_wr_sram_ready));
    vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__rst_n 
        = vlSelfRef.u_alloc_ctrl__DOT__axi_aresetn;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_rst_n 
        = vlSelfRef.u_alloc_ctrl__DOT__axi_aresetn;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_rst_n 
        = vlSelfRef.u_alloc_ctrl__DOT__axi_aresetn;
    vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__rst_n 
        = vlSelfRef.u_drain_ctrl__DOT__axi_aresetn;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_rst_n 
        = vlSelfRef.u_drain_ctrl__DOT__axi_aresetn;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_rst_n 
        = vlSelfRef.u_drain_ctrl__DOT__axi_aresetn;
    vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__rst_n 
        = vlSelfRef.u_channel_fifo__DOT__axi_aresetn;
    vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__rst_n 
        = vlSelfRef.u_channel_fifo__DOT__axi_aresetn;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_rst_n 
        = vlSelfRef.u_channel_fifo__DOT__axi_aresetn;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_rst_n 
        = vlSelfRef.u_channel_fifo__DOT__axi_aresetn;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__axi_aresetn 
        = vlSelfRef.u_latency_bridge__DOT__rst_n;
    vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__clk 
        = vlSelfRef.u_alloc_ctrl__DOT__axi_aclk;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_clk 
        = vlSelfRef.u_alloc_ctrl__DOT__axi_aclk;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_clk 
        = vlSelfRef.u_alloc_ctrl__DOT__axi_aclk;
    vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__clk 
        = vlSelfRef.u_drain_ctrl__DOT__axi_aclk;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_clk 
        = vlSelfRef.u_drain_ctrl__DOT__axi_aclk;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_clk 
        = vlSelfRef.u_drain_ctrl__DOT__axi_aclk;
    vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__clk 
        = vlSelfRef.u_channel_fifo__DOT__axi_aclk;
    vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__clk 
        = vlSelfRef.u_channel_fifo__DOT__axi_aclk;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_clk 
        = vlSelfRef.u_channel_fifo__DOT__axi_aclk;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_clk 
        = vlSelfRef.u_channel_fifo__DOT__axi_aclk;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__axi_aclk 
        = vlSelfRef.u_latency_bridge__DOT__clk;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_ready 
        = vlSelfRef.u_latency_bridge__DOT__m_ready;
    vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next 
        = (0x1fffU & ((IData)(vlSelfRef.u_alloc_ctrl__DOT__r_wr_ptr_bin) 
                      + (((IData)(vlSelfRef.u_alloc_ctrl__DOT__wr_ready) 
                          & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_write))
                          ? (IData)(vlSelfRef.axi_rd_alloc_size)
                          : 0U)));
    vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next 
        = (0x1fffU & ((IData)(vlSelfRef.u_drain_ctrl__DOT__r_rd_ptr_bin) 
                      + (((IData)(vlSelfRef.u_drain_ctrl__DOT__rd_ready) 
                          & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_read))
                          ? (IData)(vlSelfRef.axi_wr_drain_size)
                          : 0U)));
    vlSelfRef.u_drain_ctrl__DOT__wr_valid = vlSelfRef.u_channel_fifo__DOT__w_write;
    vlSelfRef.u_channel_fifo__DOT____Vcellinp__write_pointer_inst__enable 
        = ((IData)(vlSelfRef.axi_rd_sram_ready) & (IData)(vlSelfRef.u_channel_fifo__DOT__w_write));
    vlSelfRef.u_drain_ctrl__DOT__w_write = ((IData)(vlSelfRef.u_drain_ctrl__DOT__wr_ready) 
                                            & (IData)(vlSelfRef.u_channel_fifo__DOT__w_write));
    u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__write_pointer_inst__enable 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__skid_wr_ready) 
           & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_write));
    vlSelfRef.u_alloc_ctrl__DOT__rd_valid = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read;
    vlSelfRef.u_latency_bridge__DOT__w_draining_now 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read;
    vlSelfRef.u_alloc_ctrl__DOT__w_read = ((IData)(vlSelfRef.u_alloc_ctrl__DOT__rd_ready) 
                                           & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__read_pointer_inst__enable 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__m_valid) 
           & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__rst_n 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__axi_aresetn;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__rst_n 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__axi_aresetn;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_rst_n 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__axi_aresetn;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_rst_n 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__axi_aresetn;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__clk 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__axi_aclk;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__clk 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__axi_aclk;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_clk 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__axi_aclk;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_clk 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__axi_aclk;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_ptr_bin 
        = vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rdom_wr_ptr_bin 
        = vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wdom_rd_ptr_bin 
        = vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_ptr_bin 
        = vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty 
        = (1U & (((IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed)) 
                 >> 0xcU));
    if (vlSelfRef.u_channel_fifo__DOT____Vcellinp__write_pointer_inst__enable) {
        vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__enable = 1U;
        vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next 
            = (0x1fffU & (((IData)(vlSelfRef.u_channel_fifo__DOT__r_wr_addr) 
                           == (IData)(vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__w_max_val))
                           ? (0x1000U & ((~ ((IData)(vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr) 
                                             >> 0xcU)) 
                                         << 0xcU)) : 
                          ((IData)(1U) + (IData)(vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr))));
    } else {
        vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__enable = 0U;
        vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next 
            = (0x1fffU & (IData)(vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr));
    }
    vlSelfRef.u_drain_ctrl__DOT____Vcellinp__write_pointer_inst__enable 
        = ((IData)(vlSelfRef.u_drain_ctrl__DOT__wr_ready) 
           & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_write));
    if (u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__write_pointer_inst__enable) {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__enable = 1U;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next 
            = (7U & (((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_addr) 
                      == (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__w_max_val))
                      ? (4U & ((~ ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr) 
                                   >> 2U)) << 2U)) : 
                     ((IData)(1U) + (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr))));
    } else {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__enable = 0U;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next 
            = (7U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr));
    }
    vlSelfRef.u_alloc_ctrl__DOT____Vcellinp__read_pointer_inst__enable 
        = ((IData)(vlSelfRef.u_alloc_ctrl__DOT__rd_ready) 
           & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_read));
    if (vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__read_pointer_inst__enable) {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__enable = 1U;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next 
            = (7U & (((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr) 
                      == (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__w_max_val))
                      ? (4U & ((~ ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr) 
                                   >> 2U)) << 2U)) : 
                     ((IData)(1U) + (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr))));
    } else {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__enable = 0U;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next 
            = (7U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr));
    }
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rd_empty_d 
        = ((~ (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty)) 
           & ((IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed) 
              == (IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next)));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_ptr_bin 
        = vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rdom_wr_ptr_bin 
        = vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_next 
        = vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next;
    if (vlSelfRef.u_drain_ctrl__DOT____Vcellinp__write_pointer_inst__enable) {
        vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__enable = 1U;
        vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next 
            = (0x1fffU & (((0xfffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr)) 
                           == (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__w_max_val))
                           ? (0x1000U & ((~ ((IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr) 
                                             >> 0xcU)) 
                                         << 0xcU)) : 
                          ((IData)(1U) + (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr))));
    } else {
        vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__enable = 0U;
        vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next 
            = (0x1fffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr));
    }
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rdom_wr_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_next 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wr_ptr_for_empty 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next;
    if (vlSelfRef.u_alloc_ctrl__DOT____Vcellinp__read_pointer_inst__enable) {
        vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__enable = 1U;
        vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next 
            = (0x1fffU & (((0xfffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr)) 
                           == (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__w_max_val))
                           ? (0x1000U & ((~ ((IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr) 
                                             >> 0xcU)) 
                                         << 0xcU)) : 
                          ((IData)(1U) + (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr))));
    } else {
        vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__enable = 0U;
        vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next 
            = (0x1fffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr));
    }
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wdom_rd_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_next 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next)) 
                 >> 2U));
    __VdfgRegularize_h6177457e_0_8 = (7U & (((IData)(4U) 
                                             - (3U 
                                                & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next))) 
                                            + (3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next))));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next)) 
                 >> 2U));
    u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0 
        = (7U & ((3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next)) 
                 - (3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next))));
    vlSelfRef.u_drain_ctrl__DOT__w_wr_ptr_bin_next 
        = vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next)) 
                 >> 0xcU));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next) 
                  ^ (IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next)) 
                 >> 0xcU));
    __VdfgRegularize_h6177457e_0_3 = (0x1fffU & (((IData)(0x1000U) 
                                                  - 
                                                  (0xfffU 
                                                   & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next))) 
                                                 + 
                                                 (0xfffU 
                                                  & (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next))));
    u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 
        = (0x1fffU & ((0xfffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next)) 
                      - (0xfffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next))));
    vlSelfRef.u_alloc_ctrl__DOT__w_rd_ptr_bin_next 
        = vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty 
        = (1U & (((IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next) 
                  ^ (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed)) 
                 >> 0xcU));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next) 
                  ^ (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next)) 
                 >> 0xcU));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next)) 
                 >> 0xcU));
    __VdfgRegularize_h6177457e_0_1 = (0x1fffU & (((IData)(0x1000U) 
                                                  - 
                                                  (0xfffU 
                                                   & (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next))) 
                                                 + 
                                                 (0xfffU 
                                                  & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next))));
    u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 
        = (0x1fffU & ((0xfffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next)) 
                      - (0xfffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next))));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wr_full_d 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor) 
           & ((3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next)) 
              == (3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next))));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rd_empty_d 
        = ((~ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor)) 
           & ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next) 
              == (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next)));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_almost_full_count 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor)
            ? (IData)(__VdfgRegularize_h6177457e_0_8)
            : (IData)(u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0));
    if (vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor) {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = __VdfgRegularize_h6177457e_0_8;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count 
            = (7U & ((IData)(4U) + (IData)(u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0)));
    } else {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count 
            = (7U & (IData)(u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0));
    }
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_ptr_bin 
        = vlSelfRef.u_drain_ctrl__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rdom_wr_ptr_bin 
        = vlSelfRef.u_drain_ctrl__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wr_full_d 
        = ((IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor) 
           & ((0xfffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next)) 
              == (0xfffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next))));
    if (vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor) {
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & ((IData)(0x1000U) + (IData)(u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1)));
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = __VdfgRegularize_h6177457e_0_3;
    } else {
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & (IData)(u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    }
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_almost_full_count 
        = ((IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor)
            ? (IData)(__VdfgRegularize_h6177457e_0_3)
            : (IData)(u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wdom_rd_ptr_bin 
        = vlSelfRef.u_alloc_ctrl__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_ptr_bin 
        = vlSelfRef.u_alloc_ctrl__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rd_empty_d 
        = ((~ (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty)) 
           & ((IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed) 
              == (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next)));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wr_full_d 
        = ((IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor) 
           & ((0xfffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next)) 
              == (0xfffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next))));
    if (vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor) {
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & ((IData)(0x1000U) + (IData)(u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1)));
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = __VdfgRegularize_h6177457e_0_1;
    } else {
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & (IData)(u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    }
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_almost_full_count 
        = ((IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor)
            ? (IData)(__VdfgRegularize_h6177457e_0_1)
            : (IData)(u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wr_almost_full_d 
        = (3U <= (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_almost_full_count));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d 
        = (1U >= (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_almost_empty_count));
    vlSelfRef.bridge_occupancy = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
    vlSelfRef.u_latency_bridge__DOT__occupancy = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
    vlSelfRef.u_latency_bridge__DOT__skid_count = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__count 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__count 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
    vlSelfRef.u_latency_bridge__DOT__pending_count 
        = (7U & ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count) 
                 + (IData)(vlSelfRef.u_latency_bridge__DOT__w_write_stalled)));
    vlSelfRef.axi_wr_drain_data_avail = (0x1fffU & 
                                         ((IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count) 
                                          + (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count)));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wr_almost_full_d 
        = (0xfffU <= (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_almost_full_count));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d 
        = (1U >= (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wr_almost_full_d 
        = (0xfffU <= (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_almost_full_count));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d 
        = (1U >= (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count));
    vlSelfRef.u_latency_bridge__DOT__w_room_available 
        = (4U > (IData)(vlSelfRef.u_latency_bridge__DOT__pending_count));
    vlSelfRef.u_latency_bridge__DOT__s_ready = ((IData)(vlSelfRef.u_latency_bridge__DOT__w_room_available) 
                                                | (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read));
    vlSelfRef.fifo_rd_ready_internal = vlSelfRef.u_latency_bridge__DOT__s_ready;
    vlSelfRef.u_channel_fifo__DOT__w_read = ((IData)(vlSelfRef.fifo_rd_valid_internal) 
                                             & (IData)(vlSelfRef.u_latency_bridge__DOT__s_ready));
    vlSelfRef.u_channel_fifo__DOT__rd_ready = vlSelfRef.fifo_rd_ready_internal;
    vlSelfRef.u_latency_bridge__DOT__w_drain_fifo = vlSelfRef.u_channel_fifo__DOT__w_read;
    u_channel_fifo__DOT____Vcellinp__read_pointer_inst__enable 
        = ((IData)(vlSelfRef.fifo_rd_valid_internal) 
           & (IData)(vlSelfRef.u_channel_fifo__DOT__w_read));
    if (u_channel_fifo__DOT____Vcellinp__read_pointer_inst__enable) {
        vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__enable = 1U;
        vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next 
            = (0x1fffU & (((IData)(vlSelfRef.u_channel_fifo__DOT__r_rd_addr) 
                           == (IData)(vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__w_max_val))
                           ? (0x1000U & ((~ ((IData)(vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr) 
                                             >> 0xcU)) 
                                         << 0xcU)) : 
                          ((IData)(1U) + (IData)(vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr))));
    } else {
        vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__enable = 0U;
        vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next 
            = (0x1fffU & (IData)(vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr));
    }
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wdom_rd_ptr_bin 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_ptr_bin 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_next 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty 
        = (1U & (((IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed)) 
                 >> 0xcU));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next)) 
                 >> 0xcU));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next)) 
                 >> 0xcU));
    __VdfgRegularize_h6177457e_0_5 = (0x1fffU & (((IData)(0x1000U) 
                                                  - 
                                                  (0xfffU 
                                                   & (IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next))) 
                                                 + 
                                                 (0xfffU 
                                                  & (IData)(vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next))));
    u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 
        = (0x1fffU & ((0xfffU & (IData)(vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next)) 
                      - (0xfffU & (IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next))));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rd_empty_d 
        = ((~ (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty)) 
           & ((IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed) 
              == (IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next)));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wr_full_d 
        = ((IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor) 
           & ((0xfffU & (IData)(vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next)) 
              == (0xfffU & (IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next))));
    if (vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor) {
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & ((IData)(0x1000U) + (IData)(u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1)));
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = __VdfgRegularize_h6177457e_0_5;
    } else {
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & (IData)(u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    }
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_almost_full_count 
        = ((IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor)
            ? (IData)(__VdfgRegularize_h6177457e_0_5)
            : (IData)(u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wr_almost_full_d 
        = (0xfffU <= (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_almost_full_count));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d 
        = (1U >= (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_almost_empty_count));
}

VL_INLINE_OPT void Vtop_sram_controller_unit__pi14___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__0(Vtop_sram_controller_unit__pi14* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vtop_sram_controller_unit__pi14___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.u_alloc_ctrl__DOT__wr_valid = vlSelfRef.axi_rd_alloc_req;
    vlSelfRef.u_drain_ctrl__DOT__rd_valid = vlSelfRef.axi_wr_drain_req;
}

VL_INLINE_OPT void Vtop_sram_controller_unit__pi14___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__2(Vtop_sram_controller_unit__pi14* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vtop_sram_controller_unit__pi14___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__2\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_almost_empty 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_almost_full 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wr_almost_full_d));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_almost_empty 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_almost_full 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wr_almost_full_d));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_almost_empty 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_almost_full 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wr_almost_full_d));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_almost_empty 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_almost_full 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wr_almost_full_d));
    if (vlSelfRef.rst_n) {
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__r_count 
            = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_count;
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__r_count 
            = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_count;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__r_count 
            = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count 
            = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_count;
    } else {
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__r_count = 0U;
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__r_count = 0U;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__r_count = 0U;
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count = 0U;
    }
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_full 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wr_full_d));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_full 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wr_full_d));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_empty 
        = ((1U & (~ (IData)(vlSelfRef.rst_n))) || (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rd_empty_d));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_empty 
        = ((1U & (~ (IData)(vlSelfRef.rst_n))) || (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rd_empty_d));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_empty 
        = ((1U & (~ (IData)(vlSelfRef.rst_n))) || (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rd_empty_d));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_full 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wr_full_d));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_full 
        = ((IData)(vlSelfRef.rst_n) && (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wr_full_d));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_empty 
        = ((1U & (~ (IData)(vlSelfRef.rst_n))) || (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rd_empty_d));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_almost_empty 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_almost_full 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_channel_fifo__DOT__r_rd_almost_empty 
        = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_channel_fifo__DOT__r_wr_almost_full 
        = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_drain_ctrl__DOT__r_rd_almost_empty 
        = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_drain_ctrl__DOT__rd_almost_empty = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_drain_ctrl__DOT__r_wr_almost_full = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_drain_ctrl__DOT__wr_almost_full = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_alloc_ctrl__DOT__r_rd_almost_empty 
        = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_alloc_ctrl__DOT__rd_almost_empty = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelfRef.u_alloc_ctrl__DOT__r_wr_almost_full = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.u_alloc_ctrl__DOT__wr_almost_full = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelfRef.fifo_count = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_channel_fifo__DOT__count = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__count 
        = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_alloc_ctrl__DOT__w_count = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__count 
        = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.alloc_space_free = (0x1fffU & ((IData)(0x1000U) 
                                             - (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__r_count)));
    vlSelfRef.u_alloc_ctrl__DOT__r_wr_full = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_alloc_ctrl__DOT__wr_full = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_alloc_ctrl__DOT__wr_ready = (1U & (~ (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_full)));
    vlSelfRef.u_drain_ctrl__DOT__r_wr_full = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_drain_ctrl__DOT__wr_full = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_drain_ctrl__DOT__wr_ready = (1U & (~ (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_full)));
    vlSelfRef.drain_data_available = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_drain_ctrl__DOT__data_available = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_drain_ctrl__DOT__w_count = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__count 
        = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count;
    vlSelfRef.u_drain_ctrl__DOT__r_rd_empty = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_drain_ctrl__DOT__rd_empty = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_drain_ctrl__DOT__rd_ready = (1U & (~ (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_empty)));
    vlSelfRef.u_alloc_ctrl__DOT__r_rd_empty = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_alloc_ctrl__DOT__rd_empty = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_alloc_ctrl__DOT__rd_ready = (1U & (~ (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_empty)));
    vlSelfRef.u_channel_fifo__DOT__r_rd_empty = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.fifo_rd_valid_internal = (1U & (~ (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_empty)));
    vlSelfRef.u_channel_fifo__DOT__r_wr_full = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.axi_rd_sram_ready = (1U & (~ (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_full)));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_full 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_full;
    vlSelfRef.u_latency_bridge__DOT__skid_wr_ready 
        = (1U & (~ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_full)));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_empty 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelfRef.u_latency_bridge__DOT__m_valid = (1U 
                                                & (~ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_empty)));
    vlSelfRef.u_alloc_ctrl__DOT__space_free = vlSelfRef.alloc_space_free;
    vlSelfRef.u_latency_bridge__DOT__s_valid = vlSelfRef.fifo_rd_valid_internal;
    vlSelfRef.u_channel_fifo__DOT__rd_valid = vlSelfRef.fifo_rd_valid_internal;
    vlSelfRef.u_channel_fifo__DOT__wr_ready = vlSelfRef.axi_rd_sram_ready;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_ready 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_ready;
    vlSelfRef.u_latency_bridge__DOT__dbg_r_out_valid 
        = vlSelfRef.u_latency_bridge__DOT__m_valid;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_valid 
        = vlSelfRef.u_latency_bridge__DOT__m_valid;
    vlSelfRef.dbg_bridge_out_valid = vlSelfRef.u_latency_bridge__DOT__m_valid;
    vlSelfRef.axi_wr_sram_valid = vlSelfRef.u_latency_bridge__DOT__m_valid;
}

VL_INLINE_OPT void Vtop_sram_controller_unit__pi14___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__3(Vtop_sram_controller_unit__pi14* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vtop_sram_controller_unit__pi14___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__3\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.u_channel_fifo__DOT__wr_valid = vlSelfRef.axi_rd_sram_valid;
    vlSelfRef.u_latency_bridge__DOT__m_ready = vlSelfRef.axi_wr_sram_ready;
    vlSelfRef.u_channel_fifo__DOT__wr_data[0U] = vlSelfRef.axi_rd_sram_data[0U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[1U] = vlSelfRef.axi_rd_sram_data[1U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[2U] = vlSelfRef.axi_rd_sram_data[2U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[3U] = vlSelfRef.axi_rd_sram_data[3U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[4U] = vlSelfRef.axi_rd_sram_data[4U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[5U] = vlSelfRef.axi_rd_sram_data[5U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[6U] = vlSelfRef.axi_rd_sram_data[6U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[7U] = vlSelfRef.axi_rd_sram_data[7U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[8U] = vlSelfRef.axi_rd_sram_data[8U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[9U] = vlSelfRef.axi_rd_sram_data[9U];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xaU] = 
        vlSelfRef.axi_rd_sram_data[0xaU];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xbU] = 
        vlSelfRef.axi_rd_sram_data[0xbU];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xcU] = 
        vlSelfRef.axi_rd_sram_data[0xcU];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xdU] = 
        vlSelfRef.axi_rd_sram_data[0xdU];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xeU] = 
        vlSelfRef.axi_rd_sram_data[0xeU];
    vlSelfRef.u_channel_fifo__DOT__wr_data[0xfU] = 
        vlSelfRef.axi_rd_sram_data[0xfU];
    vlSelfRef.u_alloc_ctrl__DOT__wr_size = vlSelfRef.axi_rd_alloc_size;
    vlSelfRef.u_drain_ctrl__DOT__rd_size = vlSelfRef.axi_wr_drain_size;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__rd_ready 
        = vlSelfRef.u_latency_bridge__DOT__m_ready;
}

VL_INLINE_OPT void Vtop_sram_controller_unit__pi14___nba_comb__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__0(Vtop_sram_controller_unit__pi14* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vtop_sram_controller_unit__pi14___nba_comb__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__0\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    CData/*0:0*/ u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__write_pointer_inst__enable;
    u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__write_pointer_inst__enable = 0;
    // Body
    vlSelfRef.u_latency_bridge__DOT__w_write_stalled 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__r_drain_ip) 
           & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_full));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_write 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__skid_wr_ready) 
           & (IData)(vlSelfRef.u_latency_bridge__DOT__r_drain_ip));
    u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__write_pointer_inst__enable 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__skid_wr_ready) 
           & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_write));
    if (u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__write_pointer_inst__enable) {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__enable = 1U;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next 
            = (7U & (((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_addr) 
                      == (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__w_max_val))
                      ? (4U & ((~ ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr) 
                                   >> 2U)) << 2U)) : 
                     ((IData)(1U) + (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr))));
    } else {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__enable = 0U;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next 
            = (7U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr));
    }
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wr_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rdom_wr_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_next 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wr_ptr_for_empty 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next;
}

VL_INLINE_OPT void Vtop_sram_controller_unit__pi14___nba_comb__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__1(Vtop_sram_controller_unit__pi14* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vtop_sram_controller_unit__pi14___nba_comb__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__1\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.u_alloc_ctrl__DOT__w_write = ((IData)(vlSelfRef.u_alloc_ctrl__DOT__wr_ready) 
                                            & (IData)(vlSelfRef.axi_rd_alloc_req));
    vlSelfRef.u_drain_ctrl__DOT__w_read = ((IData)(vlSelfRef.u_drain_ctrl__DOT__rd_ready) 
                                           & (IData)(vlSelfRef.axi_wr_drain_req));
    vlSelfRef.u_channel_fifo__DOT__w_write = ((IData)(vlSelfRef.axi_rd_sram_ready) 
                                              & (IData)(vlSelfRef.axi_rd_sram_valid));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__m_valid) 
           & (IData)(vlSelfRef.axi_wr_sram_ready));
    vlSelfRef.u_drain_ctrl__DOT__wr_valid = vlSelfRef.u_channel_fifo__DOT__w_write;
    vlSelfRef.u_channel_fifo__DOT____Vcellinp__write_pointer_inst__enable 
        = ((IData)(vlSelfRef.axi_rd_sram_ready) & (IData)(vlSelfRef.u_channel_fifo__DOT__w_write));
    vlSelfRef.u_drain_ctrl__DOT__w_write = ((IData)(vlSelfRef.u_drain_ctrl__DOT__wr_ready) 
                                            & (IData)(vlSelfRef.u_channel_fifo__DOT__w_write));
    vlSelfRef.u_alloc_ctrl__DOT__rd_valid = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read;
    vlSelfRef.u_latency_bridge__DOT__w_draining_now 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read;
    vlSelfRef.u_alloc_ctrl__DOT__w_read = ((IData)(vlSelfRef.u_alloc_ctrl__DOT__rd_ready) 
                                           & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__read_pointer_inst__enable 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__m_valid) 
           & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read));
    vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__enable 
        = vlSelfRef.u_channel_fifo__DOT____Vcellinp__write_pointer_inst__enable;
    vlSelfRef.u_drain_ctrl__DOT____Vcellinp__write_pointer_inst__enable 
        = ((IData)(vlSelfRef.u_drain_ctrl__DOT__wr_ready) 
           & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_write));
    vlSelfRef.u_alloc_ctrl__DOT____Vcellinp__read_pointer_inst__enable 
        = ((IData)(vlSelfRef.u_alloc_ctrl__DOT__rd_ready) 
           & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_read));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__enable 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__read_pointer_inst__enable;
    vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__enable 
        = vlSelfRef.u_drain_ctrl__DOT____Vcellinp__write_pointer_inst__enable;
    vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__enable 
        = vlSelfRef.u_alloc_ctrl__DOT____Vcellinp__read_pointer_inst__enable;
}

VL_INLINE_OPT void Vtop_sram_controller_unit__pi14___nba_comb__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__2(Vtop_sram_controller_unit__pi14* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vtop_sram_controller_unit__pi14___nba_comb__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__2\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    SData/*12:0*/ u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 = 0;
    SData/*12:0*/ u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 = 0;
    CData/*0:0*/ u_channel_fifo__DOT____Vcellinp__read_pointer_inst__enable;
    u_channel_fifo__DOT____Vcellinp__read_pointer_inst__enable = 0;
    SData/*12:0*/ u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 = 0;
    CData/*2:0*/ u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0;
    u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0 = 0;
    SData/*12:0*/ __VdfgRegularize_h6177457e_0_1;
    __VdfgRegularize_h6177457e_0_1 = 0;
    SData/*12:0*/ __VdfgRegularize_h6177457e_0_3;
    __VdfgRegularize_h6177457e_0_3 = 0;
    SData/*12:0*/ __VdfgRegularize_h6177457e_0_5;
    __VdfgRegularize_h6177457e_0_5 = 0;
    CData/*2:0*/ __VdfgRegularize_h6177457e_0_8;
    __VdfgRegularize_h6177457e_0_8 = 0;
    // Body
    vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next 
        = (0x1fffU & ((IData)(vlSelfRef.u_alloc_ctrl__DOT__r_wr_ptr_bin) 
                      + (((IData)(vlSelfRef.u_alloc_ctrl__DOT__wr_ready) 
                          & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_write))
                          ? (IData)(vlSelfRef.axi_rd_alloc_size)
                          : 0U)));
    vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next 
        = (0x1fffU & ((IData)(vlSelfRef.u_drain_ctrl__DOT__r_rd_ptr_bin) 
                      + (((IData)(vlSelfRef.u_drain_ctrl__DOT__rd_ready) 
                          & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_read))
                          ? (IData)(vlSelfRef.axi_wr_drain_size)
                          : 0U)));
    vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next 
        = (0x1fffU & ((IData)(vlSelfRef.u_channel_fifo__DOT____Vcellinp__write_pointer_inst__enable)
                       ? (((IData)(vlSelfRef.u_channel_fifo__DOT__r_wr_addr) 
                           == (IData)(vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__w_max_val))
                           ? (0x1000U & ((~ ((IData)(vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr) 
                                             >> 0xcU)) 
                                         << 0xcU)) : 
                          ((IData)(1U) + (IData)(vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr)))
                       : (IData)(vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr)));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next 
        = (7U & ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT____Vcellinp__read_pointer_inst__enable)
                  ? (((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr) 
                      == (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__w_max_val))
                      ? (4U & ((~ ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr) 
                                   >> 2U)) << 2U)) : 
                     ((IData)(1U) + (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr)))
                  : (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr)));
    vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next 
        = (0x1fffU & ((IData)(vlSelfRef.u_drain_ctrl__DOT____Vcellinp__write_pointer_inst__enable)
                       ? (((0xfffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr)) 
                           == (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__w_max_val))
                           ? (0x1000U & ((~ ((IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr) 
                                             >> 0xcU)) 
                                         << 0xcU)) : 
                          ((IData)(1U) + (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr)))
                       : (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr)));
    vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next 
        = (0x1fffU & ((IData)(vlSelfRef.u_alloc_ctrl__DOT____Vcellinp__read_pointer_inst__enable)
                       ? (((0xfffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr)) 
                           == (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__w_max_val))
                           ? (0x1000U & ((~ ((IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr) 
                                             >> 0xcU)) 
                                         << 0xcU)) : 
                          ((IData)(1U) + (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr)))
                       : (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr)));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wr_ptr_bin 
        = vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rdom_wr_ptr_bin 
        = vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wdom_rd_ptr_bin 
        = vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rd_ptr_bin 
        = vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty 
        = (1U & (((IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed)) 
                 >> 0xcU));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wr_ptr_bin 
        = vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rdom_wr_ptr_bin 
        = vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_next 
        = vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__wdom_rd_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__rd_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_next 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next)) 
                 >> 2U));
    __VdfgRegularize_h6177457e_0_8 = (7U & (((IData)(4U) 
                                             - (3U 
                                                & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next))) 
                                            + (3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next))));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next)) 
                 >> 2U));
    u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0 
        = (7U & ((3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next)) 
                 - (3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next))));
    vlSelfRef.u_drain_ctrl__DOT__w_wr_ptr_bin_next 
        = vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next)) 
                 >> 0xcU));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next) 
                  ^ (IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next)) 
                 >> 0xcU));
    __VdfgRegularize_h6177457e_0_3 = (0x1fffU & (((IData)(0x1000U) 
                                                  - 
                                                  (0xfffU 
                                                   & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next))) 
                                                 + 
                                                 (0xfffU 
                                                  & (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next))));
    u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 
        = (0x1fffU & ((0xfffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next)) 
                      - (0xfffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next))));
    vlSelfRef.u_alloc_ctrl__DOT__w_rd_ptr_bin_next 
        = vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty 
        = (1U & (((IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next) 
                  ^ (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed)) 
                 >> 0xcU));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next) 
                  ^ (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next)) 
                 >> 0xcU));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next)) 
                 >> 0xcU));
    __VdfgRegularize_h6177457e_0_1 = (0x1fffU & (((IData)(0x1000U) 
                                                  - 
                                                  (0xfffU 
                                                   & (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next))) 
                                                 + 
                                                 (0xfffU 
                                                  & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next))));
    u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 
        = (0x1fffU & ((0xfffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next)) 
                      - (0xfffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next))));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rd_empty_d 
        = ((~ (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty)) 
           & ((IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed) 
              == (IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next)));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wr_full_d 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor) 
           & ((3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next)) 
              == (3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next))));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rd_empty_d 
        = ((~ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor)) 
           & ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_rd_ptr_bin_next) 
              == (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_wr_ptr_bin_next)));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_almost_full_count 
        = ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor)
            ? (IData)(__VdfgRegularize_h6177457e_0_8)
            : (IData)(u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0));
    if (vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor) {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = __VdfgRegularize_h6177457e_0_8;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count 
            = (7U & ((IData)(4U) + (IData)(u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0)));
    } else {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count 
            = (7U & (IData)(u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT____VdfgRegularize_hff262715_1_0));
    }
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__wr_ptr_bin 
        = vlSelfRef.u_drain_ctrl__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__rdom_wr_ptr_bin 
        = vlSelfRef.u_drain_ctrl__DOT__w_wr_ptr_bin_next;
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wr_full_d 
        = ((IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor) 
           & ((0xfffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next)) 
              == (0xfffU & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_rd_ptr_bin_next))));
    if (vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor) {
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & ((IData)(0x1000U) + (IData)(u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1)));
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = __VdfgRegularize_h6177457e_0_3;
    } else {
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & (IData)(u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    }
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_almost_full_count 
        = ((IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor)
            ? (IData)(__VdfgRegularize_h6177457e_0_3)
            : (IData)(u_drain_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__wdom_rd_ptr_bin 
        = vlSelfRef.u_alloc_ctrl__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__rd_ptr_bin 
        = vlSelfRef.u_alloc_ctrl__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rd_empty_d 
        = ((~ (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty)) 
           & ((IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed) 
              == (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next)));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wr_full_d 
        = ((IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor) 
           & ((0xfffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next)) 
              == (0xfffU & (IData)(vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next))));
    if (vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor) {
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & ((IData)(0x1000U) + (IData)(u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1)));
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = __VdfgRegularize_h6177457e_0_1;
    } else {
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & (IData)(u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    }
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_almost_full_count 
        = ((IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor)
            ? (IData)(__VdfgRegularize_h6177457e_0_1)
            : (IData)(u_alloc_ctrl__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_wr_almost_full_d 
        = (3U <= (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_almost_full_count));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d 
        = (1U >= (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_almost_empty_count));
    vlSelfRef.bridge_occupancy = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
    vlSelfRef.u_latency_bridge__DOT__occupancy = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
    vlSelfRef.u_latency_bridge__DOT__skid_count = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__count 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__count 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count;
    vlSelfRef.u_latency_bridge__DOT__pending_count 
        = (7U & ((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count) 
                 + (IData)(vlSelfRef.u_latency_bridge__DOT__w_write_stalled)));
    vlSelfRef.axi_wr_drain_data_avail = (0x1fffU & 
                                         ((IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__r_count) 
                                          + (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__w_count)));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wr_almost_full_d 
        = (0xfffU <= (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_almost_full_count));
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d 
        = (1U >= (IData)(vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wr_almost_full_d 
        = (0xfffU <= (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_almost_full_count));
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d 
        = (1U >= (IData)(vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_almost_empty_count));
    vlSelfRef.u_latency_bridge__DOT__w_room_available 
        = (4U > (IData)(vlSelfRef.u_latency_bridge__DOT__pending_count));
    vlSelfRef.u_latency_bridge__DOT__s_ready = ((IData)(vlSelfRef.u_latency_bridge__DOT__w_room_available) 
                                                | (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read));
    vlSelfRef.fifo_rd_ready_internal = vlSelfRef.u_latency_bridge__DOT__s_ready;
    vlSelfRef.u_channel_fifo__DOT__w_read = ((IData)(vlSelfRef.fifo_rd_valid_internal) 
                                             & (IData)(vlSelfRef.u_latency_bridge__DOT__s_ready));
    vlSelfRef.u_channel_fifo__DOT__rd_ready = vlSelfRef.fifo_rd_ready_internal;
    vlSelfRef.u_latency_bridge__DOT__w_drain_fifo = vlSelfRef.u_channel_fifo__DOT__w_read;
    u_channel_fifo__DOT____Vcellinp__read_pointer_inst__enable 
        = ((IData)(vlSelfRef.fifo_rd_valid_internal) 
           & (IData)(vlSelfRef.u_channel_fifo__DOT__w_read));
    if (u_channel_fifo__DOT____Vcellinp__read_pointer_inst__enable) {
        vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__enable = 1U;
        vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next 
            = (0x1fffU & (((IData)(vlSelfRef.u_channel_fifo__DOT__r_rd_addr) 
                           == (IData)(vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__w_max_val))
                           ? (0x1000U & ((~ ((IData)(vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr) 
                                             >> 0xcU)) 
                                         << 0xcU)) : 
                          ((IData)(1U) + (IData)(vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr))));
    } else {
        vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__enable = 0U;
        vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next 
            = (0x1fffU & (IData)(vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr));
    }
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__wdom_rd_ptr_bin 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__rd_ptr_bin 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_next 
        = vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty 
        = (1U & (((IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed)) 
                 >> 0xcU));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next)) 
                 >> 0xcU));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor 
        = (1U & (((IData)(vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next) 
                  ^ (IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next)) 
                 >> 0xcU));
    __VdfgRegularize_h6177457e_0_5 = (0x1fffU & (((IData)(0x1000U) 
                                                  - 
                                                  (0xfffU 
                                                   & (IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next))) 
                                                 + 
                                                 (0xfffU 
                                                  & (IData)(vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next))));
    u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1 
        = (0x1fffU & ((0xfffU & (IData)(vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next)) 
                      - (0xfffU & (IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next))));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rd_empty_d 
        = ((~ (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty)) 
           & ((IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed) 
              == (IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next)));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wr_full_d 
        = ((IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor) 
           & ((0xfffU & (IData)(vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next)) 
              == (0xfffU & (IData)(vlSelfRef.u_channel_fifo__DOT__w_rd_ptr_bin_next))));
    if (vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor) {
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & ((IData)(0x1000U) + (IData)(u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1)));
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = __VdfgRegularize_h6177457e_0_5;
    } else {
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_count 
            = (0x1fffU & (IData)(u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_almost_empty_count 
            = u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1;
    }
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_almost_full_count 
        = ((IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor)
            ? (IData)(__VdfgRegularize_h6177457e_0_5)
            : (IData)(u_channel_fifo__DOT__fifo_control_inst__DOT____VdfgRegularize_h589ac4a0_1_1));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wr_almost_full_d 
        = (0xfffU <= (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_almost_full_count));
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d 
        = (1U >= (IData)(vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_almost_empty_count));
}
