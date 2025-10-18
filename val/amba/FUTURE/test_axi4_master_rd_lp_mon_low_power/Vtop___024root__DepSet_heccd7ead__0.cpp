// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop___024root.h"

VL_INLINE_OPT void Vtop___024root___ico_sequent__TOP__0(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___ico_sequent__TOP__0\n"); );
    // Init
    CData/*0:0*/ axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__fub_axi_arvalid;
    axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__fub_axi_arvalid = 0;
    IData/*31:0*/ axi4_master_rd_lp_mon__DOT____VdfgTmp_hf422e32c__0;
    axi4_master_rd_lp_mon__DOT____VdfgTmp_hf422e32c__0 = 0;
    CData/*0:0*/ axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h3626690e__0;
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h3626690e__0 = 0;
    CData/*0:0*/ axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_hb4160c0e__0;
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_hb4160c0e__0 = 0;
    CData/*0:0*/ axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h89982639__0;
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h89982639__0 = 0;
    CData/*0:0*/ axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT____Vcellinp__write_pointer_inst__enable;
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT____Vcellinp__write_pointer_inst__enable = 0;
    CData/*0:0*/ axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT____Vcellinp__read_pointer_inst__enable;
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT____Vcellinp__read_pointer_inst__enable = 0;
    CData/*2:0*/ __VdfgTmp_h0605e096__0;
    __VdfgTmp_h0605e096__0 = 0;
    CData/*2:0*/ __VdfgTmp_he93352a5__0;
    __VdfgTmp_he93352a5__0 = 0;
    CData/*3:0*/ __Vfunc_get_packet_type__0__Vfuncout;
    __Vfunc_get_packet_type__0__Vfuncout = 0;
    QData/*63:0*/ __Vfunc_get_packet_type__0__pkt;
    __Vfunc_get_packet_type__0__pkt = 0;
    CData/*3:0*/ __Vfunc_get_event_code__1__Vfuncout;
    __Vfunc_get_event_code__1__Vfuncout = 0;
    QData/*63:0*/ __Vfunc_get_event_code__1__pkt;
    __Vfunc_get_event_code__1__pkt = 0;
    QData/*35:0*/ __Vfunc_get_event_data__2__Vfuncout;
    __Vfunc_get_event_data__2__Vfuncout = 0;
    QData/*63:0*/ __Vfunc_get_event_data__2__pkt;
    __Vfunc_get_event_data__2__pkt = 0;
    // Body
    vlSelf->axi4_master_rd_lp_mon__DOT__aclk = vlSelf->aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__aresetn = vlSelf->aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arvalid 
        = vlSelf->fub_axi_arvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_lp_enable 
        = vlSelf->cfg_lp_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_sleep_enable 
        = vlSelf->cfg_sleep_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_sleep_threshold 
        = vlSelf->cfg_sleep_threshold;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_coalesce_enable 
        = vlSelf->cfg_coalesce_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_coalesce_window 
        = vlSelf->cfg_coalesce_window;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_power_budget_enable 
        = vlSelf->cfg_power_budget_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_power_budget_limit 
        = vlSelf->cfg_power_budget_limit;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_power_budget_window 
        = vlSelf->cfg_power_budget_window;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_dvfs_enable 
        = vlSelf->cfg_dvfs_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_vf_level 
        = vlSelf->cfg_vf_level;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_vf_auto 
        = vlSelf->cfg_vf_auto;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_pkt_mask 
        = vlSelf->cfg_axi_pkt_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_power_event_mask 
        = vlSelf->cfg_power_event_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_power_sample_rate 
        = vlSelf->cfg_power_sample_rate;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_cg_idle_threshold 
        = vlSelf->cfg_cg_idle_threshold;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_cg_ultra_aggressive 
        = vlSelf->cfg_cg_ultra_aggressive;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_debug_level 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_debug_level;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_debug_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_debug_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 0xffffffffU;
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 0U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [1U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 1U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [2U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 2U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [3U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 3U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [4U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 4U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [5U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 5U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [6U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 6U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [7U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 7U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [8U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 8U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [9U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 9U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xaU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 0xaU;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xbU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 0xbU;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xcU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 0xcU;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xdU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 0xdU;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xeU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 0xeU;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xfU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_free_idx = 0xfU;
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xfffeU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | ((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                     [0U][8U] >> 0x18U)) && (1U & (
                                                   (3U 
                                                    == 
                                                    (7U 
                                                     & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                        [0U][8U] 
                                                        >> 0xfU)))
                                                    ? 
                                                   (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [0U][8U] 
                                                    >> 0x13U)
                                                    : 
                                                   (((4U 
                                                      == 
                                                      (7U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [0U][8U] 
                                                          >> 0xfU))) 
                                                     || (5U 
                                                         == 
                                                         (7U 
                                                          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                             [0U][8U] 
                                                             >> 0xfU)))) 
                                                    && (1U 
                                                        & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                           [0U][8U] 
                                                           >> 0x13U)))))));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xfffdU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [1U][8U] >> 0x18U)) && (1U & 
                                              ((3U 
                                                == 
                                                (7U 
                                                 & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [1U][8U] 
                                                    >> 0xfU)))
                                                ? (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                   [1U][8U] 
                                                   >> 0x13U)
                                                : (
                                                   ((4U 
                                                     == 
                                                     (7U 
                                                      & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                         [1U][8U] 
                                                         >> 0xfU))) 
                                                    || (5U 
                                                        == 
                                                        (7U 
                                                         & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                            [1U][8U] 
                                                            >> 0xfU)))) 
                                                   && (1U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [1U][8U] 
                                                          >> 0x13U)))))) 
              << 1U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xfffbU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [2U][8U] >> 0x18U)) && (1U & 
                                              ((3U 
                                                == 
                                                (7U 
                                                 & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [2U][8U] 
                                                    >> 0xfU)))
                                                ? (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                   [2U][8U] 
                                                   >> 0x13U)
                                                : (
                                                   ((4U 
                                                     == 
                                                     (7U 
                                                      & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                         [2U][8U] 
                                                         >> 0xfU))) 
                                                    || (5U 
                                                        == 
                                                        (7U 
                                                         & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                            [2U][8U] 
                                                            >> 0xfU)))) 
                                                   && (1U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [2U][8U] 
                                                          >> 0x13U)))))) 
              << 2U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xfff7U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [3U][8U] >> 0x18U)) && (1U & 
                                              ((3U 
                                                == 
                                                (7U 
                                                 & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [3U][8U] 
                                                    >> 0xfU)))
                                                ? (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                   [3U][8U] 
                                                   >> 0x13U)
                                                : (
                                                   ((4U 
                                                     == 
                                                     (7U 
                                                      & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                         [3U][8U] 
                                                         >> 0xfU))) 
                                                    || (5U 
                                                        == 
                                                        (7U 
                                                         & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                            [3U][8U] 
                                                            >> 0xfU)))) 
                                                   && (1U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [3U][8U] 
                                                          >> 0x13U)))))) 
              << 3U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xffefU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [4U][8U] >> 0x18U)) && (1U & 
                                              ((3U 
                                                == 
                                                (7U 
                                                 & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [4U][8U] 
                                                    >> 0xfU)))
                                                ? (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                   [4U][8U] 
                                                   >> 0x13U)
                                                : (
                                                   ((4U 
                                                     == 
                                                     (7U 
                                                      & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                         [4U][8U] 
                                                         >> 0xfU))) 
                                                    || (5U 
                                                        == 
                                                        (7U 
                                                         & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                            [4U][8U] 
                                                            >> 0xfU)))) 
                                                   && (1U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [4U][8U] 
                                                          >> 0x13U)))))) 
              << 4U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xffdfU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [5U][8U] >> 0x18U)) && (1U & 
                                              ((3U 
                                                == 
                                                (7U 
                                                 & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [5U][8U] 
                                                    >> 0xfU)))
                                                ? (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                   [5U][8U] 
                                                   >> 0x13U)
                                                : (
                                                   ((4U 
                                                     == 
                                                     (7U 
                                                      & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                         [5U][8U] 
                                                         >> 0xfU))) 
                                                    || (5U 
                                                        == 
                                                        (7U 
                                                         & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                            [5U][8U] 
                                                            >> 0xfU)))) 
                                                   && (1U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [5U][8U] 
                                                          >> 0x13U)))))) 
              << 5U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xffbfU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [6U][8U] >> 0x18U)) && (1U & 
                                              ((3U 
                                                == 
                                                (7U 
                                                 & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [6U][8U] 
                                                    >> 0xfU)))
                                                ? (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                   [6U][8U] 
                                                   >> 0x13U)
                                                : (
                                                   ((4U 
                                                     == 
                                                     (7U 
                                                      & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                         [6U][8U] 
                                                         >> 0xfU))) 
                                                    || (5U 
                                                        == 
                                                        (7U 
                                                         & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                            [6U][8U] 
                                                            >> 0xfU)))) 
                                                   && (1U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [6U][8U] 
                                                          >> 0x13U)))))) 
              << 6U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xff7fU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [7U][8U] >> 0x18U)) && (1U & 
                                              ((3U 
                                                == 
                                                (7U 
                                                 & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [7U][8U] 
                                                    >> 0xfU)))
                                                ? (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                   [7U][8U] 
                                                   >> 0x13U)
                                                : (
                                                   ((4U 
                                                     == 
                                                     (7U 
                                                      & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                         [7U][8U] 
                                                         >> 0xfU))) 
                                                    || (5U 
                                                        == 
                                                        (7U 
                                                         & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                            [7U][8U] 
                                                            >> 0xfU)))) 
                                                   && (1U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [7U][8U] 
                                                          >> 0x13U)))))) 
              << 7U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xfeffU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [8U][8U] >> 0x18U)) && (1U & 
                                              ((3U 
                                                == 
                                                (7U 
                                                 & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [8U][8U] 
                                                    >> 0xfU)))
                                                ? (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                   [8U][8U] 
                                                   >> 0x13U)
                                                : (
                                                   ((4U 
                                                     == 
                                                     (7U 
                                                      & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                         [8U][8U] 
                                                         >> 0xfU))) 
                                                    || (5U 
                                                        == 
                                                        (7U 
                                                         & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                            [8U][8U] 
                                                            >> 0xfU)))) 
                                                   && (1U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [8U][8U] 
                                                          >> 0x13U)))))) 
              << 8U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xfdffU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [9U][8U] >> 0x18U)) && (1U & 
                                              ((3U 
                                                == 
                                                (7U 
                                                 & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [9U][8U] 
                                                    >> 0xfU)))
                                                ? (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                   [9U][8U] 
                                                   >> 0x13U)
                                                : (
                                                   ((4U 
                                                     == 
                                                     (7U 
                                                      & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                         [9U][8U] 
                                                         >> 0xfU))) 
                                                    || (5U 
                                                        == 
                                                        (7U 
                                                         & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                            [9U][8U] 
                                                            >> 0xfU)))) 
                                                   && (1U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [9U][8U] 
                                                          >> 0x13U)))))) 
              << 9U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xfbffU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [0xaU][8U] >> 0x18U)) && (1U 
                                                & ((3U 
                                                    == 
                                                    (7U 
                                                     & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                        [0xaU][8U] 
                                                        >> 0xfU)))
                                                    ? 
                                                   (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [0xaU][8U] 
                                                    >> 0x13U)
                                                    : 
                                                   (((4U 
                                                      == 
                                                      (7U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [0xaU][8U] 
                                                          >> 0xfU))) 
                                                     || (5U 
                                                         == 
                                                         (7U 
                                                          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                             [0xaU][8U] 
                                                             >> 0xfU)))) 
                                                    && (1U 
                                                        & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                           [0xaU][8U] 
                                                           >> 0x13U)))))) 
              << 0xaU));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xf7ffU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [0xbU][8U] >> 0x18U)) && (1U 
                                                & ((3U 
                                                    == 
                                                    (7U 
                                                     & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                        [0xbU][8U] 
                                                        >> 0xfU)))
                                                    ? 
                                                   (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [0xbU][8U] 
                                                    >> 0x13U)
                                                    : 
                                                   (((4U 
                                                      == 
                                                      (7U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [0xbU][8U] 
                                                          >> 0xfU))) 
                                                     || (5U 
                                                         == 
                                                         (7U 
                                                          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                             [0xbU][8U] 
                                                             >> 0xfU)))) 
                                                    && (1U 
                                                        & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                           [0xbU][8U] 
                                                           >> 0x13U)))))) 
              << 0xbU));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xefffU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [0xcU][8U] >> 0x18U)) && (1U 
                                                & ((3U 
                                                    == 
                                                    (7U 
                                                     & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                        [0xcU][8U] 
                                                        >> 0xfU)))
                                                    ? 
                                                   (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [0xcU][8U] 
                                                    >> 0x13U)
                                                    : 
                                                   (((4U 
                                                      == 
                                                      (7U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [0xcU][8U] 
                                                          >> 0xfU))) 
                                                     || (5U 
                                                         == 
                                                         (7U 
                                                          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                             [0xcU][8U] 
                                                             >> 0xfU)))) 
                                                    && (1U 
                                                        & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                           [0xcU][8U] 
                                                           >> 0x13U)))))) 
              << 0xcU));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xdfffU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [0xdU][8U] >> 0x18U)) && (1U 
                                                & ((3U 
                                                    == 
                                                    (7U 
                                                     & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                        [0xdU][8U] 
                                                        >> 0xfU)))
                                                    ? 
                                                   (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [0xdU][8U] 
                                                    >> 0x13U)
                                                    : 
                                                   (((4U 
                                                      == 
                                                      (7U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [0xdU][8U] 
                                                          >> 0xfU))) 
                                                     || (5U 
                                                         == 
                                                         (7U 
                                                          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                             [0xdU][8U] 
                                                             >> 0xfU)))) 
                                                    && (1U 
                                                        & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                           [0xdU][8U] 
                                                           >> 0x13U)))))) 
              << 0xdU));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0xbfffU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [0xeU][8U] >> 0x18U)) && (1U 
                                                & ((3U 
                                                    == 
                                                    (7U 
                                                     & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                        [0xeU][8U] 
                                                        >> 0xfU)))
                                                    ? 
                                                   (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [0xeU][8U] 
                                                    >> 0x13U)
                                                    : 
                                                   (((4U 
                                                      == 
                                                      (7U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [0xeU][8U] 
                                                          >> 0xfU))) 
                                                     || (5U 
                                                         == 
                                                         (7U 
                                                          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                             [0xeU][8U] 
                                                             >> 0xfU)))) 
                                                    && (1U 
                                                        & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                           [0xeU][8U] 
                                                           >> 0x13U)))))) 
              << 0xeU));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup 
        = ((0x7fffU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_can_cleanup)) 
           | (((1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                      [0xfU][8U] >> 0x18U)) && (1U 
                                                & ((3U 
                                                    == 
                                                    (7U 
                                                     & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                        [0xfU][8U] 
                                                        >> 0xfU)))
                                                    ? 
                                                   (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                    [0xfU][8U] 
                                                    >> 0x13U)
                                                    : 
                                                   (((4U 
                                                      == 
                                                      (7U 
                                                       & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                          [0xfU][8U] 
                                                          >> 0xfU))) 
                                                     || (5U 
                                                         == 
                                                         (7U 
                                                          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                             [0xfU][8U] 
                                                             >> 0xfU)))) 
                                                    && (1U 
                                                        & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                           [0xfU][8U] 
                                                           >> 0x13U)))))) 
              << 0xfU));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 0xffffffffU;
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 0U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [1U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 1U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [2U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 2U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [3U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 3U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [4U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 4U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [5U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 5U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [6U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 6U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [7U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 7U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [8U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 8U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [9U][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 9U;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xaU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 0xaU;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xbU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 0xbU;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xcU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 0xcU;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xdU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 0xdU;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xeU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 0xeU;
    }
    if (((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx) 
         & (~ (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
               [0xfU][8U] >> 0x18U)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_free_idx = 0xfU;
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__clear 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__r_clear_pulse;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__loadval 
        = (0xffffU & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__w_division_factor) 
                      - (IData)(1U)));
    vlSelf->power_budget_exceeded = vlSelf->axi4_master_rd_lp_mon__DOT__power_budget_exceeded;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_wr_full 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__wr_full;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_rd_empty 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_wr_ptr_bin 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_rd_ptr_bin 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[0U] 
        = (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                  [0U]);
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[1U] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [1U]) << 0x14U) | (IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                               [0U] 
                                               >> 0x20U)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[2U] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [1U]) >> 0xcU) | ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                               [1U] 
                                               >> 0x20U)) 
                                      << 0x14U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[3U] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [2U]) << 8U) | ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                             [1U] >> 0x20U)) 
                                    >> 0xcU));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[4U] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [3U]) << 0x1cU) | (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                                [2U]) 
                                        >> 0x18U) | 
                                       ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                                 [2U] 
                                                 >> 0x20U)) 
                                        << 8U)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[5U] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [3U]) >> 4U) | ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                             [3U] >> 0x20U)) 
                                    << 0x1cU));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[6U] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [4U]) << 0x10U) | ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                                [3U] 
                                                >> 0x20U)) 
                                       >> 4U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[7U] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [4U]) >> 0x10U) | ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                                [4U] 
                                                >> 0x20U)) 
                                       << 0x10U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[8U] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [5U]) << 4U) | ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                             [4U] >> 0x20U)) 
                                    >> 0x10U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[9U] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [6U]) << 0x18U) | (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                                [5U]) 
                                        >> 0x1cU) | 
                                       ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                                 [5U] 
                                                 >> 0x20U)) 
                                        << 4U)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[0xaU] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [6U]) >> 8U) | ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                             [6U] >> 0x20U)) 
                                    << 0x18U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[0xbU] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [7U]) << 0xcU) | ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                               [6U] 
                                               >> 0x20U)) 
                                      >> 8U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__flat_r_mem[0xcU] 
        = (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                    [7U]) >> 0x14U) | ((IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
                                                [7U] 
                                                >> 0x20U)) 
                                       << 0xcU));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_wr_ptr_for_empty 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__rd_data 
        = (0xfffffffffffULL & (((QData)((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__r_data[1U])) 
                                << 0x20U) | (QData)((IData)(
                                                            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__r_data[0U]))));
    vlSelf->power_consumption = vlSelf->axi4_master_rd_lp_mon__DOT__power_consumption;
    vlSelf->dvfs_error = vlSelf->axi4_master_rd_lp_mon__DOT__dvfs_error;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_rd_data 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__rd_data;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_wr_almost_full 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__wr_almost_full;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_rd_almost_empty 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__rd_almost_empty;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 0xffffffffU;
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [0U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 0U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [1U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [1U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 1U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [2U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [2U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 2U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [3U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [3U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 3U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [4U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [4U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 4U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [5U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [5U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 5U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [6U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [6U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 6U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [7U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [7U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 7U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [8U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [8U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 8U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [9U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [9U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 9U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xaU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xaU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 0xaU;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xbU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xbU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 0xbU;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xcU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xcU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 0xcU;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xdU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xdU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 0xdU;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xeU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xeU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 0xeU;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xfU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xfU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_rid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_data_trans_idx = 0xfU;
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_cg_enable 
        = vlSelf->cfg_cg_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_cg_force_on 
        = vlSelf->cfg_cg_force_on;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_freq_sel 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_freq_sel;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_addr_cnt 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_addr_cnt;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_data_cnt 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_data_cnt;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_resp_cnt 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_resp_cnt;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_debug_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_debug_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_active_trans_threshold 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_active_trans_threshold;
    vlSelf->wake_up_pending = (4U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_skid_rready 
        = vlSelf->fub_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_skid_arready 
        = vlSelf->m_axi_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__block_ready 
        = (0xeU <= (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_active_count));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__rd_data[0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__rd_data[1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__rd_data[2U] 
        = (0x3fU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[2U]);
    vlSelf->current_vf_level = vlSelf->cfg_vf_level;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__state_change 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_state_change;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__timeout_detected 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__r_timeout_detected;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__event_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__perf_completed_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_completed_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__perf_error_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_error_count;
    vlSelf->power_management_error = ((6U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state)) 
                                      | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__power_budget_exceeded));
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_timeout_cycles 
        = vlSelf->cfg_timeout_cycles;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__r_data_count;
    vlSelf->error_count = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__error_count;
    vlSelf->transaction_count = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__transaction_count;
    vlSelf->cg_cycles_saved = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__gated_cycles;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timestamp 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__r_timestamp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__resp_valid 
        = ((IData)(vlSelf->m_axi_rlast) & (IData)(vlSelf->m_axi_rvalid));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT____Vcellinp__r_channel__wr_data 
        = (((QData)((IData)(vlSelf->m_axi_rid)) << 0x24U) 
           | (((QData)((IData)(vlSelf->m_axi_rdata)) 
               << 4U) | (QData)((IData)((((IData)(vlSelf->m_axi_rresp) 
                                          << 2U) | 
                                         (((IData)(vlSelf->m_axi_rlast) 
                                           << 1U) | (IData)(vlSelf->m_axi_ruser)))))));
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arid 
        = vlSelf->fub_axi_arid;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_araddr 
        = vlSelf->fub_axi_araddr;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arlen 
        = vlSelf->fub_axi_arlen;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arsize 
        = vlSelf->fub_axi_arsize;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arburst 
        = vlSelf->fub_axi_arburst;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arlock 
        = vlSelf->fub_axi_arlock;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arcache 
        = vlSelf->fub_axi_arcache;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arprot 
        = vlSelf->fub_axi_arprot;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arqos 
        = vlSelf->fub_axi_arqos;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arregion 
        = vlSelf->fub_axi_arregion;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_aruser 
        = vlSelf->fub_axi_aruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_rready 
        = vlSelf->fub_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rdata 
        = vlSelf->m_axi_rdata;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_ruser 
        = vlSelf->m_axi_ruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_err_select 
        = vlSelf->cfg_axi_err_select;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_error_mask 
        = vlSelf->cfg_axi_error_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_timeout_mask 
        = vlSelf->cfg_axi_timeout_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_compl_mask 
        = vlSelf->cfg_axi_compl_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_thresh_mask 
        = vlSelf->cfg_axi_thresh_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_perf_mask 
        = vlSelf->cfg_axi_perf_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_addr_mask 
        = vlSelf->cfg_axi_addr_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_debug_mask 
        = vlSelf->cfg_axi_debug_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__monbus_ready 
        = vlSelf->monbus_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_tick 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__tick;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__done 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__count) 
           == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__r_match_val));
    vlSelf->fub_axi_arready = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__wr_ready;
    vlSelf->fub_axi_rid = (0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__r_data[1U] 
                                    >> 4U));
    vlSelf->fub_axi_rdata = ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__r_data[1U] 
                              << 0x1cU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__r_data[0U] 
                                           >> 4U));
    vlSelf->fub_axi_rresp = (3U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__r_data[0U] 
                                   >> 2U));
    vlSelf->fub_axi_rlast = (1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__r_data[0U] 
                                   >> 1U));
    vlSelf->fub_axi_ruser = (1U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__r_data[0U]);
    vlSelf->m_axi_arlock = (1U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U] 
                                  >> 0x10U));
    vlSelf->m_axi_arcache = (0xfU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U] 
                                     >> 0xcU));
    vlSelf->m_axi_arprot = (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U] 
                                  >> 9U));
    vlSelf->m_axi_arqos = (0xfU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U] 
                                   >> 5U));
    vlSelf->m_axi_arregion = (0xfU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U] 
                                      >> 1U));
    vlSelf->m_axi_aruser = (1U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U]);
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT____Vcellinp__ar_channel__wr_data[0U] 
        = (IData)((((QData)((IData)(vlSelf->fub_axi_araddr)) 
                    << 0x1eU) | (QData)((IData)((((IData)(vlSelf->fub_axi_arlen) 
                                                  << 0x16U) 
                                                 | (((IData)(vlSelf->fub_axi_arsize) 
                                                     << 0x13U) 
                                                    | (((IData)(vlSelf->fub_axi_arburst) 
                                                        << 0x11U) 
                                                       | (((IData)(vlSelf->fub_axi_arlock) 
                                                           << 0x10U) 
                                                          | (((IData)(vlSelf->fub_axi_arcache) 
                                                              << 0xcU) 
                                                             | (((IData)(vlSelf->fub_axi_arprot) 
                                                                 << 9U) 
                                                                | (((IData)(vlSelf->fub_axi_arqos) 
                                                                    << 5U) 
                                                                   | (((IData)(vlSelf->fub_axi_arregion) 
                                                                       << 1U) 
                                                                      | (IData)(vlSelf->fub_axi_aruser)))))))))))));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT____Vcellinp__ar_channel__wr_data[1U] 
        = (((IData)(vlSelf->fub_axi_arid) << 0x1eU) 
           | (IData)(((((QData)((IData)(vlSelf->fub_axi_araddr)) 
                        << 0x1eU) | (QData)((IData)(
                                                    (((IData)(vlSelf->fub_axi_arlen) 
                                                      << 0x16U) 
                                                     | (((IData)(vlSelf->fub_axi_arsize) 
                                                         << 0x13U) 
                                                        | (((IData)(vlSelf->fub_axi_arburst) 
                                                            << 0x11U) 
                                                           | (((IData)(vlSelf->fub_axi_arlock) 
                                                               << 0x10U) 
                                                              | (((IData)(vlSelf->fub_axi_arcache) 
                                                                  << 0xcU) 
                                                                 | (((IData)(vlSelf->fub_axi_arprot) 
                                                                     << 9U) 
                                                                    | (((IData)(vlSelf->fub_axi_arqos) 
                                                                        << 5U) 
                                                                       | (((IData)(vlSelf->fub_axi_arregion) 
                                                                           << 1U) 
                                                                          | (IData)(vlSelf->fub_axi_aruser)))))))))))) 
                      >> 0x20U)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT____Vcellinp__ar_channel__wr_data[2U] 
        = ((IData)(vlSelf->fub_axi_arid) >> 2U);
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_monitor_enable 
        = vlSelf->cfg_monitor_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_error_enable 
        = vlSelf->cfg_error_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_latency_threshold 
        = vlSelf->cfg_latency_threshold;
    vlSelf->fub_axi_rvalid = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__rd_valid;
    axi4_master_rd_lp_mon__DOT____VdfgTmp_hf422e32c__0 
        = VL_DIV_III(32, ((IData)(0x64U) * vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__gated_cycles), 
                     (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__transaction_count 
                      + vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__gated_cycles));
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arready 
        = vlSelf->m_axi_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rlast 
        = vlSelf->m_axi_rlast;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_timeout_enable 
        = vlSelf->cfg_timeout_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__timer_activity 
        = ((IData)(vlSelf->cfg_perf_enable) | (IData)(vlSelf->cfg_timeout_enable));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency = 0U;
    if (vlSelf->cfg_perf_enable) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 1U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 2U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 3U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 4U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 5U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 6U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 7U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 8U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 9U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 0xaU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 0xbU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 0xcU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 0xdU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 0xeU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 0xfU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk9__DOT__idx = 0x10U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 1U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 2U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 3U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 4U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 5U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 6U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 7U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 8U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 9U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 0xaU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 0xbU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 0xcU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 0xdU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 0xeU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 0xfU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__unnamedblk10__DOT__idx = 0x10U;
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [0U][8U] >> 0x18U) & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                 [0U][8U] 
                                                 >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0U][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [0U][1U] 
                                          >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [0U][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0U][2U] 
                                            >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (1U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [1U][8U] >> 0x18U) & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                 [1U][8U] 
                                                 >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [1U][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [1U][1U] 
                                          >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [1U][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [1U][2U] 
                                            >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (2U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [2U][8U] >> 0x18U) & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                 [2U][8U] 
                                                 >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [2U][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [2U][1U] 
                                          >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [2U][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [2U][2U] 
                                            >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (4U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [3U][8U] >> 0x18U) & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                 [3U][8U] 
                                                 >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [3U][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [3U][1U] 
                                          >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [3U][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [3U][2U] 
                                            >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (8U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [4U][8U] >> 0x18U) & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                 [4U][8U] 
                                                 >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [4U][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [4U][1U] 
                                          >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [4U][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [4U][2U] 
                                            >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x10U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [5U][8U] >> 0x18U) & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                 [5U][8U] 
                                                 >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [5U][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [5U][1U] 
                                          >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [5U][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [5U][2U] 
                                            >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x20U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [6U][8U] >> 0x18U) & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                 [6U][8U] 
                                                 >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [6U][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [6U][1U] 
                                          >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [6U][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [6U][2U] 
                                            >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x40U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [7U][8U] >> 0x18U) & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                 [7U][8U] 
                                                 >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [7U][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [7U][1U] 
                                          >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [7U][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [7U][2U] 
                                            >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x80U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [8U][8U] >> 0x18U) & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                 [8U][8U] 
                                                 >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [8U][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [8U][1U] 
                                          >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [8U][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [8U][2U] 
                                            >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x100U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [9U][8U] >> 0x18U) & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                 [9U][8U] 
                                                 >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [9U][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [9U][1U] 
                                          >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [9U][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [9U][2U] 
                                            >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x200U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [0xaU][8U] >> 0x18U) & (3U == (7U & (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                   [0xaU][8U] 
                                                   >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xaU][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xaU][1U] 
                                            >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [0xaU][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [0xaU][2U] 
                                              >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x400U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [0xbU][8U] >> 0x18U) & (3U == (7U & (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                   [0xbU][8U] 
                                                   >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xbU][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xbU][1U] 
                                            >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [0xbU][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [0xbU][2U] 
                                              >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x800U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [0xcU][8U] >> 0x18U) & (3U == (7U & (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                   [0xcU][8U] 
                                                   >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xcU][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xcU][1U] 
                                            >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [0xcU][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [0xcU][2U] 
                                              >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x1000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [0xdU][8U] >> 0x18U) & (3U == (7U & (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                   [0xdU][8U] 
                                                   >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xdU][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xdU][1U] 
                                            >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [0xdU][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [0xdU][2U] 
                                              >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x2000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [0xeU][8U] >> 0x18U) & (3U == (7U & (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                   [0xeU][8U] 
                                                   >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xeU][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xeU][1U] 
                                            >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [0xeU][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [0xeU][2U] 
                                              >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x4000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
              [0xfU][8U] >> 0x18U) & (3U == (7U & (
                                                   vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                   [0xfU][8U] 
                                                   >> 0xfU))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xfU][2U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xfU][1U] 
                                            >> 0x14U)) 
                   - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                       [0xfU][3U] << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [0xfU][2U] 
                                              >> 0x14U)));
            if (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_total_latency 
                  > vlSelf->cfg_latency_threshold) 
                 & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_latency_threshold_crossed)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events 
                    = (0x8000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events));
            }
        }
        if ((1U & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                   & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 0U;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 1U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 1U;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 2U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 2U;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 3U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 3U;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 4U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 4U;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 5U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 5U;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 6U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 6U;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 7U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 7U;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 8U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 8U;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 9U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 9U;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 0xaU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 0xaU;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 0xbU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 0xbU;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 0xcU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 0xcU;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 0xdU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 0xdU;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                    >> 0xeU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 0xeU;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
        if ((IData)((((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_latency_threshold_events) 
                      >> 0xfU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx = 0xfU;
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event = 1U;
        }
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rvalid 
        = vlSelf->m_axi_rvalid;
    vlSelf->m_axi_araddr = ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[1U] 
                             << 2U) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U] 
                                       >> 0x1eU));
    vlSelf->m_axi_arlen = (0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U] 
                                    >> 0x16U));
    vlSelf->m_axi_arsize = (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U] 
                                  >> 0x13U));
    vlSelf->m_axi_arburst = (3U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[0U] 
                                   >> 0x11U));
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_perf_enable 
        = vlSelf->cfg_perf_enable;
    vlSelf->m_axi_arvalid = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__rd_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__busy 
        = (0U < (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_active_count));
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rid = vlSelf->m_axi_rid;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rresp 
        = vlSelf->m_axi_rresp;
    vlSelf->m_axi_arid = (0xffU & ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[2U] 
                                    << 2U) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data[1U] 
                                              >> 0x1eU)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__w_rd_xfer 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__rd_valid) 
           & (IData)(vlSelf->m_axi_arready));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__w_wr_xfer 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__wr_ready) 
           & (IData)(vlSelf->m_axi_rvalid));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__w_rd_xfer 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__rd_valid) 
           & (IData)(vlSelf->fub_axi_rready));
    vlSelf->m_axi_rready = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__wr_ready;
    vlSelf->active_transactions = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_active_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__aclk_lp = vlSelf->aclk_lp;
    vlSelf->axi4_master_rd_lp_mon__DOT__aresetn_lp 
        = vlSelf->aresetn_lp;
    vlSelf->axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__cfg_cg_idle_threshold 
        = ((IData)(vlSelf->cfg_cg_ultra_aggressive)
            ? 2U : (IData)(vlSelf->cfg_cg_idle_threshold));
    vlSelf->sleep_mode_active = ((3U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state)) 
                                 | (2U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_wr_addr 
        = (7U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_rd_addr 
        = (7U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 0U;
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0U][8U] >> 0x18U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0U][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_timeout_enable)) 
         & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0U][0U])) | (1U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                          [0U][0U]))) 
            | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                      [0U][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (1U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [1U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 1U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [1U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_timeout_enable)) & 
         (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                   [1U][0U])) | (1U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                        [1U][0U]))) 
          | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                    [1U][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (2U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [2U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 2U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [2U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_timeout_enable)) & 
         (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                   [2U][0U])) | (1U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                        [2U][0U]))) 
          | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                    [2U][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (4U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [3U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 3U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [3U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_timeout_enable)) & 
         (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                   [3U][0U])) | (1U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                        [3U][0U]))) 
          | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                    [3U][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (8U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [4U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 4U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [4U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_timeout_enable)) & 
         (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                   [4U][0U])) | (1U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                        [4U][0U]))) 
          | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                    [4U][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x10U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [5U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 5U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [5U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_timeout_enable)) & 
         (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                   [5U][0U])) | (1U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                        [5U][0U]))) 
          | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                    [5U][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x20U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [6U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 6U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [6U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_timeout_enable)) & 
         (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                   [6U][0U])) | (1U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                        [6U][0U]))) 
          | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                    [6U][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x40U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [7U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 7U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [7U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_timeout_enable)) & 
         (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                   [7U][0U])) | (1U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                        [7U][0U]))) 
          | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                    [7U][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x80U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [8U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 8U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [8U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_timeout_enable)) & 
         (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                   [8U][0U])) | (1U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                        [8U][0U]))) 
          | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                    [8U][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x100U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [9U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 9U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [9U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_timeout_enable)) & 
         (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                   [9U][0U])) | (1U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                        [9U][0U]))) 
          | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                    [9U][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x200U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xaU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xaU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xaU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_timeout_enable)) 
         & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xaU][0U])) | (1U == (0xfU & 
                                            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xaU][0U]))) 
            | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                      [0xaU][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x400U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xbU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xbU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xbU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_timeout_enable)) 
         & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xbU][0U])) | (1U == (0xfU & 
                                            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xbU][0U]))) 
            | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                      [0xbU][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x800U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xcU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xcU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xcU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_timeout_enable)) 
         & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xcU][0U])) | (1U == (0xfU & 
                                            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xcU][0U]))) 
            | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                      [0xcU][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x1000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xdU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xdU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xdU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_timeout_enable)) 
         & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xdU][0U])) | (1U == (0xfU & 
                                            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xdU][0U]))) 
            | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                      [0xdU][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x2000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xeU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xeU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xeU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_timeout_enable)) 
         & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xeU][0U])) | (1U == (0xfU & 
                                            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xeU][0U]))) 
            | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                      [0xeU][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x4000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xfU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xfU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xfU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_timeout_enable)) 
         & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                     [0xfU][0U])) | (1U == (0xfU & 
                                            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [0xfU][0U]))) 
            | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                      [0xfU][0U]))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected 
            = (0x8000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected));
    }
    if ((1U & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
               & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 0U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 1U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 1U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 2U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 2U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 3U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 3U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 4U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 4U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 5U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 5U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 6U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 6U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 7U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 7U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 8U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 8U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 9U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 9U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 0xaU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 0xaU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 0xbU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 0xbU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 0xcU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 0xcU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 0xdU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 0xdU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                >> 0xeU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 0xeU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    if ((IData)((((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_timeout_events_detected) 
                  >> 0xfU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx = 0xfU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event = 1U;
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 0U;
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [0U][8U] >> 0x18U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported))) 
          & (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                          [0U][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (1U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [1U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                     >> 1U))) & (3U 
                                                 == 
                                                 (7U 
                                                  & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                     [1U][8U] 
                                                     >> 0xfU)))) 
         & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (2U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [2U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                     >> 2U))) & (3U 
                                                 == 
                                                 (7U 
                                                  & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                     [2U][8U] 
                                                     >> 0xfU)))) 
         & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (4U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [3U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                     >> 3U))) & (3U 
                                                 == 
                                                 (7U 
                                                  & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                     [3U][8U] 
                                                     >> 0xfU)))) 
         & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (8U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [4U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                     >> 4U))) & (3U 
                                                 == 
                                                 (7U 
                                                  & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                     [4U][8U] 
                                                     >> 0xfU)))) 
         & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x10U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [5U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                     >> 5U))) & (3U 
                                                 == 
                                                 (7U 
                                                  & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                     [5U][8U] 
                                                     >> 0xfU)))) 
         & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x20U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [6U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                     >> 6U))) & (3U 
                                                 == 
                                                 (7U 
                                                  & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                     [6U][8U] 
                                                     >> 0xfU)))) 
         & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x40U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [7U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                     >> 7U))) & (3U 
                                                 == 
                                                 (7U 
                                                  & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                     [7U][8U] 
                                                     >> 0xfU)))) 
         & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x80U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [8U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                     >> 8U))) & (3U 
                                                 == 
                                                 (7U 
                                                  & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                     [8U][8U] 
                                                     >> 0xfU)))) 
         & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x100U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [9U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                     >> 9U))) & (3U 
                                                 == 
                                                 (7U 
                                                  & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                     [9U][8U] 
                                                     >> 0xfU)))) 
         & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x200U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [0xaU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                       >> 0xaU))) & 
          (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                        [0xaU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x400U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [0xbU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                       >> 0xbU))) & 
          (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                        [0xbU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x800U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [0xcU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                       >> 0xcU))) & 
          (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                        [0xcU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x1000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [0xdU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                       >> 0xdU))) & 
          (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                        [0xdU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x2000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [0xeU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                       >> 0xeU))) & 
          (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                        [0xeU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x4000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if (((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
            [0xfU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                       >> 0xfU))) & 
          (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                        [0xfU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_monitor_enable))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected 
            = (0x8000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected));
    }
    if ((1U & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
               & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 0U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 1U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 1U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 2U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 2U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 3U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 3U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 4U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 4U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 5U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 5U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 6U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 6U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 7U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 7U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 8U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 8U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 9U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 9U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 0xaU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 0xaU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 0xbU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 0xbU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 0xcU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 0xcU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 0xdU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 0xdU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                >> 0xeU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 0xeU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    if ((IData)((((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events_detected) 
                  >> 0xfU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx = 0xfU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event = 1U;
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 0U;
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0U][8U] >> 0x18U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0U][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_error_enable)) 
         & (~ ((IData)(vlSelf->cfg_timeout_enable) 
               & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0U][0U])) | (1U == (0xfU 
                                                & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [0U][0U]))) 
                  | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                            [0U][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (1U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [1U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 1U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [1U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_error_enable)) & (~ 
                                                  ((IData)(vlSelf->cfg_timeout_enable) 
                                                   & (((0U 
                                                        == 
                                                        (0xfU 
                                                         & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                         [1U][0U])) 
                                                       | (1U 
                                                          == 
                                                          (0xfU 
                                                           & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                           [1U][0U]))) 
                                                      | (2U 
                                                         == 
                                                         (0xfU 
                                                          & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                          [1U][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (2U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [2U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 2U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [2U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_error_enable)) & (~ 
                                                  ((IData)(vlSelf->cfg_timeout_enable) 
                                                   & (((0U 
                                                        == 
                                                        (0xfU 
                                                         & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                         [2U][0U])) 
                                                       | (1U 
                                                          == 
                                                          (0xfU 
                                                           & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                           [2U][0U]))) 
                                                      | (2U 
                                                         == 
                                                         (0xfU 
                                                          & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                          [2U][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (4U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [3U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 3U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [3U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_error_enable)) & (~ 
                                                  ((IData)(vlSelf->cfg_timeout_enable) 
                                                   & (((0U 
                                                        == 
                                                        (0xfU 
                                                         & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                         [3U][0U])) 
                                                       | (1U 
                                                          == 
                                                          (0xfU 
                                                           & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                           [3U][0U]))) 
                                                      | (2U 
                                                         == 
                                                         (0xfU 
                                                          & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                          [3U][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (8U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [4U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 4U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [4U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_error_enable)) & (~ 
                                                  ((IData)(vlSelf->cfg_timeout_enable) 
                                                   & (((0U 
                                                        == 
                                                        (0xfU 
                                                         & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                         [4U][0U])) 
                                                       | (1U 
                                                          == 
                                                          (0xfU 
                                                           & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                           [4U][0U]))) 
                                                      | (2U 
                                                         == 
                                                         (0xfU 
                                                          & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                          [4U][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x10U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [5U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 5U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [5U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_error_enable)) & (~ 
                                                  ((IData)(vlSelf->cfg_timeout_enable) 
                                                   & (((0U 
                                                        == 
                                                        (0xfU 
                                                         & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                         [5U][0U])) 
                                                       | (1U 
                                                          == 
                                                          (0xfU 
                                                           & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                           [5U][0U]))) 
                                                      | (2U 
                                                         == 
                                                         (0xfU 
                                                          & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                          [5U][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x20U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [6U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 6U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [6U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_error_enable)) & (~ 
                                                  ((IData)(vlSelf->cfg_timeout_enable) 
                                                   & (((0U 
                                                        == 
                                                        (0xfU 
                                                         & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                         [6U][0U])) 
                                                       | (1U 
                                                          == 
                                                          (0xfU 
                                                           & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                           [6U][0U]))) 
                                                      | (2U 
                                                         == 
                                                         (0xfU 
                                                          & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                          [6U][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x40U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [7U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 7U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [7U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_error_enable)) & (~ 
                                                  ((IData)(vlSelf->cfg_timeout_enable) 
                                                   & (((0U 
                                                        == 
                                                        (0xfU 
                                                         & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                         [7U][0U])) 
                                                       | (1U 
                                                          == 
                                                          (0xfU 
                                                           & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                           [7U][0U]))) 
                                                      | (2U 
                                                         == 
                                                         (0xfU 
                                                          & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                          [7U][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x80U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [8U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 8U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [8U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_error_enable)) & (~ 
                                                  ((IData)(vlSelf->cfg_timeout_enable) 
                                                   & (((0U 
                                                        == 
                                                        (0xfU 
                                                         & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                         [8U][0U])) 
                                                       | (1U 
                                                          == 
                                                          (0xfU 
                                                           & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                           [8U][0U]))) 
                                                      | (2U 
                                                         == 
                                                         (0xfU 
                                                          & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                          [8U][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x100U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [9U][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                      >> 9U))) & (4U 
                                                  == 
                                                  (7U 
                                                   & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                      [9U][8U] 
                                                      >> 0xfU)))) 
          & (IData)(vlSelf->cfg_error_enable)) & (~ 
                                                  ((IData)(vlSelf->cfg_timeout_enable) 
                                                   & (((0U 
                                                        == 
                                                        (0xfU 
                                                         & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                         [9U][0U])) 
                                                       | (1U 
                                                          == 
                                                          (0xfU 
                                                           & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                           [9U][0U]))) 
                                                      | (2U 
                                                         == 
                                                         (0xfU 
                                                          & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                          [9U][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x200U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xaU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xaU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xaU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_error_enable)) 
         & (~ ((IData)(vlSelf->cfg_timeout_enable) 
               & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xaU][0U])) | (1U == (0xfU 
                                                  & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                  [0xaU][0U]))) 
                  | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                            [0xaU][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x400U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xbU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xbU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xbU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_error_enable)) 
         & (~ ((IData)(vlSelf->cfg_timeout_enable) 
               & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xbU][0U])) | (1U == (0xfU 
                                                  & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                  [0xbU][0U]))) 
                  | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                            [0xbU][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x800U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xcU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xcU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xcU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_error_enable)) 
         & (~ ((IData)(vlSelf->cfg_timeout_enable) 
               & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xcU][0U])) | (1U == (0xfU 
                                                  & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                  [0xcU][0U]))) 
                  | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                            [0xcU][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x1000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xdU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xdU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xdU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_error_enable)) 
         & (~ ((IData)(vlSelf->cfg_timeout_enable) 
               & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xdU][0U])) | (1U == (0xfU 
                                                  & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                  [0xdU][0U]))) 
                  | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                            [0xdU][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x2000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xeU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xeU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xeU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_error_enable)) 
         & (~ ((IData)(vlSelf->cfg_timeout_enable) 
               & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xeU][0U])) | (1U == (0xfU 
                                                  & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                  [0xeU][0U]))) 
                  | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                            [0xeU][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x4000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
             [0xfU][8U] >> 0x18U) & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                                        >> 0xfU))) 
           & (4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xfU][8U] >> 0xfU)))) & (IData)(vlSelf->cfg_error_enable)) 
         & (~ ((IData)(vlSelf->cfg_timeout_enable) 
               & (((0U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                           [0xfU][0U])) | (1U == (0xfU 
                                                  & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                  [0xfU][0U]))) 
                  | (2U == (0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                            [0xfU][0U]))))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected 
            = (0x8000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected));
    }
    if ((1U & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
               & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 0U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 1U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 1U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 2U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 2U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 3U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 3U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 4U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 4U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 5U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 5U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 6U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 6U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 7U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 7U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 8U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 8U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 9U) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 9U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 0xaU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 0xaU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 0xbU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 0xbU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 0xcU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 0xcU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 0xdU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 0xdU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                >> 0xeU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 0xeU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    if ((IData)((((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events_detected) 
                  >> 0xfU) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx = 0xfU;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event = 1U;
    }
    vlSelf->axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__cfg_axi_pkt_mask 
        = ((IData)(vlSelf->cfg_axi_pkt_mask) | (IData)(vlSelf->cfg_power_event_mask));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready 
        = (1U & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__wr_full)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__rd_valid 
        = (1U & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__rd_empty)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__monbus_packet 
        = ((0x7fffffffffffULL & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__monbus_packet) 
           | ((QData)((IData)((((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_packet_type) 
                                << 0xdU) | (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_code) 
                                             << 6U) 
                                            | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_channel))))) 
              << 0x2fU));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__monbus_packet 
        = (0x88000000000ULL | ((0xffff800000000000ULL 
                                & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__monbus_packet) 
                               | (0x7ffffffffULL & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_data)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_reporter_monbus_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__monbus_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[1U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [1U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[1U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [1U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[1U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [1U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[1U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [1U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[1U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [1U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[1U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [1U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[1U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [1U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[1U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [1U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[1U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [1U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[2U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [2U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[2U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [2U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[2U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [2U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[2U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [2U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[2U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [2U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[2U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [2U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[2U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [2U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[2U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [2U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[2U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [2U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[3U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [3U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[3U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [3U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[3U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [3U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[3U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [3U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[3U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [3U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[3U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [3U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[3U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [3U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[3U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [3U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[3U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [3U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[4U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [4U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[4U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [4U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[4U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [4U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[4U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [4U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[4U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [4U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[4U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [4U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[4U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [4U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[4U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [4U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[4U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [4U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[5U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [5U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[5U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [5U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[5U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [5U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[5U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [5U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[5U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [5U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[5U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [5U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[5U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [5U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[5U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [5U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[5U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [5U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[6U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [6U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[6U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [6U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[6U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [6U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[6U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [6U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[6U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [6U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[6U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [6U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[6U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [6U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[6U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [6U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[6U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [6U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[7U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [7U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[7U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [7U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[7U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [7U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[7U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [7U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[7U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [7U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[7U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [7U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[7U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [7U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[7U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [7U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[7U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [7U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[8U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [8U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[8U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [8U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[8U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [8U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[8U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [8U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[8U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [8U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[8U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [8U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[8U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [8U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[8U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [8U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[8U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [8U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[9U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [9U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[9U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [9U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[9U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [9U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[9U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [9U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[9U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [9U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[9U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [9U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[9U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [9U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[9U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [9U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[9U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [9U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xaU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xaU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xaU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xaU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xaU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xaU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xaU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xaU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xaU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xaU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xaU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xaU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xaU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xaU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xaU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xaU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xaU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xaU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xbU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xbU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xbU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xbU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xbU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xbU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xbU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xbU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xbU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xbU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xbU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xbU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xbU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xbU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xbU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xbU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xbU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xbU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xcU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xcU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xcU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xcU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xcU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xcU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xcU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xcU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xcU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xcU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xcU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xcU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xcU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xcU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xcU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xcU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xcU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xcU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xdU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xdU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xdU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xdU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xdU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xdU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xdU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xdU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xdU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xdU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xdU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xdU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xdU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xdU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xdU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xdU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xdU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xdU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xeU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xeU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xeU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xeU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xeU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xeU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xeU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xeU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xeU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xeU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xeU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xeU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xeU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xeU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xeU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xeU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xeU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xeU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xfU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xfU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xfU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xfU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xfU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xfU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xfU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xfU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xfU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xfU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xfU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xfU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xfU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xfU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xfU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xfU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table[0xfU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
        [0xfU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_cg_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_cg_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_cg_force_on 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_cg_force_on;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__cfg_freq_sel 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_freq_sel;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__cfg_addr_cnt 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_addr_cnt;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__cfg_data_cnt 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_data_cnt;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__cfg_resp_cnt 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_resp_cnt;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__cfg_debug_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_debug_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__active_trans_threshold 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_active_trans_threshold;
    vlSelf->axi4_master_rd_lp_mon__DOT__wake_up_pending 
        = vlSelf->wake_up_pending;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__rd_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_skid_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__rd_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_skid_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__block_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__block_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_ar_pkt[0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__rd_data[0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_ar_pkt[1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__rd_data[1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_ar_pkt[2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__rd_data[2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__current_vf_level 
        = vlSelf->current_vf_level;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_state_change_detected 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__state_change;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_timeout_detected 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__timeout_detected;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_event_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__event_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__r_perf_completed_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__perf_completed_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__r_perf_error_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__perf_error_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__power_management_error 
        = vlSelf->power_management_error;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_timeout_cycles 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_timeout_cycles;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_ar_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__rd_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_r_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__rd_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__count;
    vlSelf->axi4_master_rd_lp_mon__DOT__error_count 
        = vlSelf->error_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__error_count 
        = vlSelf->error_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__transaction_count 
        = vlSelf->transaction_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__transaction_count 
        = vlSelf->transaction_count;
    vlSelf->axi4_master_rd_lp_mon__DOT__cg_cycles_saved 
        = vlSelf->cg_cycles_saved;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_cycles_saved 
        = vlSelf->cg_cycles_saved;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__timestamp 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timestamp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__r_timestamp 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timestamp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__resp_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__resp_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__wr_data 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT____Vcellinp__r_channel__wr_data;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_araddr 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_araddr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arlen 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arlen;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arsize 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arsize;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arburst 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arburst;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arlock 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arlock;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arcache 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arcache;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arprot 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arprot;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arqos 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arqos;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arregion 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arregion;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_aruser 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_aruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_rready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rdata 
        = vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rdata;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_ruser 
        = vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_ruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_err_select 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_err_select;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_error_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_error_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_timeout_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_timeout_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_compl_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_compl_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_thresh_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_thresh_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_perf_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_perf_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_addr_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_addr_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_debug_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_axi_debug_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__monbus_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__monbus_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__timer_tick 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_tick;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_timer_tick 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_tick;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__w_timer_tick 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_tick;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__w_prescaler_done 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__done;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__w_next_count 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__r_clear_pulse)
            ? 0U : ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__done)
                     ? 0U : (0xffffU & ((IData)(1U) 
                                        + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__count)))));
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_arready 
        = vlSelf->fub_axi_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arready 
        = vlSelf->fub_axi_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arready 
        = vlSelf->fub_axi_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arready 
        = vlSelf->fub_axi_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_rid 
        = vlSelf->fub_axi_rid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_rid 
        = vlSelf->fub_axi_rid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_rid 
        = vlSelf->fub_axi_rid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_rid 
        = vlSelf->fub_axi_rid;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_rdata 
        = vlSelf->fub_axi_rdata;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_rdata 
        = vlSelf->fub_axi_rdata;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_rdata 
        = vlSelf->fub_axi_rdata;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_rdata 
        = vlSelf->fub_axi_rdata;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_rresp 
        = vlSelf->fub_axi_rresp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_rresp 
        = vlSelf->fub_axi_rresp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_rresp 
        = vlSelf->fub_axi_rresp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_rresp 
        = vlSelf->fub_axi_rresp;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_rlast 
        = vlSelf->fub_axi_rlast;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_rlast 
        = vlSelf->fub_axi_rlast;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_rlast 
        = vlSelf->fub_axi_rlast;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_rlast 
        = vlSelf->fub_axi_rlast;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_ruser 
        = vlSelf->fub_axi_ruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_ruser 
        = vlSelf->fub_axi_ruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_ruser 
        = vlSelf->fub_axi_ruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_ruser 
        = vlSelf->fub_axi_ruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arlock 
        = vlSelf->m_axi_arlock;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arlock 
        = vlSelf->m_axi_arlock;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arlock 
        = vlSelf->m_axi_arlock;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arlock 
        = vlSelf->m_axi_arlock;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arcache 
        = vlSelf->m_axi_arcache;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arcache 
        = vlSelf->m_axi_arcache;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arcache 
        = vlSelf->m_axi_arcache;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arcache 
        = vlSelf->m_axi_arcache;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arprot 
        = vlSelf->m_axi_arprot;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arprot 
        = vlSelf->m_axi_arprot;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arprot 
        = vlSelf->m_axi_arprot;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arprot 
        = vlSelf->m_axi_arprot;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arqos 
        = vlSelf->m_axi_arqos;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arqos 
        = vlSelf->m_axi_arqos;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arqos 
        = vlSelf->m_axi_arqos;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arqos 
        = vlSelf->m_axi_arqos;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arregion 
        = vlSelf->m_axi_arregion;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arregion 
        = vlSelf->m_axi_arregion;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arregion 
        = vlSelf->m_axi_arregion;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arregion 
        = vlSelf->m_axi_arregion;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_aruser 
        = vlSelf->m_axi_aruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_aruser 
        = vlSelf->m_axi_aruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_aruser 
        = vlSelf->m_axi_aruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_aruser 
        = vlSelf->m_axi_aruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__wr_data[0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT____Vcellinp__ar_channel__wr_data[0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__wr_data[1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT____Vcellinp__ar_channel__wr_data[1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__wr_data[2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT____Vcellinp__ar_channel__wr_data[2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_monitor_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_monitor_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_error_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_error_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_latency_threshold 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_latency_threshold;
    vlSelf->axi4_master_rd_lp_mon__DOT__fub_axi_rvalid 
        = vlSelf->fub_axi_rvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_rvalid 
        = vlSelf->fub_axi_rvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_rvalid 
        = vlSelf->fub_axi_rvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_rvalid 
        = vlSelf->fub_axi_rvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_skid_rvalid 
        = vlSelf->fub_axi_rvalid;
    vlSelf->power_efficiency = ((0U < vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__transaction_count)
                                 ? (0xffU & axi4_master_rd_lp_mon__DOT____VdfgTmp_hf422e32c__0)
                                 : 0U);
    vlSelf->cg_power_saved_percent = ((0U < vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__gated_cycles)
                                       ? (0xffffU & axi4_master_rd_lp_mon__DOT____VdfgTmp_hf422e32c__0)
                                       : 0U);
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rlast 
        = vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rlast;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_timeout_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_timeout_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_value = 0U;
    if (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_latency_event) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_value 
            = (((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                 [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx][2U] 
                 << 0xcU) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                             [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx][1U] 
                             >> 0x14U)) - ((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx][3U] 
                                            << 0xcU) 
                                           | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_latency_idx][2U] 
                                              >> 0x14U)));
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rvalid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_araddr 
        = vlSelf->m_axi_araddr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_araddr 
        = vlSelf->m_axi_araddr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_araddr 
        = vlSelf->m_axi_araddr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_araddr 
        = vlSelf->m_axi_araddr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_addr 
        = vlSelf->m_axi_araddr;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arlen 
        = vlSelf->m_axi_arlen;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arlen 
        = vlSelf->m_axi_arlen;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arlen 
        = vlSelf->m_axi_arlen;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arlen 
        = vlSelf->m_axi_arlen;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_len 
        = vlSelf->m_axi_arlen;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arsize 
        = vlSelf->m_axi_arsize;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arsize 
        = vlSelf->m_axi_arsize;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arsize 
        = vlSelf->m_axi_arsize;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arsize 
        = vlSelf->m_axi_arsize;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_size 
        = vlSelf->m_axi_arsize;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arburst 
        = vlSelf->m_axi_arburst;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arburst 
        = vlSelf->m_axi_arburst;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arburst 
        = vlSelf->m_axi_arburst;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arburst 
        = vlSelf->m_axi_arburst;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_burst 
        = vlSelf->m_axi_arburst;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_perf_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__cfg_perf_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arvalid 
        = vlSelf->m_axi_arvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arvalid 
        = vlSelf->m_axi_arvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arvalid 
        = vlSelf->m_axi_arvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arvalid 
        = vlSelf->m_axi_arvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__int_skid_arvalid 
        = vlSelf->m_axi_arvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_valid 
        = vlSelf->m_axi_arvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__busy 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__busy;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rresp 
        = vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rresp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_chan_idx 
        = (0x3fU & (IData)(vlSelf->m_axi_arid));
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_arid 
        = vlSelf->m_axi_arid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arid 
        = vlSelf->m_axi_arid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arid 
        = vlSelf->m_axi_arid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arid 
        = vlSelf->m_axi_arid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 0xffffffffU;
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [0U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 0U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [1U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [1U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 1U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [2U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [2U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 2U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [3U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [3U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 3U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [4U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [4U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 4U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [5U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [5U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 5U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [6U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [6U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 6U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [7U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [7U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 7U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [8U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [8U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 8U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [9U][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                              [9U][7U] 
                                              >> 7U)) 
                                    == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 9U;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xaU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xaU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 0xaU;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xbU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xbU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 0xbU;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xcU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xcU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 0xcU;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xdU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xdU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 0xdU;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xeU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xeU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 0xeU;
    }
    if ((((0xffffffffU == vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx) 
          & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
             [0xfU][8U] >> 0x18U)) & ((0xffU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__r_trans_table
                                                [0xfU][7U] 
                                                >> 7U)) 
                                      == (IData)(vlSelf->m_axi_arid)))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__w_addr_trans_idx = 0xfU;
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_id 
        = vlSelf->m_axi_arid;
    vlSelf->axi4_master_rd_lp_mon__DOT__m_axi_rready 
        = vlSelf->m_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rready 
        = vlSelf->m_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rready 
        = vlSelf->m_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_rready 
        = vlSelf->m_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__data_ready 
        = vlSelf->m_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__resp_ready 
        = vlSelf->m_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__active_transactions 
        = vlSelf->active_transactions;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__active_transactions 
        = vlSelf->active_transactions;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__active_transactions 
        = vlSelf->active_transactions;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__active_count 
        = vlSelf->active_transactions;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__active_count 
        = vlSelf->active_transactions;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_active_count 
        = vlSelf->active_transactions;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__active_count 
        = vlSelf->active_transactions;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__aclk_lp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__aresetn_lp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_cg_idle_threshold 
        = vlSelf->axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__cfg_cg_idle_threshold;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_monitor_en 
        = ((IData)(vlSelf->cfg_cg_enable) & ((~ (IData)(vlSelf->cfg_cg_force_on)) 
                                             & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__monitor_idle_count) 
                                                >= (IData)(vlSelf->axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__cfg_cg_idle_threshold))));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_reporter_en 
        = ((IData)(vlSelf->cfg_cg_enable) & ((~ (IData)(vlSelf->cfg_cg_force_on)) 
                                             & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__reporter_idle_count) 
                                                >= (IData)(vlSelf->axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__cfg_cg_idle_threshold))));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_timers_en 
        = ((IData)(vlSelf->cfg_cg_enable) & ((~ (IData)(vlSelf->cfg_cg_force_on)) 
                                             & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__timer_idle_count) 
                                                >= (IData)(vlSelf->axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__cfg_cg_idle_threshold))));
    vlSelf->cg_deep_sleep = vlSelf->sleep_mode_active;
    vlSelf->axi4_master_rd_lp_mon__DOT__sleep_mode_active 
        = vlSelf->sleep_mode_active;
    vlSelf->axi4_master_rd_lp_mon__DOT__cg_deep_sleep 
        = vlSelf->sleep_mode_active;
    axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__fub_axi_arvalid 
        = ((~ (IData)(vlSelf->sleep_mode_active)) & (IData)(vlSelf->fub_axi_arvalid));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_rd_data 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
        [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_rd_addr];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data = 0ULL;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid = 0U;
    if (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_error_event) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data 
            = ((0xfffffffffffULL & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data) 
               | ((QData)((IData)((0xfU & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                   [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx][0U]))) 
                  << 0x2cU));
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data 
            = ((0xff03fffffffffULL & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data) 
               | ((QData)((IData)((0x3fU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx][6U] 
                                            >> 0x14U)))) 
                  << 0x26U));
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data 
            = ((0xfffc000000000ULL & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data) 
               | (QData)((IData)(((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                   [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx][8U] 
                                   << 0x11U) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_error_idx][7U] 
                                                >> 0xfU)))));
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid = 1U;
    } else if (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_timeout_event) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data 
            = ((0xfffffffffffULL & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data) 
               | ((QData)((IData)((0x30U | (0xfU & 
                                            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx][0U])))) 
                  << 0x2cU));
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data 
            = ((0xff03fffffffffULL & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data) 
               | ((QData)((IData)((0x3fU & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                            [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx][6U] 
                                            >> 0x14U)))) 
                  << 0x26U));
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data 
            = ((0xfffc000000000ULL & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data) 
               | (QData)((IData)(((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                   [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx][8U] 
                                   << 0x11U) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_timeout_idx][7U] 
                                                >> 0xfU)))));
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid = 1U;
    } else if (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_has_completion_event) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data 
            = ((0x3fffffffffULL & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data) 
               | ((QData)((IData)((0x400U | (0x3fU 
                                             & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx][6U] 
                                                >> 0x14U))))) 
                  << 0x26U));
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data 
            = ((0xfffc000000000ULL & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data) 
               | (QData)((IData)(((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                   [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx][8U] 
                                   << 0x11U) | (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_selected_completion_idx][7U] 
                                                >> 0xfU)))));
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid = 1U;
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_pkt_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__cfg_axi_pkt_mask;
    vlSelf->cfg_conflict_error = (0U != ((IData)(vlSelf->cfg_axi_err_select) 
                                         & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__cfg_axi_pkt_mask)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_rd_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__rd_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_next_perf_report_state = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_generate_perf_packet_completed = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_generate_perf_packet_errors = 0U;
    if ((((IData)(vlSelf->cfg_perf_enable) & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__monbus_valid))) 
         & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__rd_valid)))) {
        if ((4U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_report_state))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_next_perf_report_state = 0U;
            if ((1U & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_report_state) 
                          >> 1U)))) {
                if ((1U & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_report_state)))) {
                    if ((0U < (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_error_count))) {
                        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_generate_perf_packet_errors = 1U;
                    }
                }
            }
        } else {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_next_perf_report_state 
                = ((2U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_report_state))
                    ? ((1U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_report_state))
                        ? 4U : 3U) : ((1U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_report_state))
                                       ? 2U : 1U));
        }
        if ((1U & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_report_state) 
                      >> 2U)))) {
            if ((2U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_report_state))) {
                if ((1U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_report_state))) {
                    if ((0U < (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_perf_completed_count))) {
                        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_generate_perf_packet_completed = 1U;
                    }
                }
            }
        }
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current = 0U;
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [0U][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [0U][8U] 
                                              >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [0U][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [1U][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [1U][8U] 
                                              >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [1U][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [2U][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [2U][8U] 
                                              >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [2U][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [3U][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [3U][8U] 
                                              >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [3U][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [4U][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [4U][8U] 
                                              >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [4U][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [5U][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [5U][8U] 
                                              >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [5U][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [6U][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [6U][8U] 
                                              >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [6U][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [7U][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [7U][8U] 
                                              >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [7U][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [8U][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [8U][8U] 
                                              >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [8U][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [9U][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                              [9U][8U] 
                                              >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [9U][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [0xaU][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [0xaU][8U] 
                                                >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [0xaU][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [0xbU][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [0xbU][8U] 
                                                >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [0xbU][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [0xcU][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [0xcU][8U] 
                                                >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [0xcU][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [0xdU][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [0xdU][8U] 
                                                >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [0xdU][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [0xeU][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [0xeU][8U] 
                                                >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [0xeU][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    if ((((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
           [0xfU][8U] >> 0x18U) & (3U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                                [0xfU][8U] 
                                                >> 0xfU)))) 
         & (4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                         [0xfU][8U] >> 0xfU))))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current 
            = (0xffU & ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)));
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_threshold_detection 
        = ((((8U < (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_active_count_current)) 
             & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_active_threshold_crossed))) 
            & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__monbus_valid))) 
           & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__rd_valid)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_reporter_monbus_packet 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__monbus_packet;
    if (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_reporter_monbus_valid) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_valid 
            = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_reporter_monbus_valid;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_packet 
            = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_reporter_monbus_packet;
    } else if (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_debug_monbus_valid) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_valid = 1U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_packet 
            = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_debug_monbus_packet;
    } else {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_valid = 0U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_packet = 0ULL;
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[1U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [1U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[1U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [1U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[1U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [1U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[1U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [1U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[1U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [1U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[1U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [1U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[1U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [1U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[1U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [1U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[1U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [1U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[2U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [2U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[2U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [2U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[2U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [2U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[2U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [2U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[2U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [2U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[2U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [2U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[2U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [2U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[2U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [2U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[2U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [2U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[3U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [3U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[3U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [3U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[3U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [3U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[3U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [3U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[3U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [3U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[3U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [3U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[3U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [3U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[3U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [3U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[3U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [3U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[4U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [4U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[4U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [4U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[4U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [4U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[4U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [4U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[4U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [4U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[4U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [4U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[4U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [4U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[4U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [4U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[4U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [4U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[5U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [5U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[5U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [5U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[5U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [5U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[5U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [5U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[5U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [5U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[5U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [5U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[5U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [5U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[5U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [5U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[5U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [5U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[6U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [6U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[6U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [6U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[6U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [6U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[6U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [6U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[6U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [6U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[6U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [6U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[6U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [6U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[6U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [6U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[6U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [6U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[7U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [7U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[7U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [7U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[7U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [7U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[7U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [7U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[7U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [7U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[7U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [7U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[7U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [7U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[7U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [7U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[7U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [7U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[8U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [8U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[8U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [8U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[8U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [8U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[8U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [8U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[8U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [8U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[8U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [8U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[8U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [8U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[8U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [8U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[8U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [8U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[9U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [9U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[9U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [9U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[9U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [9U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[9U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [9U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[9U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [9U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[9U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [9U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[9U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [9U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[9U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [9U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[9U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [9U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xaU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xaU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xaU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xaU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xaU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xaU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xaU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xaU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xaU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xaU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xaU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xaU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xaU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xaU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xaU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xaU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xaU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xaU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xbU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xbU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xbU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xbU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xbU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xbU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xbU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xbU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xbU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xbU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xbU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xbU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xbU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xbU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xbU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xbU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xbU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xbU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xcU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xcU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xcU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xcU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xcU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xcU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xcU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xcU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xcU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xcU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xcU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xcU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xcU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xcU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xcU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xcU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xcU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xcU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xdU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xdU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xdU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xdU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xdU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xdU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xdU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xdU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xdU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xdU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xdU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xdU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xdU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xdU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xdU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xdU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xdU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xdU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xeU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xeU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xeU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xeU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xeU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xeU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xeU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xeU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xeU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xeU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xeU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xeU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xeU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xeU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xeU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xeU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xeU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xeU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xfU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xfU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xfU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xfU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xfU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xfU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xfU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xfU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xfU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xfU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xfU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xfU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xfU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xfU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xfU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xfU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table[0xfU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__trans_table
        [0xfU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_timeout_cycles 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_timeout_cycles;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__resp_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__resp_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_araddr 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_araddr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arlen 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arlen;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arsize 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arsize;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arburst 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arburst;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arlock 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arlock;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arcache 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arcache;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arprot 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arprot;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arqos 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arqos;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arregion 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arregion;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_aruser 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_aruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_rready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rdata 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rdata;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_ruser 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_ruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_err_select 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_err_select;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_error_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_error_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_timeout_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_timeout_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_compl_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_compl_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_thresh_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_thresh_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_perf_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_perf_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_addr_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_addr_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_debug_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_debug_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__monbus_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__monbus_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_monitor_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_monitor_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_error_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_error_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_latency_threshold 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_latency_threshold;
    vlSelf->axi4_master_rd_lp_mon__DOT__power_efficiency 
        = vlSelf->power_efficiency;
    vlSelf->axi4_master_rd_lp_mon__DOT__cg_power_saved_percent 
        = vlSelf->cg_power_saved_percent;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rlast 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rlast;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_timeout_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_timeout_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rvalid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_addr 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_addr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_len 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_len;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_size 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_size;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_burst 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_burst;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_perf_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_perf_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rresp 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__m_axi_rresp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_id 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_id;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__data_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__data_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__resp_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__resp_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__aresetn;
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h89982639__0 
        = ((~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__timer_activity)) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_timers_en));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arvalid 
        = axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__fub_axi_arvalid;
    vlSelf->busy = ((0U < (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__r_data_count)) 
                    | ((0U < (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__r_data_count)) 
                       | ((IData)(axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__fub_axi_arvalid) 
                          | (IData)(vlSelf->m_axi_rvalid))));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__w_wr_xfer 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__wr_ready) 
           & (IData)(axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__fub_axi_arvalid));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_data 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events = 0U;
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0U][8U] >> 0xfU)))) 
               & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported))) 
              & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0U][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [0U][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (1U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [1U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [1U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [1U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 1U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [1U][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [1U][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (2U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [2U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [2U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [2U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 2U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [2U][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [2U][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (4U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [3U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [3U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [3U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 3U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [3U][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [3U][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (8U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [4U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [4U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [4U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 4U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [4U][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [4U][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x10U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [5U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [5U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [5U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 5U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [5U][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [5U][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x20U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [6U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [6U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [6U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 6U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [6U][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [6U][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x40U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [7U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [7U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [7U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 7U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [7U][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [7U][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x80U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [8U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [8U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [8U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 8U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [8U][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [8U][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x100U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [9U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [9U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [9U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 9U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [9U][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [9U][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x200U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xaU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xaU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xaU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xaU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xaU][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [0xaU][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x400U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xbU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xbU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xbU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xbU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xbU][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [0xbU][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x800U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xcU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xcU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xcU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xcU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xcU][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [0xcU][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x1000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xdU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xdU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xdU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xdU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xdU][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [0xdU][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x2000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
        }
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events = 0U;
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0U][8U] >> 0xfU)))) 
               & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported))) 
              & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0U][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (1U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [1U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [1U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [1U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 1U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [1U][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (2U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [2U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [2U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [2U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 2U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [2U][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (4U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [3U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [3U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [3U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 3U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [3U][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (8U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [4U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [4U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [4U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 4U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [4U][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x10U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [5U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [5U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [5U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 5U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [5U][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x20U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [6U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [6U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [6U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 6U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [6U][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x40U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [7U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [7U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [7U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 7U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [7U][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x80U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [8U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [8U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [8U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 8U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [8U][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x100U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [9U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [9U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [9U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 9U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [9U][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x200U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xaU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xaU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xaU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xaU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xaU][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x400U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xbU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xbU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xbU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xbU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xbU][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x800U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xcU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xcU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xcU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xcU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xcU][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x1000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xdU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xdU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xdU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xdU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xdU][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x2000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xeU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xeU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xeU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xeU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xeU][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [0xeU][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x4000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xeU][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x4000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
        }
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark = 0U;
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0U][8U] >> 0xfU)))) 
               & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported))) 
              & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (1U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [1U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [1U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [1U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 1U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (2U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [2U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [2U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [2U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 2U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (4U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [3U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [3U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [3U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 3U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (8U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [4U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [4U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [4U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 4U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x10U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [5U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [5U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [5U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 5U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x20U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [6U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [6U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [6U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 6U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x40U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [7U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [7U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [7U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 7U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x80U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [8U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [8U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [8U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 8U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x100U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [9U][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [9U][8U] >> 0xfU))) | 
                (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [9U][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 9U))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x200U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xaU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xaU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xaU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xaU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x400U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xbU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xbU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xbU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xbU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x800U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xcU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xcU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xcU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xcU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x1000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xdU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xdU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xdU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xdU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x2000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xeU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xeU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xeU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xeU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x4000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    if ((0x1000000U & vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
         [0xfU][8U])) {
        if ((((((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xfU][8U] >> 0xfU))) 
                | (3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                [0xfU][8U] >> 0xfU)))) 
               & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_event_reported) 
                     >> 0xfU))) & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid)) 
             & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready))) {
            if ((4U != (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xfU][8U] >> 0xfU)))) {
                if ((3U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                                  [0xfU][8U] >> 0xfU)))) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events 
                        = (0x8000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_completion_events));
                }
            }
            if ((4U == (7U & (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__r_trans_table_local
                              [0xfU][8U] >> 0xfU)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events 
                    = (0x8000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_error_events));
            }
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark 
                = (0x8000U | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_events_to_mark));
        }
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_write 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_pkt_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_axi_pkt_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__cfg_conflict_error 
        = vlSelf->cfg_conflict_error;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cfg_conflict_error 
        = vlSelf->cfg_conflict_error;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_conflict_error 
        = vlSelf->cfg_conflict_error;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_conflict_error 
        = vlSelf->cfg_conflict_error;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__base_monbus_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[1U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[1U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[1U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[1U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[1U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[1U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[1U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[1U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[1U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[2U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[2U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[2U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[2U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[2U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[2U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[2U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[2U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[2U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[3U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[3U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[3U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[3U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[3U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[3U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[3U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[3U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[3U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[4U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[4U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[4U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[4U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[4U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[4U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[4U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[4U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[4U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[5U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[5U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[5U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[5U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[5U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[5U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[5U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[5U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[5U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[6U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[6U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[6U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[6U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[6U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[6U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[6U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[6U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[6U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[7U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[7U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[7U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[7U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[7U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[7U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[7U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[7U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[7U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[8U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[8U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[8U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[8U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[8U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[8U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[8U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[8U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[8U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[9U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[9U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[9U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[9U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[9U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[9U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[9U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[9U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[9U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xaU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xaU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xaU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xaU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xaU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xaU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xaU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xaU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xaU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xbU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xbU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xbU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xbU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xbU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xbU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xbU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xbU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xbU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xcU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xcU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xcU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xcU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xcU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xcU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xcU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xcU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xcU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xdU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xdU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xdU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xdU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xdU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xdU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xdU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xdU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xdU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xeU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xeU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xeU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xeU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xeU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xeU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xeU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xeU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xeU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xfU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xfU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xfU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xfU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xfU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xfU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xfU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xfU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__trans_table[0xfU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[1U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[1U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[1U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[1U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[1U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[1U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[1U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[1U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[1U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [1U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[2U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[2U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[2U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[2U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[2U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[2U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[2U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[2U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[2U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [2U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[3U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[3U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[3U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[3U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[3U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[3U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[3U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[3U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[3U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [3U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[4U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[4U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[4U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[4U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[4U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[4U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[4U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[4U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[4U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [4U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[5U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[5U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[5U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[5U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[5U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[5U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[5U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[5U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[5U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [5U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[6U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[6U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[6U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[6U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[6U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[6U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[6U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[6U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[6U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [6U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[7U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[7U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[7U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[7U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[7U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[7U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[7U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[7U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[7U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [7U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[8U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[8U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[8U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[8U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[8U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[8U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[8U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[8U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[8U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [8U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[9U][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[9U][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[9U][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[9U][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[9U][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[9U][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[9U][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[9U][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[9U][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [9U][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xaU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xaU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xaU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xaU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xaU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xaU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xaU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xaU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xaU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xaU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xbU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xbU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xbU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xbU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xbU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xbU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xbU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xbU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xbU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xbU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xcU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xcU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xcU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xcU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xcU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xcU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xcU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xcU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xcU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xcU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xdU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xdU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xdU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xdU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xdU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xdU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xdU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xdU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xdU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xdU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xeU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xeU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xeU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xeU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xeU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xeU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xeU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xeU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xeU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xeU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xfU][0U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][0U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xfU][1U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][1U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xfU][2U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][2U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xfU][3U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][3U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xfU][4U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][4U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xfU][5U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][5U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xfU][6U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][6U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xfU][7U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][7U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__trans_table[0xfU][8U] 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__w_trans_table
        [0xfU][8U];
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_araddr 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_araddr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arlen 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arlen;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arsize 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arsize;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arburst 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arburst;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arlock 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arlock;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arcache 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arcache;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arprot 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arprot;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arqos 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arqos;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arregion 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arregion;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_aruser 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_aruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_rready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_rready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_rdata 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rdata;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_ruser 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_ruser;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_axi_err_select 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_err_select;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_axi_error_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_error_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_axi_timeout_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_timeout_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_axi_compl_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_compl_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_axi_thresh_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_thresh_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_axi_perf_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_perf_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_axi_addr_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_addr_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_axi_debug_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_debug_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__monbus_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__monbus_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_compl_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_monitor_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_error_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_error_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_latency_threshold 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_latency_threshold;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_arready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_arready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_rlast 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rlast;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__data_last 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rlast;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_timeout_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_timeout_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_rvalid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__data_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__cmd_addr 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_addr;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__cmd_len 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_len;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__cmd_size 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_size;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__cmd_burst 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_burst;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_threshold_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_perf_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_perf_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_perf_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__cmd_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_rid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__data_id 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__resp_id 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_rresp 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rresp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__data_resp 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rresp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__resp_code 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__m_axi_rresp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__cmd_id 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_id;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__data_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__data_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__resp_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__resp_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__aclk_timers 
        = ((1U & (~ (IData)(axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h89982639__0))) 
           && (IData)(vlSelf->aclk_lp));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_timers_gated 
        = axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h89982639__0;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arvalid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__fub_axi_arvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__busy = vlSelf->busy;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__busy 
        = vlSelf->busy;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__busy 
        = vlSelf->busy;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__busy 
        = vlSelf->busy;
    vlSelf->axi4_master_rd_lp_mon__DOT__pm_state_next 
        = vlSelf->axi4_master_rd_lp_mon__DOT__pm_state;
    if ((0U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state))) {
        if (((((IData)(vlSelf->cfg_lp_enable) & (~ (IData)(vlSelf->busy))) 
              & (0U == (IData)(vlSelf->active_transactions))) 
             & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__idle_counter) 
                >= (IData)(vlSelf->cfg_sleep_threshold)))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__pm_state_next = 1U;
        }
    } else if ((1U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state))) {
        if (((IData)(vlSelf->busy) | (0U < (IData)(vlSelf->active_transactions)))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__pm_state_next = 0U;
        } else if (((IData)(vlSelf->cfg_sleep_enable) 
                    & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__idle_counter) 
                       >= (0xffU & VL_SHIFTL_III(8,8,32, (IData)(vlSelf->cfg_sleep_threshold), 1U))))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__pm_state_next = 2U;
        }
    } else if ((2U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state))) {
        vlSelf->axi4_master_rd_lp_mon__DOT__pm_state_next = 3U;
    } else if ((3U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state))) {
        if (((IData)(vlSelf->fub_axi_arvalid) | (IData)(vlSelf->busy))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__pm_state_next = 4U;
        }
    } else if ((4U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state))) {
        if ((8U <= (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__wake_counter))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__pm_state_next = 0U;
        }
    } else if ((5U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state))) {
        if ((8U <= (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__vf_switch_counter))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__pm_state_next = 0U;
        }
    } else if ((6U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__pm_state))) {
        if ((1U & (~ (IData)(vlSelf->cfg_lp_enable)))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__pm_state_next = 0U;
        }
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi_activity 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__w_wr_xfer) 
           | ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__w_rd_xfer) 
              | ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__w_rd_xfer) 
                 | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__w_wr_xfer))));
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT____Vcellinp__write_pointer_inst__enable 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_write));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_axi_pkt_mask 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__cfg_axi_pkt_mask;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_protocol 
        = (7U & (IData)((vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_packet 
                         >> 0x39U)));
    vlSelf->monbus_packet = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_packet;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_compl_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_compl_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_error_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_error_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_latency_threshold 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_latency_threshold;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cmd_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__data_last 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__data_last;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_timeout_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_timeout_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__wr_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__m_axi_rvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__data_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__data_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_threshold_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_threshold_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_perf_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__cfg_perf_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__data_id 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__data_id;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__resp_id 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__resp_id;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__data_resp 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__data_resp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__resp_code 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__resp_code;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__axi_aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__axi_aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__axi_aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__r_channel__DOT__axi_aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__aresetn;
    vlSelf->cg_timers_gated = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_timers_gated;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arvalid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__monitor_activity 
        = ((IData)(vlSelf->cfg_monitor_enable) & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi_activity) 
                                                  | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__busy)));
    if (axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT____Vcellinp__write_pointer_inst__enable) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__enable = 1U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next 
            = (0xfU & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_wr_addr) 
                        == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__w_max_val))
                        ? (8U & ((~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr) 
                                     >> 3U)) << 3U))
                        : ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr))));
    } else {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__enable = 0U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next 
            = (0xfU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr));
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__monbus_packet 
        = vlSelf->monbus_packet;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__monbus_packet 
        = vlSelf->monbus_packet;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__monbus_packet 
        = vlSelf->monbus_packet;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__monbus_packet 
        = vlSelf->monbus_packet;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__base_monbus_packet 
        = vlSelf->monbus_packet;
    __Vfunc_get_event_data__2__pkt = vlSelf->monbus_packet;
    __Vfunc_get_event_data__2__Vfuncout = (0xfffffffffULL 
                                           & __Vfunc_get_event_data__2__pkt);
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_data 
        = __Vfunc_get_event_data__2__Vfuncout;
    __Vfunc_get_packet_type__0__pkt = vlSelf->monbus_packet;
    __Vfunc_get_packet_type__0__Vfuncout = (0xfU & (IData)(
                                                           (__Vfunc_get_packet_type__0__pkt 
                                                            >> 0x3cU)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type 
        = __Vfunc_get_packet_type__0__Vfuncout;
    __Vfunc_get_event_code__1__pkt = vlSelf->monbus_packet;
    __Vfunc_get_event_code__1__Vfuncout = (0xfU & (IData)(
                                                          (__Vfunc_get_event_code__1__pkt 
                                                           >> 0x36U)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_code 
        = __Vfunc_get_event_code__1__Vfuncout;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__cfg_compl_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_compl_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__cfg_error_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_error_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__latency_threshold 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_latency_threshold;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__cmd_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cmd_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__data_last 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__data_last;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__cfg_timeout_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_timeout_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__cfg_timeout_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_timeout_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__data_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__data_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__cfg_threshold_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_threshold_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__cfg_perf_enable 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__cfg_perf_enable;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__data_id 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__data_id;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__resp_id 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__resp_id;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__data_resp 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__data_resp;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__resp_code 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__resp_code;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__trans_mgr__DOT__aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timeout__DOT__aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__cg_timers_gated 
        = vlSelf->cg_timers_gated;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__wr_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arvalid;
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h3626690e__0 
        = ((~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__monitor_activity)) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_monitor_en));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__wr_ptr_bin 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__rdom_wr_ptr_bin 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_wr_ptr_bin_next 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_drop = 0U;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_masked = 0U;
    if (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__base_monbus_valid) {
        if ((0U == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_protocol))) {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_drop 
                = (1U & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT____Vcellinp__lp_core_inst__cfg_axi_pkt_mask) 
                         >> (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type)));
            if ((1U & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_drop)))) {
                vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_masked 
                    = (1U & ((8U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type))
                              ? ((4U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type))
                                  ? ((1U & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type) 
                                            >> 1U)) 
                                     && ((1U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type)) 
                                         && (1U & ((IData)(vlSelf->cfg_axi_debug_mask) 
                                                   >> (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_code)))))
                                  : ((1U & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type) 
                                               >> 1U))) 
                                     && ((1U & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type))) 
                                         && (1U & ((IData)(vlSelf->cfg_axi_addr_mask) 
                                                   >> (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_code))))))
                              : ((4U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type))
                                  ? ((1U & (~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type) 
                                               >> 1U))) 
                                     && ((1U & (~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type))) 
                                         && (1U & ((IData)(vlSelf->cfg_axi_perf_mask) 
                                                   >> (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_code)))))
                                  : ((2U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type))
                                      ? ((1U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type))
                                          ? ((IData)(vlSelf->cfg_axi_timeout_mask) 
                                             >> (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_code))
                                          : ((IData)(vlSelf->cfg_axi_thresh_mask) 
                                             >> (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_code)))
                                      : ((1U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_type))
                                          ? ((IData)(vlSelf->cfg_axi_compl_mask) 
                                             >> (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_code))
                                          : ((IData)(vlSelf->cfg_axi_error_mask) 
                                             >> (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_code)))))));
                if (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_event_masked) {
                    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_drop = 1U;
                }
            }
        } else {
            vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_drop = 1U;
        }
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__clk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__axi_aclk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__rst_n 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__axi_aresetn 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__aclk_monitor 
        = ((1U & (~ (IData)(axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h3626690e__0))) 
           && (IData)(vlSelf->aclk_lp));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_monitor_gated 
        = axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h3626690e__0;
    vlSelf->monbus_valid = ((~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_drop)) 
                            & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_valid));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__base_monbus_ready 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_drop) 
           | (IData)(vlSelf->monbus_ready));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__clk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__clk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__clk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__axi_aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__clk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__axi_aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__wr_clk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__axi_aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__rd_clk 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__axi_aclk;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__prescaler_counter__DOT__rst_n 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__timer__DOT__timer_counter__DOT__rst_n;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__rst_n 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__axi_aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__rst_n 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__axi_aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__wr_rst_n 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__axi_aresetn;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__rd_rst_n 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__axi_aresetn;
    vlSelf->cg_monitor_gated = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_monitor_gated;
    vlSelf->axi4_master_rd_lp_mon__DOT__monbus_valid 
        = vlSelf->monbus_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__monbus_valid 
        = vlSelf->monbus_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__monbus_valid 
        = vlSelf->monbus_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__monbus_valid 
        = vlSelf->monbus_valid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__reporter_activity 
        = ((IData)(vlSelf->monbus_valid) | ((IData)(vlSelf->cfg_error_enable) 
                                            | (IData)(vlSelf->cfg_perf_enable)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__base_monbus_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_rd_ready 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__base_monbus_ready) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__monbus_valid));
    vlSelf->axi4_master_rd_lp_mon__DOT__cg_monitor_gated 
        = vlSelf->cg_monitor_gated;
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_hb4160c0e__0 
        = ((~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__reporter_activity)) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_reporter_en));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__monbus_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__rd_ready 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_rd_ready;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_read 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__rd_valid) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_rd_ready));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__aclk_reporter 
        = ((1U & (~ (IData)(axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_hb4160c0e__0))) 
           && (IData)(vlSelf->aclk_lp));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_reporter_gated 
        = axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_hb4160c0e__0;
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT____Vcellinp__read_pointer_inst__enable 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__rd_valid) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_read));
    vlSelf->cg_reporter_gated = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_reporter_gated;
    if (axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT____Vcellinp__read_pointer_inst__enable) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__enable = 1U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next 
            = (0xfU & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_rd_addr) 
                        == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__w_max_val))
                        ? (8U & ((~ ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr) 
                                     >> 3U)) << 3U))
                        : ((IData)(1U) + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr))));
    } else {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__enable = 0U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next 
            = (0xfU & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr));
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__cg_reporter_gated 
        = vlSelf->cg_reporter_gated;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__wdom_rd_ptr_bin 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__rd_ptr_bin 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_rd_ptr_bin_next 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty 
        = (1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next) 
                  ^ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed)) 
                 >> 3U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__count 
        = (0xfU & ((7U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next)) 
                   - (7U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next))));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor 
        = (1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next) 
                  ^ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next)) 
                 >> 3U));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor 
        = (1U & (((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next) 
                  ^ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next)) 
                 >> 3U));
    __VdfgTmp_h0605e096__0 = (7U & ((- (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next)) 
                                    + (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next)));
    __VdfgTmp_he93352a5__0 = (7U & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next) 
                                    - (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_rd_empty_d 
        = ((~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor_for_empty)) 
           & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed) 
              == (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__count;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_count 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__count;
    if (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_wdom_ptr_xor) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_wr_full_d 
            = ((7U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next)) 
               == (7U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__read_pointer_inst__DOT__counter_bin_next)));
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_almost_full_count 
            = __VdfgTmp_h0605e096__0;
    } else {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_wr_full_d = 0U;
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_almost_full_count 
            = __VdfgTmp_he93352a5__0;
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_almost_empty_count 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_rdom_ptr_xor)
            ? (IData)(__VdfgTmp_h0605e096__0) : (IData)(__VdfgTmp_he93352a5__0));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_wr_almost_full_d 
        = (7U <= (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_almost_full_count));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_rd_almost_empty_d 
        = (1U >= (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__w_almost_empty_count));
}
