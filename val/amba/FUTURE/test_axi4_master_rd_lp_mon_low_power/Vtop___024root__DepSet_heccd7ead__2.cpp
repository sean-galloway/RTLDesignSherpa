// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop___024root.h"

VL_INLINE_OPT void Vtop___024root___nba_sequent__TOP__1(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___nba_sequent__TOP__1\n"); );
    // Body
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
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arvalid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__fub_axi_arvalid;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__monitor_activity 
        = ((IData)(vlSelf->cfg_monitor_enable) & ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi_activity) 
                                                  | (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__busy)));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__ar_channel__DOT__wr_valid 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi4_master_rd_inst__DOT__fub_axi_arvalid;
}

VL_INLINE_OPT void Vtop___024root___nba_sequent__TOP__3(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___nba_sequent__TOP__3\n"); );
    // Init
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
    // Body
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_wr_full 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__wr_full;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_rd_empty 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__rd_empty;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data = 0ULL;
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
    }
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_wr_addr 
        = (7U & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_write 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_valid));
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
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_data 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data;
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT____Vcellinp__write_pointer_inst__enable 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__wr_ready) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_write));
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h3626690e__0 
        = ((~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__monitor_activity)) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_monitor_en));
    axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h89982639__0 
        = ((~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__timer_activity)) 
           & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_timers_en));
    vlSelf->monbus_valid = ((~ (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_drop)) 
                            & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__monbus_valid));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__base_monbus_ready 
        = ((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__pkt_drop) 
           | (IData)(vlSelf->monbus_ready));
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
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__aclk_monitor 
        = ((1U & (~ (IData)(axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h3626690e__0))) 
           && (IData)(vlSelf->aclk_lp));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_monitor_gated 
        = axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h3626690e__0;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__aclk_timers 
        = ((1U & (~ (IData)(axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h89982639__0))) 
           && (IData)(vlSelf->aclk_lp));
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_timers_gated 
        = axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT____VdfgExtracted_h89982639__0;
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
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__wr_ptr_bin 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__fifo_control_inst__DOT__rdom_wr_ptr_bin 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next;
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_wr_ptr_bin_next 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__write_pointer_inst__DOT__counter_bin_next;
    vlSelf->cg_monitor_gated = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_monitor_gated;
    vlSelf->cg_timers_gated = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__cg_timers_gated;
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
    vlSelf->axi4_master_rd_lp_mon__DOT__cg_monitor_gated 
        = vlSelf->cg_monitor_gated;
    vlSelf->axi4_master_rd_lp_mon__DOT__cg_timers_gated 
        = vlSelf->cg_timers_gated;
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

VL_INLINE_OPT void Vtop___024root___nba_comb__TOP__0(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___nba_comb__TOP__0\n"); );
    // Body
    vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_rd_data 
        = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem
        [vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_rd_addr];
}

void Vtop___024root___nba_sequent__TOP__0(Vtop___024root* vlSelf);
void Vtop___024root___nba_sequent__TOP__2(Vtop___024root* vlSelf);

void Vtop___024root___eval_nba(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___eval_nba\n"); );
    // Body
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        Vtop___024root___nba_sequent__TOP__0(vlSelf);
        Vtop___024root___nba_sequent__TOP__1(vlSelf);
    }
    if ((2ULL & vlSelf->__VnbaTriggered.word(0U))) {
        Vtop___024root___nba_sequent__TOP__2(vlSelf);
    }
    if ((1ULL & vlSelf->__VnbaTriggered.word(0U))) {
        Vtop___024root___nba_sequent__TOP__3(vlSelf);
    }
    if ((3ULL & vlSelf->__VnbaTriggered.word(0U))) {
        Vtop___024root___nba_comb__TOP__0(vlSelf);
    }
}

void Vtop___024root___eval_triggers__act(Vtop___024root* vlSelf);
void Vtop___024root___eval_act(Vtop___024root* vlSelf);

bool Vtop___024root___eval_phase__act(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___eval_phase__act\n"); );
    // Init
    VlTriggerVec<2> __VpreTriggered;
    CData/*0:0*/ __VactExecute;
    // Body
    Vtop___024root___eval_triggers__act(vlSelf);
    __VactExecute = vlSelf->__VactTriggered.any();
    if (__VactExecute) {
        __VpreTriggered.andNot(vlSelf->__VactTriggered, vlSelf->__VnbaTriggered);
        vlSelf->__VnbaTriggered.thisOr(vlSelf->__VactTriggered);
        Vtop___024root___eval_act(vlSelf);
    }
    return (__VactExecute);
}

bool Vtop___024root___eval_phase__nba(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___eval_phase__nba\n"); );
    // Init
    CData/*0:0*/ __VnbaExecute;
    // Body
    __VnbaExecute = vlSelf->__VnbaTriggered.any();
    if (__VnbaExecute) {
        Vtop___024root___eval_nba(vlSelf);
        vlSelf->__VnbaTriggered.clear();
    }
    return (__VnbaExecute);
}

#ifdef VL_DEBUG
VL_ATTR_COLD void Vtop___024root___dump_triggers__ico(Vtop___024root* vlSelf);
#endif  // VL_DEBUG
bool Vtop___024root___eval_phase__ico(Vtop___024root* vlSelf);
#ifdef VL_DEBUG
VL_ATTR_COLD void Vtop___024root___dump_triggers__nba(Vtop___024root* vlSelf);
#endif  // VL_DEBUG
#ifdef VL_DEBUG
VL_ATTR_COLD void Vtop___024root___dump_triggers__act(Vtop___024root* vlSelf);
#endif  // VL_DEBUG

void Vtop___024root___eval(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___eval\n"); );
    // Init
    IData/*31:0*/ __VicoIterCount;
    CData/*0:0*/ __VicoContinue;
    IData/*31:0*/ __VnbaIterCount;
    CData/*0:0*/ __VnbaContinue;
    // Body
    __VicoIterCount = 0U;
    vlSelf->__VicoFirstIteration = 1U;
    __VicoContinue = 1U;
    while (__VicoContinue) {
        if (VL_UNLIKELY((0x64U < __VicoIterCount))) {
#ifdef VL_DEBUG
            Vtop___024root___dump_triggers__ico(vlSelf);
#endif
            VL_FATAL_MT("/mnt/data/github/rtldesignsherpa/rtl/amba/axi4/axi4_master_rd_lp_mon.sv", 18, "", "Input combinational region did not converge.");
        }
        __VicoIterCount = ((IData)(1U) + __VicoIterCount);
        __VicoContinue = 0U;
        if (Vtop___024root___eval_phase__ico(vlSelf)) {
            __VicoContinue = 1U;
        }
        vlSelf->__VicoFirstIteration = 0U;
    }
    __VnbaIterCount = 0U;
    __VnbaContinue = 1U;
    while (__VnbaContinue) {
        if (VL_UNLIKELY((0x64U < __VnbaIterCount))) {
#ifdef VL_DEBUG
            Vtop___024root___dump_triggers__nba(vlSelf);
#endif
            VL_FATAL_MT("/mnt/data/github/rtldesignsherpa/rtl/amba/axi4/axi4_master_rd_lp_mon.sv", 18, "", "NBA region did not converge.");
        }
        __VnbaIterCount = ((IData)(1U) + __VnbaIterCount);
        __VnbaContinue = 0U;
        vlSelf->__VactIterCount = 0U;
        vlSelf->__VactContinue = 1U;
        while (vlSelf->__VactContinue) {
            if (VL_UNLIKELY((0x64U < vlSelf->__VactIterCount))) {
#ifdef VL_DEBUG
                Vtop___024root___dump_triggers__act(vlSelf);
#endif
                VL_FATAL_MT("/mnt/data/github/rtldesignsherpa/rtl/amba/axi4/axi4_master_rd_lp_mon.sv", 18, "", "Active region did not converge.");
            }
            vlSelf->__VactIterCount = ((IData)(1U) 
                                       + vlSelf->__VactIterCount);
            vlSelf->__VactContinue = 0U;
            if (Vtop___024root___eval_phase__act(vlSelf)) {
                vlSelf->__VactContinue = 1U;
            }
        }
        if (Vtop___024root___eval_phase__nba(vlSelf)) {
            __VnbaContinue = 1U;
        }
    }
}

#ifdef VL_DEBUG
void Vtop___024root___eval_debug_assertions(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((vlSelf->aclk & 0xfeU))) {
        Verilated::overWidthError("aclk");}
    if (VL_UNLIKELY((vlSelf->aresetn & 0xfeU))) {
        Verilated::overWidthError("aresetn");}
    if (VL_UNLIKELY((vlSelf->aclk_lp & 0xfeU))) {
        Verilated::overWidthError("aclk_lp");}
    if (VL_UNLIKELY((vlSelf->aresetn_lp & 0xfeU))) {
        Verilated::overWidthError("aresetn_lp");}
    if (VL_UNLIKELY((vlSelf->fub_axi_arsize & 0xf8U))) {
        Verilated::overWidthError("fub_axi_arsize");}
    if (VL_UNLIKELY((vlSelf->fub_axi_arburst & 0xfcU))) {
        Verilated::overWidthError("fub_axi_arburst");}
    if (VL_UNLIKELY((vlSelf->fub_axi_arlock & 0xfeU))) {
        Verilated::overWidthError("fub_axi_arlock");}
    if (VL_UNLIKELY((vlSelf->fub_axi_arcache & 0xf0U))) {
        Verilated::overWidthError("fub_axi_arcache");}
    if (VL_UNLIKELY((vlSelf->fub_axi_arprot & 0xf8U))) {
        Verilated::overWidthError("fub_axi_arprot");}
    if (VL_UNLIKELY((vlSelf->fub_axi_arqos & 0xf0U))) {
        Verilated::overWidthError("fub_axi_arqos");}
    if (VL_UNLIKELY((vlSelf->fub_axi_arregion & 0xf0U))) {
        Verilated::overWidthError("fub_axi_arregion");}
    if (VL_UNLIKELY((vlSelf->fub_axi_aruser & 0xfeU))) {
        Verilated::overWidthError("fub_axi_aruser");}
    if (VL_UNLIKELY((vlSelf->fub_axi_arvalid & 0xfeU))) {
        Verilated::overWidthError("fub_axi_arvalid");}
    if (VL_UNLIKELY((vlSelf->fub_axi_rready & 0xfeU))) {
        Verilated::overWidthError("fub_axi_rready");}
    if (VL_UNLIKELY((vlSelf->m_axi_arready & 0xfeU))) {
        Verilated::overWidthError("m_axi_arready");}
    if (VL_UNLIKELY((vlSelf->m_axi_rresp & 0xfcU))) {
        Verilated::overWidthError("m_axi_rresp");}
    if (VL_UNLIKELY((vlSelf->m_axi_rlast & 0xfeU))) {
        Verilated::overWidthError("m_axi_rlast");}
    if (VL_UNLIKELY((vlSelf->m_axi_ruser & 0xfeU))) {
        Verilated::overWidthError("m_axi_ruser");}
    if (VL_UNLIKELY((vlSelf->m_axi_rvalid & 0xfeU))) {
        Verilated::overWidthError("m_axi_rvalid");}
    if (VL_UNLIKELY((vlSelf->cfg_monitor_enable & 0xfeU))) {
        Verilated::overWidthError("cfg_monitor_enable");}
    if (VL_UNLIKELY((vlSelf->cfg_error_enable & 0xfeU))) {
        Verilated::overWidthError("cfg_error_enable");}
    if (VL_UNLIKELY((vlSelf->cfg_timeout_enable & 0xfeU))) {
        Verilated::overWidthError("cfg_timeout_enable");}
    if (VL_UNLIKELY((vlSelf->cfg_perf_enable & 0xfeU))) {
        Verilated::overWidthError("cfg_perf_enable");}
    if (VL_UNLIKELY((vlSelf->cfg_lp_enable & 0xfeU))) {
        Verilated::overWidthError("cfg_lp_enable");}
    if (VL_UNLIKELY((vlSelf->cfg_sleep_enable & 0xfeU))) {
        Verilated::overWidthError("cfg_sleep_enable");}
    if (VL_UNLIKELY((vlSelf->cfg_coalesce_enable & 0xfeU))) {
        Verilated::overWidthError("cfg_coalesce_enable");}
    if (VL_UNLIKELY((vlSelf->cfg_power_budget_enable 
                     & 0xfeU))) {
        Verilated::overWidthError("cfg_power_budget_enable");}
    if (VL_UNLIKELY((vlSelf->cfg_dvfs_enable & 0xfeU))) {
        Verilated::overWidthError("cfg_dvfs_enable");}
    if (VL_UNLIKELY((vlSelf->cfg_vf_level & 0xfcU))) {
        Verilated::overWidthError("cfg_vf_level");}
    if (VL_UNLIKELY((vlSelf->cfg_vf_auto & 0xfeU))) {
        Verilated::overWidthError("cfg_vf_auto");}
    if (VL_UNLIKELY((vlSelf->cfg_cg_enable & 0xfeU))) {
        Verilated::overWidthError("cfg_cg_enable");}
    if (VL_UNLIKELY((vlSelf->cfg_cg_force_on & 0xfeU))) {
        Verilated::overWidthError("cfg_cg_force_on");}
    if (VL_UNLIKELY((vlSelf->cfg_cg_ultra_aggressive 
                     & 0xfeU))) {
        Verilated::overWidthError("cfg_cg_ultra_aggressive");}
    if (VL_UNLIKELY((vlSelf->monbus_ready & 0xfeU))) {
        Verilated::overWidthError("monbus_ready");}
}
#endif  // VL_DEBUG
