// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop___024root.h"

#ifdef VL_DEBUG
VL_ATTR_COLD void Vtop___024root___dump_triggers__ico(Vtop___024root* vlSelf);
#endif  // VL_DEBUG

void Vtop___024root___eval_triggers__ico(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___eval_triggers__ico\n"); );
    // Body
    vlSelf->__VicoTriggered.set(0U, (IData)(vlSelf->__VicoFirstIteration));
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        Vtop___024root___dump_triggers__ico(vlSelf);
    }
#endif
}

#ifdef VL_DEBUG
VL_ATTR_COLD void Vtop___024root___dump_triggers__act(Vtop___024root* vlSelf);
#endif  // VL_DEBUG

void Vtop___024root___eval_triggers__act(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___eval_triggers__act\n"); );
    // Body
    vlSelf->__VactTriggered.set(0U, (((IData)(vlSelf->aclk_lp) 
                                      & (~ (IData)(vlSelf->__Vtrigprevexpr___TOP__aclk_lp__0))) 
                                     | ((~ (IData)(vlSelf->aresetn_lp)) 
                                        & (IData)(vlSelf->__Vtrigprevexpr___TOP__aresetn_lp__0))));
    vlSelf->__VactTriggered.set(1U, ((IData)(vlSelf->aclk_lp) 
                                     & (~ (IData)(vlSelf->__Vtrigprevexpr___TOP__aclk_lp__0))));
    vlSelf->__Vtrigprevexpr___TOP__aclk_lp__0 = vlSelf->aclk_lp;
    vlSelf->__Vtrigprevexpr___TOP__aresetn_lp__0 = vlSelf->aresetn_lp;
#ifdef VL_DEBUG
    if (VL_UNLIKELY(vlSymsp->_vm_contextp__->debug())) {
        Vtop___024root___dump_triggers__act(vlSelf);
    }
#endif
}

VL_INLINE_OPT void Vtop___024root___nba_sequent__TOP__2(Vtop___024root* vlSelf) {
    if (false && vlSelf) {}  // Prevent unused
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___nba_sequent__TOP__2\n"); );
    // Init
    CData/*2:0*/ __Vdlyvdim0__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0;
    __Vdlyvdim0__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0 = 0;
    QData/*51:0*/ __Vdlyvval__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0;
    __Vdlyvval__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0 = 0;
    CData/*0:0*/ __Vdlyvset__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0;
    __Vdlyvset__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0 = 0;
    // Body
    if (VL_UNLIKELY(((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_write) 
                     & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_wr_full)))) {
        VL_TIMEFORMAT_IINI(0xfffffff7U, 3U, std::string{" ns"}, 0xaU, vlSymsp->_vm_contextp__);
        VL_WRITEF("Error: INTR_FIFO write while fifo full, %t\n",
                  64,VL_TIME_UNITED_Q(1000),-9);
    }
    if (VL_UNLIKELY(((IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_read) 
                     & (IData)(vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_rd_empty)))) {
        VL_TIMEFORMAT_IINI(0xfffffff7U, 3U, std::string{" ns"}, 0xaU, vlSymsp->_vm_contextp__);
        VL_WRITEF("Error: INTR_FIFO read while fifo empty, %t\n",
                  64,VL_TIME_UNITED_Q(1000),-9);
    }
    __Vdlyvset__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0 = 0U;
    if (vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__w_write) {
        __Vdlyvval__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0 
            = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__w_fifo_wr_data;
        __Vdlyvset__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0 = 1U;
        __Vdlyvdim0__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0 
            = vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_wr_addr;
    }
    if (__Vdlyvset__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0) {
        vlSelf->axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem[__Vdlyvdim0__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0] 
            = __Vdlyvval__axi4_master_rd_lp_mon__DOT__lp_core_inst__DOT__axi4_master_rd_mon_inst__DOT__axi_monitor_inst__DOT__u_axi_monitor_base__DOT__reporter__DOT__intr_fifo__DOT__r_mem__v0;
    }
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
}
