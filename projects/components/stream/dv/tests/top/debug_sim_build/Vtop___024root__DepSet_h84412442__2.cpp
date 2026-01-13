// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop___024root.h"

VL_INLINE_OPT void Vtop___024root___nba_comb__TOP__1(Vtop___024root* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___nba_comb__TOP__1\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    VlWide<64>/*2047:0*/ __Vtemp_6;
    VlWide<80>/*2559:0*/ __Vtemp_7;
    VlWide<96>/*3071:0*/ __Vtemp_8;
    VlWide<112>/*3583:0*/ __Vtemp_9;
    // Body
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[0U] 
        = (IData)((((QData)((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_alloc_space_free)) 
                    << 0x27U) | (((QData)((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_alloc_space_free)) 
                                  << 0x1aU) | (QData)((IData)(
                                                              (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_alloc_space_free) 
                                                                << 0xdU) 
                                                               | (IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_alloc_space_free)))))));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[1U] 
        = (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_alloc_space_free) 
            << 0x14U) | (IData)(((((QData)((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_alloc_space_free)) 
                                   << 0x27U) | (((QData)((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_alloc_space_free)) 
                                                 << 0x1aU) 
                                                | (QData)((IData)(
                                                                  (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_alloc_space_free) 
                                                                    << 0xdU) 
                                                                   | (IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_alloc_space_free)))))) 
                                 >> 0x20U)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[2U] 
        = (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_alloc_space_free) 
            << 0x1bU) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_alloc_space_free) 
                          << 0xeU) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_alloc_space_free) 
                                       << 1U) | ((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_alloc_space_free) 
                                                 >> 0xcU))));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[3U] 
        = ((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_alloc_space_free) 
           >> 5U);
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__dbg_bridge_pending 
        = (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.dbg_bridge_pending) 
            << 7U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.dbg_bridge_pending) 
                       << 6U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.dbg_bridge_pending) 
                                  << 5U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.dbg_bridge_pending) 
                                             << 4U) 
                                            | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.dbg_bridge_pending) 
                                                << 3U) 
                                               | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.dbg_bridge_pending) 
                                                   << 2U) 
                                                  | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.dbg_bridge_pending) 
                                                      << 1U) 
                                                     | (IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.dbg_bridge_pending))))))));
    __Vtemp_6[0U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[0U];
    __Vtemp_6[1U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[1U];
    __Vtemp_6[2U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[2U];
    __Vtemp_6[3U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[3U];
    __Vtemp_6[4U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[4U];
    __Vtemp_6[5U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[5U];
    __Vtemp_6[6U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[6U];
    __Vtemp_6[7U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[7U];
    __Vtemp_6[8U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[8U];
    __Vtemp_6[9U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[9U];
    __Vtemp_6[0xaU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[0xaU];
    __Vtemp_6[0xbU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[0xbU];
    __Vtemp_6[0xcU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[0xcU];
    __Vtemp_6[0xdU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[0xdU];
    __Vtemp_6[0xeU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[0xeU];
    __Vtemp_6[0xfU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_data[0xfU];
    __Vtemp_6[0x10U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[0U];
    __Vtemp_6[0x11U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[1U];
    __Vtemp_6[0x12U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[2U];
    __Vtemp_6[0x13U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[3U];
    __Vtemp_6[0x14U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[4U];
    __Vtemp_6[0x15U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[5U];
    __Vtemp_6[0x16U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[6U];
    __Vtemp_6[0x17U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[7U];
    __Vtemp_6[0x18U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[8U];
    __Vtemp_6[0x19U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[9U];
    __Vtemp_6[0x1aU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[0xaU];
    __Vtemp_6[0x1bU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[0xbU];
    __Vtemp_6[0x1cU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[0xcU];
    __Vtemp_6[0x1dU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[0xdU];
    __Vtemp_6[0x1eU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[0xeU];
    __Vtemp_6[0x1fU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_data[0xfU];
    __Vtemp_6[0x20U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[0U];
    __Vtemp_6[0x21U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[1U];
    __Vtemp_6[0x22U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[2U];
    __Vtemp_6[0x23U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[3U];
    __Vtemp_6[0x24U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[4U];
    __Vtemp_6[0x25U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[5U];
    __Vtemp_6[0x26U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[6U];
    __Vtemp_6[0x27U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[7U];
    __Vtemp_6[0x28U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[8U];
    __Vtemp_6[0x29U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[9U];
    __Vtemp_6[0x2aU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[0xaU];
    __Vtemp_6[0x2bU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[0xbU];
    __Vtemp_6[0x2cU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[0xcU];
    __Vtemp_6[0x2dU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[0xdU];
    __Vtemp_6[0x2eU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[0xeU];
    __Vtemp_6[0x2fU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_data[0xfU];
    __Vtemp_6[0x30U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[0U];
    __Vtemp_6[0x31U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[1U];
    __Vtemp_6[0x32U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[2U];
    __Vtemp_6[0x33U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[3U];
    __Vtemp_6[0x34U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[4U];
    __Vtemp_6[0x35U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[5U];
    __Vtemp_6[0x36U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[6U];
    __Vtemp_6[0x37U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[7U];
    __Vtemp_6[0x38U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[8U];
    __Vtemp_6[0x39U] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[9U];
    __Vtemp_6[0x3aU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[0xaU];
    __Vtemp_6[0x3bU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[0xbU];
    __Vtemp_6[0x3cU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[0xcU];
    __Vtemp_6[0x3dU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[0xdU];
    __Vtemp_6[0x3eU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[0xeU];
    __Vtemp_6[0x3fU] = vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_data[0xfU];
    VL_CONCAT_WWW(2560,2048,512, __Vtemp_7, __Vtemp_6, vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_wr_sram_data);
    VL_CONCAT_WWW(3072,2560,512, __Vtemp_8, __Vtemp_7, vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_wr_sram_data);
    VL_CONCAT_WWW(3584,3072,512, __Vtemp_9, __Vtemp_8, vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_wr_sram_data);
    VL_CONCAT_WWW(4096,3584,512, vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_sram_data_per_channel, __Vtemp_9, vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_wr_sram_data);
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_read_engine__DOT__axi_rd_alloc_space_free[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[0U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_read_engine__DOT__axi_rd_alloc_space_free[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[1U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_read_engine__DOT__axi_rd_alloc_space_free[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[2U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_read_engine__DOT__axi_rd_alloc_space_free[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[3U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_alloc_space_free[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[0U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_alloc_space_free[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[1U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_alloc_space_free[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[2U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_alloc_space_free[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_space_free[3U];
}

VL_INLINE_OPT void Vtop___024root___nba_comb__TOP__3(Vtop___024root* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___nba_comb__TOP__3\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Body
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_sram_ready_per_channel 
        = (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_ready) 
            << 7U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_ready) 
                       << 6U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_ready) 
                                  << 5U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_ready) 
                                             << 4U) 
                                            | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_ready) 
                                                << 3U) 
                                               | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_ready) 
                                                   << 2U) 
                                                  | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_ready) 
                                                      << 1U) 
                                                     | (IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_ready))))))));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__dbg_bridge_out_valid 
        = (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.dbg_bridge_out_valid) 
            << 7U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.dbg_bridge_out_valid) 
                       << 6U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.dbg_bridge_out_valid) 
                                  << 5U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.dbg_bridge_out_valid) 
                                             << 4U) 
                                            | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.dbg_bridge_out_valid) 
                                                << 3U) 
                                               | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.dbg_bridge_out_valid) 
                                                   << 2U) 
                                                  | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.dbg_bridge_out_valid) 
                                                      << 1U) 
                                                     | (IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.dbg_bridge_out_valid))))))));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_sram_valid 
        = (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_valid) 
            << 7U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_valid) 
                       << 6U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_valid) 
                                  << 5U) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_valid) 
                                             << 4U) 
                                            | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_wr_sram_valid) 
                                                << 3U) 
                                               | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_wr_sram_valid) 
                                                   << 2U) 
                                                  | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_wr_sram_valid) 
                                                      << 1U) 
                                                     | (IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_wr_sram_valid))))))));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__axi_wr_sram_valid 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_sram_valid;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_sram_valid 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_sram_valid;
}

extern const VlUnpacked<CData/*2:0*/, 256> Vtop__ConstPool__TABLE_h256e5f3b_0;
extern const VlUnpacked<CData/*0:0*/, 256> Vtop__ConstPool__TABLE_hb32d1eae_0;

VL_INLINE_OPT void Vtop___024root___nba_comb__TOP__9(Vtop___024root* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___nba_comb__TOP__9\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    CData/*7:0*/ __Vtableidx34;
    __Vtableidx34 = 0;
    // Body
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[0U] 
        = (IData)((((QData)((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_wr_drain_data_avail)) 
                    << 0x27U) | (((QData)((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_wr_drain_data_avail)) 
                                  << 0x1aU) | (QData)((IData)(
                                                              (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_wr_drain_data_avail) 
                                                                << 0xdU) 
                                                               | (IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_wr_drain_data_avail)))))));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[1U] 
        = (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_drain_data_avail) 
            << 0x14U) | (IData)(((((QData)((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_wr_drain_data_avail)) 
                                   << 0x27U) | (((QData)((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_wr_drain_data_avail)) 
                                                 << 0x1aU) 
                                                | (QData)((IData)(
                                                                  (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_wr_drain_data_avail) 
                                                                    << 0xdU) 
                                                                   | (IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_wr_drain_data_avail)))))) 
                                 >> 0x20U)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[2U] 
        = (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_drain_data_avail) 
            << 0x1bU) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_drain_data_avail) 
                          << 0xeU) | (((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_drain_data_avail) 
                                       << 1U) | ((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_drain_data_avail) 
                                                 >> 0xcU))));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[3U] 
        = ((IData)(vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_drain_data_avail) 
           >> 5U);
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__axi_wr_drain_data_avail[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[0U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__axi_wr_drain_data_avail[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[1U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__axi_wr_drain_data_avail[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[2U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__axi_wr_drain_data_avail[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[3U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_drain_data_avail[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[0U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_drain_data_avail[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[1U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_drain_data_avail[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[2U];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_drain_data_avail[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[3U];
    if ((1U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid))) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = ((0xffffffffffffff00ULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size) 
               | (IData)((IData)((0xffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[0U] 
                                            <= ((IData)(1U) 
                                                + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))
                                            ? (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[0U] 
                                               - (IData)(1U))
                                            : (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats))))));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = ((0xfeU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data)) 
               | ((0x1fffU & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[0U]) 
                  >= (0x1fffU & ((IData)(1U) + (0xffU 
                                                & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size))))));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = ((0xfeU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst)) 
               | ((0U < vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[0U]) 
                  & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[0U] 
                     <= ((IData)(1U) + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = ((0xfeU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
               | (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data) 
                        | (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst))));
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = (0xfeU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = (0xffffffffffffff00ULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size);
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = (0xfeU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = (0xfeU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok));
    }
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding 
        = ((0xfeU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding)) 
           | (1U & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__r_outstanding_limit))));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request 
        = ((0xfeU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request)) 
           | (1U & (((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid) 
                     & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
                    & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding))));
    if ((2U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid))) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = ((0xffffffffffff00ffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size) 
               | ((QData)((IData)((0xffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[1U] 
                                             <= ((IData)(1U) 
                                                 + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))
                                             ? (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[1U] 
                                                - (IData)(1U))
                                             : (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats))))) 
                  << 8U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = ((0xfdU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data)) 
               | (((0x1fffU & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[0U] 
                               >> 0xdU)) >= (0x1fffU 
                                             & ((IData)(1U) 
                                                + (0xffU 
                                                   & (IData)(
                                                             (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
                                                              >> 8U)))))) 
                  << 1U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = ((0xfdU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst)) 
               | (((0U < vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[1U]) 
                   & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[1U] 
                      <= ((IData)(1U) + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))) 
                  << 1U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = ((0xfdU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
               | (2U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data) 
                        | (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst))));
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = (0xfdU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = (0xffffffffffff00ffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size);
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = (0xfdU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = (0xfdU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok));
    }
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding 
        = ((0xfdU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding)) 
           | (2U & ((~ ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__r_outstanding_limit) 
                        >> 1U)) << 1U)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request 
        = ((0xfdU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request)) 
           | (2U & (((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid) 
                     & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
                    & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding))));
    if ((4U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid))) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = ((0xffffffffff00ffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size) 
               | ((QData)((IData)((0xffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[2U] 
                                             <= ((IData)(1U) 
                                                 + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))
                                             ? (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[2U] 
                                                - (IData)(1U))
                                             : (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats))))) 
                  << 0x10U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = ((0xfbU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data)) 
               | (((0x1fffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[1U] 
                                << 6U) | (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[0U] 
                                          >> 0x1aU))) 
                   >= (0x1fffU & ((IData)(1U) + (0xffU 
                                                 & (IData)(
                                                           (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
                                                            >> 0x10U)))))) 
                  << 2U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = ((0xfbU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst)) 
               | (((0U < vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[2U]) 
                   & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[2U] 
                      <= ((IData)(1U) + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))) 
                  << 2U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = ((0xfbU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
               | (4U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data) 
                        | (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst))));
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = (0xfbU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = (0xffffffffff00ffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size);
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = (0xfbU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = (0xfbU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok));
    }
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding 
        = ((0xfbU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding)) 
           | (4U & ((~ ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__r_outstanding_limit) 
                        >> 2U)) << 2U)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request 
        = ((0xfbU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request)) 
           | (4U & (((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid) 
                     & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
                    & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding))));
    if ((8U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid))) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = ((0xffffffff00ffffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size) 
               | ((QData)((IData)((0xffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[3U] 
                                             <= ((IData)(1U) 
                                                 + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))
                                             ? (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[3U] 
                                                - (IData)(1U))
                                             : (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats))))) 
                  << 0x18U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = ((0xf7U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data)) 
               | (((0x1fffU & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[1U] 
                               >> 7U)) >= (0x1fffU 
                                           & ((IData)(1U) 
                                              + (0xffU 
                                                 & (IData)(
                                                           (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
                                                            >> 0x18U)))))) 
                  << 3U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = ((0xf7U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst)) 
               | (((0U < vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[3U]) 
                   & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[3U] 
                      <= ((IData)(1U) + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))) 
                  << 3U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = ((0xf7U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
               | (8U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data) 
                        | (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst))));
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = (0xf7U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = (0xffffffff00ffffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size);
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = (0xf7U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = (0xf7U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok));
    }
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding 
        = ((0xf7U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding)) 
           | (8U & ((~ ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__r_outstanding_limit) 
                        >> 3U)) << 3U)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request 
        = ((0xf7U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request)) 
           | (8U & (((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid) 
                     & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
                    & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding))));
    if ((0x10U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid))) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = ((0xffffff00ffffffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size) 
               | ((QData)((IData)((0xffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[4U] 
                                             <= ((IData)(1U) 
                                                 + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))
                                             ? (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[4U] 
                                                - (IData)(1U))
                                             : (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats))))) 
                  << 0x20U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = ((0xefU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data)) 
               | (((0x1fffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[2U] 
                                << 0xcU) | (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[1U] 
                                            >> 0x14U))) 
                   >= (0x1fffU & ((IData)(1U) + (0xffU 
                                                 & (IData)(
                                                           (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
                                                            >> 0x20U)))))) 
                  << 4U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = ((0xefU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst)) 
               | (((0U < vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[4U]) 
                   & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[4U] 
                      <= ((IData)(1U) + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))) 
                  << 4U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = ((0xefU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
               | (0x10U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data) 
                           | (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst))));
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = (0xefU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = (0xffffff00ffffffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size);
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = (0xefU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = (0xefU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok));
    }
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding 
        = ((0xefU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding)) 
           | (0x10U & ((~ ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__r_outstanding_limit) 
                           >> 4U)) << 4U)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request 
        = ((0xefU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request)) 
           | (0x10U & (((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid) 
                        & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
                       & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding))));
    if ((0x20U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid))) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = ((0xffff00ffffffffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size) 
               | ((QData)((IData)((0xffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[5U] 
                                             <= ((IData)(1U) 
                                                 + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))
                                             ? (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[5U] 
                                                - (IData)(1U))
                                             : (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats))))) 
                  << 0x28U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = ((0xdfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data)) 
               | (((0x1fffU & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[2U] 
                               >> 1U)) >= (0x1fffU 
                                           & ((IData)(1U) 
                                              + (0xffU 
                                                 & (IData)(
                                                           (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
                                                            >> 0x28U)))))) 
                  << 5U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = ((0xdfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst)) 
               | (((0U < vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[5U]) 
                   & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[5U] 
                      <= ((IData)(1U) + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))) 
                  << 5U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = ((0xdfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
               | (0x20U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data) 
                           | (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst))));
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = (0xdfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = (0xffff00ffffffffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size);
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = (0xdfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = (0xdfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok));
    }
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding 
        = ((0xdfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding)) 
           | (0x20U & ((~ ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__r_outstanding_limit) 
                           >> 5U)) << 5U)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request 
        = ((0xdfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request)) 
           | (0x20U & (((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid) 
                        & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
                       & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding))));
    if ((0x40U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid))) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = ((0xff00ffffffffffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size) 
               | ((QData)((IData)((0xffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[6U] 
                                             <= ((IData)(1U) 
                                                 + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))
                                             ? (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[6U] 
                                                - (IData)(1U))
                                             : (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats))))) 
                  << 0x30U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = ((0xbfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data)) 
               | (((0x1fffU & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[2U] 
                               >> 0xeU)) >= (0x1fffU 
                                             & ((IData)(1U) 
                                                + (0xffU 
                                                   & (IData)(
                                                             (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
                                                              >> 0x30U)))))) 
                  << 6U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = ((0xbfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst)) 
               | (((0U < vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[6U]) 
                   & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[6U] 
                      <= ((IData)(1U) + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))) 
                  << 6U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = ((0xbfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
               | (0x40U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data) 
                           | (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst))));
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = (0xbfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = (0xff00ffffffffffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size);
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = (0xbfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = (0xbfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok));
    }
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding 
        = ((0xbfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding)) 
           | (0x40U & ((~ ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__r_outstanding_limit) 
                           >> 6U)) << 6U)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request 
        = ((0xbfU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request)) 
           | (0x40U & (((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid) 
                        & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
                       & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding))));
    if ((0x80U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid))) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = ((0xffffffffffffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size) 
               | ((QData)((IData)((0xffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[7U] 
                                             <= ((IData)(1U) 
                                                 + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))
                                             ? (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[7U] 
                                                - (IData)(1U))
                                             : (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats))))) 
                  << 0x38U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = ((0x7fU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data)) 
               | (((0x1fffU & ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[3U] 
                                << 5U) | (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_wr_drain_data_avail[2U] 
                                          >> 0x1bU))) 
                   >= (0x1fffU & ((IData)(1U) + (0xffU 
                                                 & (IData)(
                                                           (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
                                                            >> 0x38U)))))) 
                  << 7U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = ((0x7fU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst)) 
               | (((0U < vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[7U]) 
                   & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_beats[7U] 
                      <= ((IData)(1U) + (IData)(vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats)))) 
                  << 7U));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = ((0x7fU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
               | (0x80U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data) 
                           | (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst))));
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data 
            = (0x7fU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_has_data));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size 
            = (0xffffffffffffffULL & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_transfer_size);
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst 
            = (0x7fU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_final_burst));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok 
            = (0x7fU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok));
    }
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding 
        = ((0x7fU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding)) 
           | (0x80U & ((~ ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__r_outstanding_limit) 
                           >> 7U)) << 7U)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request 
        = ((0x7fU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request)) 
           | (0x80U & (((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__sched_wr_valid) 
                        & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_data_ok)) 
                       & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_no_outstanding))));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__request 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_requests_gated 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_other_requests 
        = ((~ ((IData)(1U) << (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__r_pending_client))) 
           & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_requests_unmasked 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_any_requests 
        = (0U != (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_requests_masked 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request) 
           & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_curr_mask_decode));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__requests_unmasked 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_requests_unmasked;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__requests_masked 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_requests_masked;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_any_masked_requests 
        = (0U != (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_requests_masked));
    if (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_any_masked_requests) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 1U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_requests_masked;
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__any_masked_requests = 0U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests 
            = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_arb_request;
    }
    __Vtableidx34 = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__w_priority_requests;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__winner 
        = Vtop__ConstPool__TABLE_h256e5f3b_0[__Vtableidx34];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__winner_valid 
        = Vtop__ConstPool__TABLE_hb32d1eae_0[__Vtableidx34];
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_winner 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__winner;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_winner_valid 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__winner_valid;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_should_grant 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__u_priority_encoder__DOT__winner_valid) 
           & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_any_requests) 
              & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_can_grant)));
    if (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_should_grant) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_next_grant_valid = 1U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_next_grant_id = 0U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_next_grant 
            = ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_next_grant) 
               | (0xffU & ((IData)(1U) << (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_winner))));
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_next_grant_id 
            = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_winner;
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_next_grant_valid = 0U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_next_grant = 0U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__gen_multi_channel__DOT__u_arbiter__DOT__w_next_grant_id = 0U;
    }
}
