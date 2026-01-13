// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop___024root.h"
#include "Vtop_stream_regs_pkg.h"

extern const VlUnpacked<CData/*1:0*/, 512> Vtop__ConstPool__TABLE_he32e647c_0;

VL_INLINE_OPT void Vtop___024root___nba_sequent__TOP__13(Vtop___024root* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+    Vtop___024root___nba_sequent__TOP__13\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    SData/*8:0*/ __Vtableidx1;
    __Vtableidx1 = 0;
    // Body
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_valid 
        = (1U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_sram_valid_decoded));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_wr_sram_ready 
        = (1U & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_sram_drain_decoded));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[1U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[2U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[3U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[4U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[4U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[5U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[5U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[6U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[6U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[7U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[7U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[8U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[8U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[9U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[9U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[0xaU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xaU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[0xbU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xbU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[0xcU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xcU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[0xdU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xdU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[0xeU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xeU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_sram_data[0xfU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xfU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_rd_alloc_size 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_alloc_size;
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit.axi_wr_drain_size 
        = (0xffU & (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_drain_size));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_valid 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_sram_valid_decoded) 
                 >> 1U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_wr_sram_ready 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_sram_drain_decoded) 
                 >> 1U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[1U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[2U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[3U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[4U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[4U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[5U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[5U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[6U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[6U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[7U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[7U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[8U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[8U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[9U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[9U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[0xaU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xaU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[0xbU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xbU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[0xcU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xcU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[0xdU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xdU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[0xeU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xeU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_sram_data[0xfU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xfU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_rd_alloc_size 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_alloc_size;
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit.axi_wr_drain_size 
        = (0xffU & (IData)((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_drain_size 
                            >> 8U)));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_valid 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_sram_valid_decoded) 
                 >> 2U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_wr_sram_ready 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_sram_drain_decoded) 
                 >> 2U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[1U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[2U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[3U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[4U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[4U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[5U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[5U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[6U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[6U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[7U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[7U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[8U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[8U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[9U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[9U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[0xaU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xaU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[0xbU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xbU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[0xcU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xcU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[0xdU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xdU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[0xeU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xeU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_sram_data[0xfU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xfU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_rd_alloc_size 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_alloc_size;
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit.axi_wr_drain_size 
        = (0xffU & (IData)((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_drain_size 
                            >> 0x10U)));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_valid 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_sram_valid_decoded) 
                 >> 3U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_wr_sram_ready 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_sram_drain_decoded) 
                 >> 3U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[1U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[2U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[3U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[4U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[4U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[5U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[5U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[6U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[6U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[7U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[7U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[8U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[8U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[9U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[9U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[0xaU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xaU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[0xbU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xbU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[0xcU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xcU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[0xdU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xdU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[0xeU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xeU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_sram_data[0xfU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xfU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_rd_alloc_size 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_alloc_size;
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit.axi_wr_drain_size 
        = (0xffU & (IData)((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_drain_size 
                            >> 0x18U)));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_valid 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_sram_valid_decoded) 
                 >> 4U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_sram_ready 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_sram_drain_decoded) 
                 >> 4U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[1U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[2U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[3U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[4U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[4U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[5U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[5U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[6U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[6U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[7U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[7U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[8U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[8U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[9U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[9U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[0xaU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xaU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[0xbU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xbU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[0xcU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xcU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[0xdU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xdU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[0xeU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xeU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_sram_data[0xfU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xfU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_rd_alloc_size 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_alloc_size;
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit.axi_wr_drain_size 
        = (0xffU & (IData)((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_drain_size 
                            >> 0x20U)));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_valid 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_sram_valid_decoded) 
                 >> 5U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_sram_ready 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_sram_drain_decoded) 
                 >> 5U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[1U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[2U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[3U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[4U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[4U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[5U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[5U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[6U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[6U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[7U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[7U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[8U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[8U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[9U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[9U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[0xaU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xaU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[0xbU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xbU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[0xcU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xcU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[0xdU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xdU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[0xeU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xeU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_sram_data[0xfU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xfU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_rd_alloc_size 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_alloc_size;
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit.axi_wr_drain_size 
        = (0xffU & (IData)((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_drain_size 
                            >> 0x28U)));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_valid 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_sram_valid_decoded) 
                 >> 6U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_sram_ready 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_sram_drain_decoded) 
                 >> 6U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[1U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[2U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[3U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[4U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[4U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[5U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[5U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[6U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[6U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[7U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[7U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[8U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[8U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[9U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[9U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[0xaU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xaU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[0xbU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xbU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[0xcU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xcU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[0xdU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xdU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[0xeU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xeU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_sram_data[0xfU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xfU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_rd_alloc_size 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_alloc_size;
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit.axi_wr_drain_size 
        = (0xffU & (IData)((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_drain_size 
                            >> 0x30U)));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_valid 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_rd_sram_valid_decoded) 
                 >> 7U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_sram_ready 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__axi_wr_sram_drain_decoded) 
                 >> 7U));
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[0U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[1U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[1U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[2U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[2U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[3U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[3U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[4U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[4U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[5U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[5U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[6U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[6U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[7U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[7U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[8U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[8U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[9U] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[9U];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[0xaU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xaU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[0xbU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xbU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[0xcU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xcU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[0xdU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xdU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[0xeU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xeU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_sram_data[0xfU] 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_sram_data[0xfU];
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_rd_alloc_size 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__axi_rd_alloc_size;
    vlSymsp->TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit.axi_wr_drain_size 
        = (0xffU & (IData)((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__w_drain_size 
                            >> 0x38U)));
    vlSelfRef.stream_top_ch8__DOT__peakrdl_cmd_pwrite 
        = vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_pwrite;
    vlSelfRef.stream_top_ch8__DOT__apb_cmd_pwdata = vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_pwdata;
    vlSelfRef.stream_top_ch8__DOT__apb_cmd_pwrite = vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_pwrite;
    vlSelfRef.stream_top_ch8__DOT__apb_cmd_paddr = vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_paddr;
    vlSelfRef.stream_top_ch8__DOT__apb_rsp_ready = vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__resp_skid_buffer_inst__DOT__wr_ready;
    vlSelfRef.stream_top_ch8__DOT__apb_cmd_valid = vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__cmd_skid_buffer_inst__DOT__rd_valid;
    vlSelfRef.stream_top_ch8__DOT__regblk_req_is_wr 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr;
    vlSelfRef.stream_top_ch8__DOT__regblk_addr = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__cmd_ready)
                                                   ? (IData)(vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_paddr)
                                                   : (IData)(vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__r_cmd_paddr));
    vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__cmd_pwrite 
        = vlSelfRef.stream_top_ch8__DOT__peakrdl_cmd_pwrite;
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_pwdata 
        = vlSelfRef.stream_top_ch8__DOT__apb_cmd_pwdata;
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_pwrite 
        = vlSelfRef.stream_top_ch8__DOT__apb_cmd_pwrite;
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_paddr 
        = vlSelfRef.stream_top_ch8__DOT__apb_cmd_paddr;
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__addr_hit_m0 
        = (0U == (0x3fU & ((IData)(vlSelfRef.stream_top_ch8__DOT__apb_cmd_paddr) 
                           >> 6U)));
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__addr_hit_perf 
        = (IData)(((0U == (0xf00U & (IData)(vlSelfRef.stream_top_ch8__DOT__apb_cmd_paddr))) 
                   & (0U != (3U & ((IData)(vlSelfRef.stream_top_ch8__DOT__apb_cmd_paddr) 
                                   >> 6U)))));
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__addr_hit_m1 
        = (1U & ((~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__addr_hit_m0)) 
                 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__addr_hit_perf))));
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_rsp_ready 
        = vlSelfRef.stream_top_ch8__DOT__apb_rsp_ready;
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_valid 
        = vlSelfRef.stream_top_ch8__DOT__apb_cmd_valid;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__s_cpuif_req_is_wr 
        = vlSelfRef.stream_top_ch8__DOT__regblk_req_is_wr;
    vlSelfRef.debug_regblk_addr = vlSelfRef.stream_top_ch8__DOT__regblk_addr;
    vlSelfRef.stream_top_ch8__DOT__debug_regblk_addr 
        = vlSelfRef.stream_top_ch8__DOT__regblk_addr;
    vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__regblk_addr 
        = vlSelfRef.stream_top_ch8__DOT__regblk_addr;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr 
        = (0x3ffU & (IData)(vlSelfRef.stream_top_ch8__DOT__regblk_addr));
    if (vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__addr_hit_m0) {
        vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_valid 
            = vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__cmd_skid_buffer_inst__DOT__rd_valid;
        vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_ready 
            = vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_ready;
    } else {
        vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_valid = 0U;
        vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_ready 
            = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__addr_hit_perf)
                ? (IData)(vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__perf_rsp_ready_internal)
                : (IData)(vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__cmd_ready));
    }
    vlSelfRef.stream_top_ch8__DOT__peakrdl_cmd_valid 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__cmd_skid_buffer_inst__DOT__rd_valid) 
           & (IData)(vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__addr_hit_m1));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__s_cpuif_addr 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr;
    vlSelfRef.stream_top_ch8__DOT__u_apbtodescr__DOT__apb_cmd_valid 
        = vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_valid;
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__m0_cmd_valid 
        = vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_valid;
    vlSelfRef.debug_apb_cmd_ready = vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_ready;
    vlSelfRef.stream_top_ch8__DOT__debug_apb_cmd_ready 
        = vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_ready;
    vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__cmd_skid_buffer_inst__DOT__w_rd_xfer 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_ready) 
           & (IData)(vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__cmd_skid_buffer_inst__DOT__rd_valid));
    vlSelfRef.stream_top_ch8__DOT__apb_cmd_ready = vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_ready;
    vlSelfRef.stream_top_ch8__DOT__perf_fifo_rd = ((IData)(vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__cmd_skid_buffer_inst__DOT__rd_valid) 
                                                   & ((IData)(vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__s_cmd_ready) 
                                                      & ((IData)(vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__addr_hit_perf) 
                                                         & ((~ (IData)(vlSelfRef.stream_top_ch8__DOT__kickoff_cmd_pwrite)) 
                                                            & (0x44U 
                                                               == 
                                                               (0xffU 
                                                                & vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__cmd_skid_buffer_inst__DOT__r_data[1U]))))));
    vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__cmd_valid 
        = vlSelfRef.stream_top_ch8__DOT__peakrdl_cmd_valid;
    vlSelfRef.debug_peakrdl_cmd_valid = vlSelfRef.stream_top_ch8__DOT__peakrdl_cmd_valid;
    vlSelfRef.stream_top_ch8__DOT__debug_peakrdl_cmd_valid 
        = vlSelfRef.stream_top_ch8__DOT__peakrdl_cmd_valid;
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__m1_cmd_valid 
        = vlSelfRef.stream_top_ch8__DOT__peakrdl_cmd_valid;
    vlSelfRef.stream_top_ch8__DOT__regblk_req = ((1U 
                                                  == (IData)(vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__cmd_state)) 
                                                 | ((IData)(vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__cmd_ready) 
                                                    & (IData)(vlSelfRef.stream_top_ch8__DOT__peakrdl_cmd_valid)));
    vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__cmd_ready 
        = vlSelfRef.stream_top_ch8__DOT__apb_cmd_ready;
    vlSelfRef.stream_top_ch8__DOT__u_cmdrsp_router__DOT__perf_fifo_rd 
        = vlSelfRef.stream_top_ch8__DOT__perf_fifo_rd;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__perf_fifo_rd 
        = vlSelfRef.stream_top_ch8__DOT__perf_fifo_rd;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__s_cpuif_req 
        = vlSelfRef.stream_top_ch8__DOT__regblk_req;
    vlSelfRef.debug_regblk_req = vlSelfRef.stream_top_ch8__DOT__regblk_req;
    vlSelfRef.stream_top_ch8__DOT__debug_regblk_req 
        = vlSelfRef.stream_top_ch8__DOT__regblk_req;
    vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__regblk_req 
        = vlSelfRef.stream_top_ch8__DOT__regblk_req;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req 
        = vlSelfRef.stream_top_ch8__DOT__regblk_req;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked 
        = ((~ (((~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)) 
                & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_stall_rd)) 
               | ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_stall_wr) 
                  & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))) 
           & (IData)(vlSelfRef.stream_top_ch8__DOT__regblk_req));
    vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__cmd_skid_buffer_inst__DOT__rd_ready 
        = vlSelfRef.stream_top_ch8__DOT__g_apb_passthrough__DOT__u_apb_slave__DOT__cmd_ready;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__perf_fifo_rd 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__perf_fifo_rd;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked;
    vlSelfRef.stream_top_ch8__DOT__regblk_wr_ack = 
        ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
         & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_done 
        = ((~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)) 
           & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__GLOBAL_CTRL 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x100U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__GLOBAL_STATUS 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x104U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__VERSION 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x108U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CHANNEL_ENABLE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x120U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CHANNEL_RESET 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x124U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CHANNEL_IDLE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x140U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DESC_ENGINE_IDLE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x144U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__SCHEDULER_IDLE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x148U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CH_STATE[0U].__PVT__STATE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x150U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CH_STATE[1U].__PVT__STATE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x154U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CH_STATE[2U].__PVT__STATE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x158U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CH_STATE[3U].__PVT__STATE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x15cU == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CH_STATE[4U].__PVT__STATE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x160U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CH_STATE[5U].__PVT__STATE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x164U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CH_STATE[6U].__PVT__STATE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x168U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__CH_STATE[7U].__PVT__STATE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x16cU == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__SCHED_TIMEOUT_CYCLES 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x200U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__SCHED_CONFIG 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x204U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DESCENG_CONFIG 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x220U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DESCENG_ADDR0_BASE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x224U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DESCENG_ADDR0_LIMIT 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x228U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DESCENG_ADDR1_BASE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x22cU == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DESCENG_ADDR1_LIMIT 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x230U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DAXMON_ENABLE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x240U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DAXMON_TIMEOUT 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x244U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DAXMON_LATENCY_THRESH 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x248U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DAXMON_PKT_MASK 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x24cU == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DAXMON_ERR_CFG 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x250U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DAXMON_MASK1 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x254U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DAXMON_MASK2 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x258U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__DAXMON_MASK3 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x25cU == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__RDMON_ENABLE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x260U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__RDMON_TIMEOUT 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x264U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__RDMON_LATENCY_THRESH 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x268U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__RDMON_PKT_MASK 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x26cU == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__RDMON_ERR_CFG 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x270U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__RDMON_MASK1 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x274U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__RDMON_MASK2 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x278U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__RDMON_MASK3 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x27cU == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__WRMON_ENABLE 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x280U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__WRMON_TIMEOUT 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x284U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__WRMON_LATENCY_THRESH 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x288U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__WRMON_PKT_MASK 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x28cU == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__WRMON_ERR_CFG 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x290U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__WRMON_MASK1 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x294U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__WRMON_MASK2 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x298U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__WRMON_MASK3 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x29cU == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__AXI_XFER_CONFIG 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x2a0U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb.__PVT__PERF_CONFIG 
        = ((IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_req_masked) 
           & (0x2b0U == (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_addr)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__u_perf_fifo__DOT__rd_ready 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__perf_fifo_rd;
    vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__regblk_wr_ack 
        = vlSelfRef.stream_top_ch8__DOT__regblk_wr_ack;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__s_cpuif_wr_ack 
        = vlSelfRef.stream_top_ch8__DOT__regblk_wr_ack;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_wr_ack 
        = vlSelfRef.stream_top_ch8__DOT__regblk_wr_ack;
    vlSelfRef.debug_regblk_rd_ack = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_done;
    vlSelfRef.stream_top_ch8__DOT__debug_regblk_rd_ack 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_done;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__s_cpuif_rd_ack 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_done;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__cpuif_rd_ack 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_done;
    vlSelfRef.stream_top_ch8__DOT__regblk_rd_ack = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_done;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk2__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__GLOBAL_CTRL.__PVT__GLOBAL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk2__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__GLOBAL_CTRL & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk2__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__GLOBAL_CTRL.__PVT__GLOBAL_EN
                      .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                     | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk2__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__GLOBAL_CTRL.__PVT__GLOBAL_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk2__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__GLOBAL_CTRL.__PVT__GLOBAL_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk2__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk3__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__GLOBAL_CTRL.__PVT__GLOBAL_RST.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk3__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__GLOBAL_CTRL & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk3__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__GLOBAL_CTRL.__PVT__GLOBAL_RST
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 1U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 1U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk3__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__GLOBAL_CTRL.__PVT__GLOBAL_RST.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk3__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__GLOBAL_CTRL.__PVT__GLOBAL_RST.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk3__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk4__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__CHANNEL_ENABLE.__PVT__CH_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk4__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__CHANNEL_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk4__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__CHANNEL_ENABLE.__PVT__CH_EN
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk4__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__CHANNEL_ENABLE.__PVT__CH_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk4__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__CHANNEL_ENABLE.__PVT__CH_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk4__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk5__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__CHANNEL_RESET.__PVT__CH_RST.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk5__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__CHANNEL_RESET & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk5__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__CHANNEL_RESET.__PVT__CH_RST
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk5__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__CHANNEL_RESET.__PVT__CH_RST.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk5__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__CHANNEL_RESET.__PVT__CH_RST.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk5__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk6__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__SCHED_TIMEOUT_CYCLES.__PVT__TIMEOUT_CYCLES
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk6__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__SCHED_TIMEOUT_CYCLES & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk6__DOT__next_c 
            = (0xffffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                           .__PVT__SCHED_TIMEOUT_CYCLES
                           .__PVT__TIMEOUT_CYCLES.__PVT__value 
                           & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                          | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                             & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk6__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_TIMEOUT_CYCLES.__PVT__TIMEOUT_CYCLES.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk6__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_TIMEOUT_CYCLES.__PVT__TIMEOUT_CYCLES.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk6__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk7__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__SCHED_CONFIG.__PVT__SCHED_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk7__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__SCHED_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk7__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__SCHED_CONFIG.__PVT__SCHED_EN
                      .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                     | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk7__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_CONFIG.__PVT__SCHED_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk7__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_CONFIG.__PVT__SCHED_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk7__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk8__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__SCHED_CONFIG.__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk8__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__SCHED_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk8__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__SCHED_CONFIG.__PVT__TIMEOUT_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 1U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 1U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk8__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_CONFIG.__PVT__TIMEOUT_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk8__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_CONFIG.__PVT__TIMEOUT_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk8__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk9__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__SCHED_CONFIG.__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk9__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__SCHED_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk9__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__SCHED_CONFIG.__PVT__ERR_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 2U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 2U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk9__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_CONFIG.__PVT__ERR_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk9__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_CONFIG.__PVT__ERR_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk9__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk10__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__SCHED_CONFIG.__PVT__COMPL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk10__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__SCHED_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk10__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__SCHED_CONFIG.__PVT__COMPL_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 3U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 3U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk10__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_CONFIG.__PVT__COMPL_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk10__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_CONFIG.__PVT__COMPL_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk10__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk11__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__SCHED_CONFIG.__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk11__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__SCHED_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk11__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__SCHED_CONFIG.__PVT__PERF_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 4U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 4U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk11__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_CONFIG.__PVT__PERF_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk11__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__SCHED_CONFIG.__PVT__PERF_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk11__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk12__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DESCENG_CONFIG.__PVT__DESCENG_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk12__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DESCENG_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk12__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__DESCENG_CONFIG.__PVT__DESCENG_EN
                      .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                     | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk12__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_CONFIG.__PVT__DESCENG_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk12__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_CONFIG.__PVT__DESCENG_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk12__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk13__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DESCENG_CONFIG.__PVT__PREFETCH_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk13__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DESCENG_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk13__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__DESCENG_CONFIG.__PVT__PREFETCH_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 1U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 1U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk13__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_CONFIG.__PVT__PREFETCH_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk13__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_CONFIG.__PVT__PREFETCH_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk13__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk14__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DESCENG_CONFIG.__PVT__FIFO_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk14__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DESCENG_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk14__DOT__next_c 
            = (0xfU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__DESCENG_CONFIG.__PVT__FIFO_THRESH
                        .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                            >> 2U))) 
                       | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                          >> 2U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk14__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_CONFIG.__PVT__FIFO_THRESH.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk14__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_CONFIG.__PVT__FIFO_THRESH.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk14__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk15__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DESCENG_ADDR0_BASE.__PVT__ADDR0_BASE
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk15__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DESCENG_ADDR0_BASE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk15__DOT__next_c 
            = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                .__PVT__DESCENG_ADDR0_BASE.__PVT__ADDR0_BASE
                .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
               | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                  & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk15__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_ADDR0_BASE.__PVT__ADDR0_BASE.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk15__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_ADDR0_BASE.__PVT__ADDR0_BASE.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk15__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk16__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DESCENG_ADDR0_LIMIT.__PVT__ADDR0_LIMIT
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk16__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DESCENG_ADDR0_LIMIT & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk16__DOT__next_c 
            = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                .__PVT__DESCENG_ADDR0_LIMIT.__PVT__ADDR0_LIMIT
                .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
               | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                  & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk16__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_ADDR0_LIMIT.__PVT__ADDR0_LIMIT.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk16__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_ADDR0_LIMIT.__PVT__ADDR0_LIMIT.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk16__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk17__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DESCENG_ADDR1_BASE.__PVT__ADDR1_BASE
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk17__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DESCENG_ADDR1_BASE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk17__DOT__next_c 
            = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                .__PVT__DESCENG_ADDR1_BASE.__PVT__ADDR1_BASE
                .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
               | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                  & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk17__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_ADDR1_BASE.__PVT__ADDR1_BASE.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk17__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_ADDR1_BASE.__PVT__ADDR1_BASE.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk17__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk18__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DESCENG_ADDR1_LIMIT.__PVT__ADDR1_LIMIT
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk18__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DESCENG_ADDR1_LIMIT & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk18__DOT__next_c 
            = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                .__PVT__DESCENG_ADDR1_LIMIT.__PVT__ADDR1_LIMIT
                .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
               | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                  & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk18__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_ADDR1_LIMIT.__PVT__ADDR1_LIMIT.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk18__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DESCENG_ADDR1_LIMIT.__PVT__ADDR1_LIMIT.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk18__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk19__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_ENABLE.__PVT__MON_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk19__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk19__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__DAXMON_ENABLE.__PVT__MON_EN
                      .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                     | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk19__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ENABLE.__PVT__MON_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk19__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ENABLE.__PVT__MON_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk19__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk20__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_ENABLE.__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk20__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk20__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__DAXMON_ENABLE.__PVT__ERR_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 1U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 1U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk20__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ENABLE.__PVT__ERR_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk20__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ENABLE.__PVT__ERR_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk20__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk21__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_ENABLE.__PVT__COMPL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk21__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk21__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__DAXMON_ENABLE.__PVT__COMPL_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 2U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 2U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk21__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ENABLE.__PVT__COMPL_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk21__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ENABLE.__PVT__COMPL_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk21__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk22__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_ENABLE.__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk22__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk22__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__DAXMON_ENABLE.__PVT__TIMEOUT_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 3U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 3U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk22__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ENABLE.__PVT__TIMEOUT_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk22__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ENABLE.__PVT__TIMEOUT_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk22__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk23__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_ENABLE.__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk23__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk23__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__DAXMON_ENABLE.__PVT__PERF_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 4U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 4U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk23__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ENABLE.__PVT__PERF_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk23__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ENABLE.__PVT__PERF_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk23__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk24__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_TIMEOUT.__PVT__TIMEOUT_CYCLES
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk24__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_TIMEOUT & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk24__DOT__next_c 
            = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                .__PVT__DAXMON_TIMEOUT.__PVT__TIMEOUT_CYCLES
                .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
               | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                  & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk24__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_TIMEOUT.__PVT__TIMEOUT_CYCLES.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk24__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_TIMEOUT.__PVT__TIMEOUT_CYCLES.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk24__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk25__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_LATENCY_THRESH.__PVT__LATENCY_THRESH
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk25__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_LATENCY_THRESH & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk25__DOT__next_c 
            = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                .__PVT__DAXMON_LATENCY_THRESH.__PVT__LATENCY_THRESH
                .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
               | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                  & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk25__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_LATENCY_THRESH.__PVT__LATENCY_THRESH.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk25__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_LATENCY_THRESH.__PVT__LATENCY_THRESH.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk25__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk26__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_PKT_MASK.__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk26__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_PKT_MASK & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk26__DOT__next_c 
            = (0xffffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                           .__PVT__DAXMON_PKT_MASK.__PVT__PKT_MASK
                           .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                          | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                             & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk26__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_PKT_MASK.__PVT__PKT_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk26__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_PKT_MASK.__PVT__PKT_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk26__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk27__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_ERR_CFG.__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk27__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_ERR_CFG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk27__DOT__next_c 
            = (0xfU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__DAXMON_ERR_CFG.__PVT__ERR_SELECT
                        .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                       | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                          & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk27__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ERR_CFG.__PVT__ERR_SELECT.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk27__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ERR_CFG.__PVT__ERR_SELECT.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk27__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk28__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_ERR_CFG.__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk28__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_ERR_CFG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk28__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_ERR_CFG.__PVT__ERR_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk28__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ERR_CFG.__PVT__ERR_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk28__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_ERR_CFG.__PVT__ERR_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk28__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk29__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_MASK1.__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk29__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_MASK1 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk29__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_MASK1.__PVT__TIMEOUT_MASK
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk29__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK1.__PVT__TIMEOUT_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk29__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK1.__PVT__TIMEOUT_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk29__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk30__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_MASK1.__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk30__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_MASK1 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk30__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_MASK1.__PVT__COMPL_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk30__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK1.__PVT__COMPL_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk30__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK1.__PVT__COMPL_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk30__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk31__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_MASK2.__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk31__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_MASK2 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk31__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_MASK2.__PVT__THRESH_MASK
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk31__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK2.__PVT__THRESH_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk31__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK2.__PVT__THRESH_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk31__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk32__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_MASK2.__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk32__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_MASK2 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk32__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_MASK2.__PVT__PERF_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk32__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK2.__PVT__PERF_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk32__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK2.__PVT__PERF_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk32__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk33__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_MASK3.__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk33__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_MASK3 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk33__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_MASK3.__PVT__ADDR_MASK
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk33__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK3.__PVT__ADDR_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk33__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK3.__PVT__ADDR_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk33__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk34__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__DAXMON_MASK3.__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk34__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__DAXMON_MASK3 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk34__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_MASK3.__PVT__DEBUG_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk34__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK3.__PVT__DEBUG_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk34__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__DAXMON_MASK3.__PVT__DEBUG_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk34__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk35__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_ENABLE.__PVT__MON_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk35__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk35__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__RDMON_ENABLE.__PVT__MON_EN
                      .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                     | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk35__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ENABLE.__PVT__MON_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk35__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ENABLE.__PVT__MON_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk35__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk36__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_ENABLE.__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk36__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk36__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__RDMON_ENABLE.__PVT__ERR_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 1U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 1U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk36__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ENABLE.__PVT__ERR_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk36__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ENABLE.__PVT__ERR_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk36__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk37__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_ENABLE.__PVT__COMPL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk37__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk37__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__RDMON_ENABLE.__PVT__COMPL_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 2U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 2U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk37__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ENABLE.__PVT__COMPL_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk37__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ENABLE.__PVT__COMPL_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk37__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk38__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_ENABLE.__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk38__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk38__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__RDMON_ENABLE.__PVT__TIMEOUT_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 3U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 3U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk38__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ENABLE.__PVT__TIMEOUT_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk38__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ENABLE.__PVT__TIMEOUT_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk38__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk39__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_ENABLE.__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk39__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk39__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__RDMON_ENABLE.__PVT__PERF_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 4U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 4U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk39__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ENABLE.__PVT__PERF_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk39__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ENABLE.__PVT__PERF_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk39__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk40__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_TIMEOUT.__PVT__TIMEOUT_CYCLES
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk40__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_TIMEOUT & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk40__DOT__next_c 
            = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                .__PVT__RDMON_TIMEOUT.__PVT__TIMEOUT_CYCLES
                .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
               | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                  & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk40__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_TIMEOUT.__PVT__TIMEOUT_CYCLES.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk40__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_TIMEOUT.__PVT__TIMEOUT_CYCLES.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk40__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk41__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_LATENCY_THRESH.__PVT__LATENCY_THRESH
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk41__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_LATENCY_THRESH & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk41__DOT__next_c 
            = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                .__PVT__RDMON_LATENCY_THRESH.__PVT__LATENCY_THRESH
                .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
               | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                  & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk41__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_LATENCY_THRESH.__PVT__LATENCY_THRESH.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk41__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_LATENCY_THRESH.__PVT__LATENCY_THRESH.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk41__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk42__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_PKT_MASK.__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk42__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_PKT_MASK & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk42__DOT__next_c 
            = (0xffffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                           .__PVT__RDMON_PKT_MASK.__PVT__PKT_MASK
                           .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                          | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                             & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk42__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_PKT_MASK.__PVT__PKT_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk42__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_PKT_MASK.__PVT__PKT_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk42__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk43__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_ERR_CFG.__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk43__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_ERR_CFG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk43__DOT__next_c 
            = (0xfU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__RDMON_ERR_CFG.__PVT__ERR_SELECT
                        .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                       | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                          & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk43__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ERR_CFG.__PVT__ERR_SELECT.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk43__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ERR_CFG.__PVT__ERR_SELECT.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk43__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk44__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_ERR_CFG.__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk44__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_ERR_CFG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk44__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_ERR_CFG.__PVT__ERR_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk44__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ERR_CFG.__PVT__ERR_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk44__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_ERR_CFG.__PVT__ERR_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk44__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk45__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_MASK1.__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk45__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_MASK1 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk45__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_MASK1.__PVT__TIMEOUT_MASK
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk45__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK1.__PVT__TIMEOUT_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk45__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK1.__PVT__TIMEOUT_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk45__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk46__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_MASK1.__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk46__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_MASK1 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk46__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_MASK1.__PVT__COMPL_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk46__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK1.__PVT__COMPL_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk46__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK1.__PVT__COMPL_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk46__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk47__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_MASK2.__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk47__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_MASK2 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk47__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_MASK2.__PVT__THRESH_MASK
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk47__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK2.__PVT__THRESH_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk47__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK2.__PVT__THRESH_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk47__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk48__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_MASK2.__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk48__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_MASK2 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk48__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_MASK2.__PVT__PERF_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk48__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK2.__PVT__PERF_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk48__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK2.__PVT__PERF_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk48__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk49__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_MASK3.__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk49__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_MASK3 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk49__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_MASK3.__PVT__ADDR_MASK
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk49__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK3.__PVT__ADDR_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk49__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK3.__PVT__ADDR_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk49__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk50__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__RDMON_MASK3.__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk50__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__RDMON_MASK3 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk50__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_MASK3.__PVT__DEBUG_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk50__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK3.__PVT__DEBUG_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk50__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__RDMON_MASK3.__PVT__DEBUG_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk50__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk51__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_ENABLE.__PVT__MON_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk51__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk51__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__WRMON_ENABLE.__PVT__MON_EN
                      .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                     | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk51__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ENABLE.__PVT__MON_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk51__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ENABLE.__PVT__MON_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk51__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk52__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_ENABLE.__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk52__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk52__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__WRMON_ENABLE.__PVT__ERR_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 1U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 1U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk52__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ENABLE.__PVT__ERR_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk52__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ENABLE.__PVT__ERR_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk52__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk53__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_ENABLE.__PVT__COMPL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk53__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk53__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__WRMON_ENABLE.__PVT__COMPL_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 2U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 2U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk53__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ENABLE.__PVT__COMPL_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk53__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ENABLE.__PVT__COMPL_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk53__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk54__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_ENABLE.__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk54__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk54__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__WRMON_ENABLE.__PVT__TIMEOUT_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 3U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 3U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk54__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ENABLE.__PVT__TIMEOUT_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk54__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ENABLE.__PVT__TIMEOUT_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk54__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk55__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_ENABLE.__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk55__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_ENABLE & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk55__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__WRMON_ENABLE.__PVT__PERF_EN
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 4U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 4U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk55__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ENABLE.__PVT__PERF_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk55__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ENABLE.__PVT__PERF_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk55__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk56__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_TIMEOUT.__PVT__TIMEOUT_CYCLES
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk56__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_TIMEOUT & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk56__DOT__next_c 
            = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                .__PVT__WRMON_TIMEOUT.__PVT__TIMEOUT_CYCLES
                .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
               | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                  & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk56__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_TIMEOUT.__PVT__TIMEOUT_CYCLES.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk56__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_TIMEOUT.__PVT__TIMEOUT_CYCLES.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk56__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk57__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_LATENCY_THRESH.__PVT__LATENCY_THRESH
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk57__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_LATENCY_THRESH & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk57__DOT__next_c 
            = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                .__PVT__WRMON_LATENCY_THRESH.__PVT__LATENCY_THRESH
                .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
               | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                  & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk57__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_LATENCY_THRESH.__PVT__LATENCY_THRESH.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk57__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_LATENCY_THRESH.__PVT__LATENCY_THRESH.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk57__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk58__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_PKT_MASK.__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk58__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_PKT_MASK & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk58__DOT__next_c 
            = (0xffffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                           .__PVT__WRMON_PKT_MASK.__PVT__PKT_MASK
                           .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                          | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                             & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk58__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_PKT_MASK.__PVT__PKT_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk58__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_PKT_MASK.__PVT__PKT_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk58__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk59__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_ERR_CFG.__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk59__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_ERR_CFG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk59__DOT__next_c 
            = (0xfU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__WRMON_ERR_CFG.__PVT__ERR_SELECT
                        .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                       | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                          & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk59__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ERR_CFG.__PVT__ERR_SELECT.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk59__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ERR_CFG.__PVT__ERR_SELECT.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk59__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk60__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_ERR_CFG.__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk60__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_ERR_CFG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk60__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_ERR_CFG.__PVT__ERR_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk60__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ERR_CFG.__PVT__ERR_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk60__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_ERR_CFG.__PVT__ERR_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk60__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk61__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_MASK1.__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk61__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_MASK1 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk61__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_MASK1.__PVT__TIMEOUT_MASK
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk61__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK1.__PVT__TIMEOUT_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk61__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK1.__PVT__TIMEOUT_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk61__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk62__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_MASK1.__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk62__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_MASK1 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk62__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_MASK1.__PVT__COMPL_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk62__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK1.__PVT__COMPL_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk62__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK1.__PVT__COMPL_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk62__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk63__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_MASK2.__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk63__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_MASK2 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk63__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_MASK2.__PVT__THRESH_MASK
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk63__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK2.__PVT__THRESH_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk63__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK2.__PVT__THRESH_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk63__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk64__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_MASK2.__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk64__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_MASK2 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk64__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_MASK2.__PVT__PERF_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk64__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK2.__PVT__PERF_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk64__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK2.__PVT__PERF_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk64__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk65__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_MASK3.__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk65__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_MASK3 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk65__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_MASK3.__PVT__ADDR_MASK
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk65__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK3.__PVT__ADDR_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk65__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK3.__PVT__ADDR_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk65__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk66__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__WRMON_MASK3.__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk66__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__WRMON_MASK3 & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk66__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_MASK3.__PVT__DEBUG_MASK
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk66__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK3.__PVT__DEBUG_MASK.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk66__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__WRMON_MASK3.__PVT__DEBUG_MASK.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk66__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk67__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__AXI_XFER_CONFIG.__PVT__RD_XFER_BEATS
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk67__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__AXI_XFER_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk67__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__AXI_XFER_CONFIG.__PVT__RD_XFER_BEATS
                         .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                        | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                           & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk67__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__AXI_XFER_CONFIG.__PVT__RD_XFER_BEATS.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk67__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__AXI_XFER_CONFIG.__PVT__RD_XFER_BEATS.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk67__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk68__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__AXI_XFER_CONFIG.__PVT__WR_XFER_BEATS
        .__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk68__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__AXI_XFER_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk68__DOT__next_c 
            = (0xffU & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__AXI_XFER_CONFIG.__PVT__WR_XFER_BEATS
                         .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                             >> 8U))) 
                        | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                            & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                           >> 8U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk68__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__AXI_XFER_CONFIG.__PVT__WR_XFER_BEATS.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk68__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__AXI_XFER_CONFIG.__PVT__WR_XFER_BEATS.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk68__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk69__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__PERF_CONFIG.__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk69__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__PERF_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk69__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__PERF_CONFIG.__PVT__PERF_EN
                      .__PVT__value & (~ vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)) 
                     | (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk69__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__PERF_CONFIG.__PVT__PERF_EN.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk69__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__PERF_CONFIG.__PVT__PERF_EN.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk69__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk70__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__PERF_CONFIG.__PVT__PERF_MODE.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk70__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__PERF_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk70__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__PERF_CONFIG.__PVT__PERF_MODE
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 1U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 1U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk70__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__PERF_CONFIG.__PVT__PERF_MODE.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk70__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__PERF_CONFIG.__PVT__PERF_MODE.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk70__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk71__DOT__next_c 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
        .__PVT__PERF_CONFIG.__PVT__PERF_CLEAR.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk71__DOT__load_next_c = 0U;
    if ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
         .__PVT__PERF_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) {
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk71__DOT__next_c 
            = (1U & ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__PERF_CONFIG.__PVT__PERF_CLEAR
                      .__PVT__value & (~ (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
                                          >> 2U))) 
                     | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_data 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten) 
                        >> 2U)));
        vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk71__DOT__load_next_c = 1U;
    }
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__PERF_CONFIG.__PVT__PERF_CLEAR.__PVT__next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk71__DOT__next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_combo.__PVT__PERF_CONFIG.__PVT__PERF_CLEAR.__PVT__load_next 
        = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__unnamedblk71__DOT__load_next_c;
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[2U] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [2U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                      .__PVT__VERSION & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                      ? 0x5aU : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[2U] 
        = ((0xff00ffffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [2U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                       .__PVT__VERSION & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                       ? 8U : 0U) << 0x10U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0U] 
        = ((0xfffffffeU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                      .__PVT__GLOBAL_CTRL & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                     & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                     .__PVT__GLOBAL_CTRL.__PVT__GLOBAL_EN
                     .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0U] 
        = ((0xfffffffdU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                       .__PVT__GLOBAL_CTRL & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                      & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                      .__PVT__GLOBAL_CTRL.__PVT__GLOBAL_RST
                      .__PVT__value) << 1U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[3U] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [3U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                      .__PVT__CHANNEL_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                      ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                     .__PVT__CHANNEL_ENABLE.__PVT__CH_EN
                     .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[4U] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [4U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                      .__PVT__CHANNEL_RESET & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                      ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                     .__PVT__CHANNEL_RESET.__PVT__CH_RST
                     .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x10U] 
        = ((0xffff0000U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x10U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__SCHED_TIMEOUT_CYCLES 
                         & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__SCHED_TIMEOUT_CYCLES
                        .__PVT__TIMEOUT_CYCLES.__PVT__value
                         : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x11U] 
        = ((0xfffffffeU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x11U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__SCHED_CONFIG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__SCHED_CONFIG.__PVT__SCHED_EN
                        .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x11U] 
        = ((0xfffffffdU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x11U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__SCHED_CONFIG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__SCHED_CONFIG.__PVT__TIMEOUT_EN
                         .__PVT__value) << 1U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x11U] 
        = ((0xfffffffbU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x11U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__SCHED_CONFIG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__SCHED_CONFIG.__PVT__ERR_EN
                         .__PVT__value) << 2U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x11U] 
        = ((0xfffffff7U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x11U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__SCHED_CONFIG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__SCHED_CONFIG.__PVT__COMPL_EN
                         .__PVT__value) << 3U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x11U] 
        = ((0xffffffefU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x11U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__SCHED_CONFIG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__SCHED_CONFIG.__PVT__PERF_EN
                         .__PVT__value) << 4U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x12U] 
        = ((0xfffffffeU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x12U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__DESCENG_CONFIG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__DESCENG_CONFIG.__PVT__DESCENG_EN
                        .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x12U] 
        = ((0xfffffffdU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x12U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__DESCENG_CONFIG & 
                          (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DESCENG_CONFIG.__PVT__PREFETCH_EN
                         .__PVT__value) << 1U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x12U] 
        = ((0xffffffc3U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x12U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__DESCENG_CONFIG & 
                          (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DESCENG_CONFIG.__PVT__FIFO_THRESH
                         .__PVT__value : 0U) << 2U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x13U] 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__DESCENG_ADDR0_BASE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
            ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
           .__PVT__DESCENG_ADDR0_BASE.__PVT__ADDR0_BASE
           .__PVT__value : 0U);
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x14U] 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__DESCENG_ADDR0_LIMIT & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
            ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
           .__PVT__DESCENG_ADDR0_LIMIT.__PVT__ADDR0_LIMIT
           .__PVT__value : 0U);
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x15U] 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__DESCENG_ADDR1_BASE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
            ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
           .__PVT__DESCENG_ADDR1_BASE.__PVT__ADDR1_BASE
           .__PVT__value : 0U);
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x16U] 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__DESCENG_ADDR1_LIMIT & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
            ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
           .__PVT__DESCENG_ADDR1_LIMIT.__PVT__ADDR1_LIMIT
           .__PVT__value : 0U);
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x17U] 
        = ((0xfffffffeU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x17U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__DAXMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__DAXMON_ENABLE.__PVT__MON_EN
                        .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x17U] 
        = ((0xfffffffdU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x17U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__DAXMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_ENABLE.__PVT__ERR_EN
                         .__PVT__value) << 1U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x17U] 
        = ((0xfffffffbU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x17U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__DAXMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_ENABLE.__PVT__COMPL_EN
                         .__PVT__value) << 2U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x17U] 
        = ((0xfffffff7U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x17U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__DAXMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_ENABLE.__PVT__TIMEOUT_EN
                         .__PVT__value) << 3U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x17U] 
        = ((0xffffffefU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x17U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__DAXMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_ENABLE.__PVT__PERF_EN
                         .__PVT__value) << 4U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x18U] 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__DAXMON_TIMEOUT & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
            ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
           .__PVT__DAXMON_TIMEOUT.__PVT__TIMEOUT_CYCLES
           .__PVT__value : 0U);
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x19U] 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__DAXMON_LATENCY_THRESH & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
            ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
           .__PVT__DAXMON_LATENCY_THRESH.__PVT__LATENCY_THRESH
           .__PVT__value : 0U);
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1aU] 
        = ((0xffff0000U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1aU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__DAXMON_PKT_MASK & 
                         (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__DAXMON_PKT_MASK.__PVT__PKT_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1bU] 
        = ((0xfffffff0U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1bU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__DAXMON_ERR_CFG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__DAXMON_ERR_CFG.__PVT__ERR_SELECT
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1bU] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1bU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__DAXMON_ERR_CFG & 
                          (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_ERR_CFG.__PVT__ERR_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1cU] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1cU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__DAXMON_MASK1 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__DAXMON_MASK1.__PVT__TIMEOUT_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1cU] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1cU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__DAXMON_MASK1 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_MASK1.__PVT__COMPL_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1dU] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1dU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__DAXMON_MASK2 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__DAXMON_MASK2.__PVT__THRESH_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1dU] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1dU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__DAXMON_MASK2 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_MASK2.__PVT__PERF_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1eU] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1eU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__DAXMON_MASK3 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__DAXMON_MASK3.__PVT__ADDR_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1eU] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1eU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__DAXMON_MASK3 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__DAXMON_MASK3.__PVT__DEBUG_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1fU] 
        = ((0xfffffffeU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1fU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__RDMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__RDMON_ENABLE.__PVT__MON_EN
                        .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1fU] 
        = ((0xfffffffdU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1fU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__RDMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_ENABLE.__PVT__ERR_EN
                         .__PVT__value) << 1U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1fU] 
        = ((0xfffffffbU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1fU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__RDMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_ENABLE.__PVT__COMPL_EN
                         .__PVT__value) << 2U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1fU] 
        = ((0xfffffff7U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1fU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__RDMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_ENABLE.__PVT__TIMEOUT_EN
                         .__PVT__value) << 3U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x1fU] 
        = ((0xffffffefU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x1fU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__RDMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_ENABLE.__PVT__PERF_EN
                         .__PVT__value) << 4U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x20U] 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__RDMON_TIMEOUT & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
            ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
           .__PVT__RDMON_TIMEOUT.__PVT__TIMEOUT_CYCLES
           .__PVT__value : 0U);
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x21U] 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__RDMON_LATENCY_THRESH & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
            ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
           .__PVT__RDMON_LATENCY_THRESH.__PVT__LATENCY_THRESH
           .__PVT__value : 0U);
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x22U] 
        = ((0xffff0000U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x22U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__RDMON_PKT_MASK & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__RDMON_PKT_MASK.__PVT__PKT_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x23U] 
        = ((0xfffffff0U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x23U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__RDMON_ERR_CFG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__RDMON_ERR_CFG.__PVT__ERR_SELECT
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x23U] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x23U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__RDMON_ERR_CFG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_ERR_CFG.__PVT__ERR_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x24U] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x24U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__RDMON_MASK1 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__RDMON_MASK1.__PVT__TIMEOUT_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x24U] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x24U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__RDMON_MASK1 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_MASK1.__PVT__COMPL_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x25U] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x25U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__RDMON_MASK2 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__RDMON_MASK2.__PVT__THRESH_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x25U] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x25U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__RDMON_MASK2 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_MASK2.__PVT__PERF_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x26U] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x26U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__RDMON_MASK3 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__RDMON_MASK3.__PVT__ADDR_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x26U] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x26U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__RDMON_MASK3 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__RDMON_MASK3.__PVT__DEBUG_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x27U] 
        = ((0xfffffffeU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x27U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__WRMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__WRMON_ENABLE.__PVT__MON_EN
                        .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x27U] 
        = ((0xfffffffdU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x27U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__WRMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_ENABLE.__PVT__ERR_EN
                         .__PVT__value) << 1U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x27U] 
        = ((0xfffffffbU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x27U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__WRMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_ENABLE.__PVT__COMPL_EN
                         .__PVT__value) << 2U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x27U] 
        = ((0xfffffff7U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x27U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__WRMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_ENABLE.__PVT__TIMEOUT_EN
                         .__PVT__value) << 3U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x27U] 
        = ((0xffffffefU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x27U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__WRMON_ENABLE & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_ENABLE.__PVT__PERF_EN
                         .__PVT__value) << 4U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x28U] 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__WRMON_TIMEOUT & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
            ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
           .__PVT__WRMON_TIMEOUT.__PVT__TIMEOUT_CYCLES
           .__PVT__value : 0U);
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x29U] 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__WRMON_LATENCY_THRESH & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
            ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
           .__PVT__WRMON_LATENCY_THRESH.__PVT__LATENCY_THRESH
           .__PVT__value : 0U);
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2aU] 
        = ((0xffff0000U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2aU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__WRMON_PKT_MASK & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__WRMON_PKT_MASK.__PVT__PKT_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2bU] 
        = ((0xfffffff0U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2bU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__WRMON_ERR_CFG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__WRMON_ERR_CFG.__PVT__ERR_SELECT
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2bU] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2bU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__WRMON_ERR_CFG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_ERR_CFG.__PVT__ERR_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2cU] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2cU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__WRMON_MASK1 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__WRMON_MASK1.__PVT__TIMEOUT_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2cU] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2cU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__WRMON_MASK1 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_MASK1.__PVT__COMPL_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2dU] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2dU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__WRMON_MASK2 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__WRMON_MASK2.__PVT__THRESH_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2dU] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2dU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__WRMON_MASK2 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_MASK2.__PVT__PERF_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2eU] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2eU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__WRMON_MASK3 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__WRMON_MASK3.__PVT__ADDR_MASK
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2eU] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2eU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__WRMON_MASK3 & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__WRMON_MASK3.__PVT__DEBUG_MASK
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2fU] 
        = ((0xffffff00U & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2fU]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__AXI_XFER_CONFIG & 
                         (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                         ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__AXI_XFER_CONFIG.__PVT__RD_XFER_BEATS
                        .__PVT__value : 0U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x2fU] 
        = ((0xffff00ffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x2fU]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__AXI_XFER_CONFIG & 
                          (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)))
                          ? vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__AXI_XFER_CONFIG.__PVT__WR_XFER_BEATS
                         .__PVT__value : 0U) << 8U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x30U] 
        = ((0xfffffffeU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x30U]) | ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                         .__PVT__PERF_CONFIG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                        & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                        .__PVT__PERF_CONFIG.__PVT__PERF_EN
                        .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x30U] 
        = ((0xfffffffdU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x30U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__PERF_CONFIG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__PERF_CONFIG.__PVT__PERF_MODE
                         .__PVT__value) << 1U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array[0x30U] 
        = ((0xfffffffbU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__readback_array
            [0x30U]) | (((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
                          .__PVT__PERF_CONFIG & (~ (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr))) 
                         & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__field_storage
                         .__PVT__PERF_CONFIG.__PVT__PERF_CLEAR
                         .__PVT__value) << 2U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__hwif_out.__PVT__GLOBAL_CTRL.__PVT__GLOBAL_RST.__PVT__swmod 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__GLOBAL_CTRL & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)) 
           & (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
              >> 1U));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__hwif_out.__PVT__CHANNEL_RESET.__PVT__CH_RST.__PVT__swmod 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__CHANNEL_RESET & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)) 
           & (0U != (0xffU & vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten)));
    vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__hwif_out.__PVT__PERF_CONFIG.__PVT__PERF_CLEAR.__PVT__swmod 
        = ((vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_reg_strb
            .__PVT__PERF_CONFIG & (IData)(vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_req_is_wr)) 
           & (vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__decoded_wr_biten 
              >> 2U));
    vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__regblk_rd_ack 
        = vlSelfRef.stream_top_ch8__DOT__regblk_rd_ack;
    __Vtableidx1 = (((IData)(vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__r_cmd_pwrite) 
                     << 8U) | (((IData)(vlSelfRef.stream_top_ch8__DOT__regblk_rd_ack) 
                                << 7U) | (((IData)(vlSelfRef.stream_top_ch8__DOT__regblk_wr_ack) 
                                           << 6U) | 
                                          (((IData)(vlSelfRef.stream_top_ch8__DOT__regblk_req_stall_rd) 
                                            << 5U) 
                                           | (((IData)(vlSelfRef.stream_top_ch8__DOT__regblk_req_stall_wr) 
                                               << 4U) 
                                              | (((IData)(vlSelfRef.stream_top_ch8__DOT__peakrdl_cmd_pwrite) 
                                                  << 3U) 
                                                 | (((IData)(vlSelfRef.stream_top_ch8__DOT__peakrdl_cmd_valid) 
                                                     << 2U) 
                                                    | (IData)(vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__cmd_state))))))));
    vlSelfRef.stream_top_ch8__DOT__u_peakrdl_adapter__DOT__cmd_state_next 
        = Vtop__ConstPool__TABLE_he32e647c_0[__Vtableidx1];
    vlSelfRef.stream_top_ch8__DOT__hwif_out = vlSelfRef.stream_top_ch8__DOT__u_stream_regs__DOT__hwif_out;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_global_ctrl_global_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__GLOBAL_CTRL
        .__PVT__GLOBAL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_global_ctrl_global_rst 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__GLOBAL_CTRL
        .__PVT__GLOBAL_RST.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_channel_enable_ch_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__CHANNEL_ENABLE
        .__PVT__CH_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_channel_reset_ch_rst 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__CHANNEL_RESET
        .__PVT__CH_RST.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_sched_timeout_cycles_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_TIMEOUT_CYCLES
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_sched_config_sched_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__SCHED_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_sched_config_timeout_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_sched_config_err_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_sched_config_compl_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__COMPL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_sched_config_perf_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_desceng_config_desceng_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_CONFIG
        .__PVT__DESCENG_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_desceng_config_prefetch_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_CONFIG
        .__PVT__PREFETCH_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_desceng_config_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_CONFIG
        .__PVT__FIFO_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_desceng_addr0_base_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_ADDR0_BASE
        .__PVT__ADDR0_BASE.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_desceng_addr0_limit_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_ADDR0_LIMIT
        .__PVT__ADDR0_LIMIT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_desceng_addr1_base_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_ADDR1_BASE
        .__PVT__ADDR1_BASE.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_desceng_addr1_limit_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_ADDR1_LIMIT
        .__PVT__ADDR1_LIMIT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_enable_mon_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__MON_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_enable_err_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_enable_compl_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__COMPL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_enable_timeout_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_enable_perf_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_timeout_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_TIMEOUT
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_latency_thresh_latency_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_LATENCY_THRESH
        .__PVT__LATENCY_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_pkt_mask_pkt_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_PKT_MASK
        .__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_err_cfg_err_select 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ERR_CFG
        .__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_err_cfg_err_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ERR_CFG
        .__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_mask1_timeout_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK1
        .__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_mask1_compl_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK1
        .__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_mask2_thresh_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK2
        .__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_mask2_perf_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK2
        .__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_mask3_addr_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK3
        .__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_daxmon_mask3_debug_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK3
        .__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_enable_mon_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__MON_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_enable_err_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_enable_compl_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__COMPL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_enable_timeout_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_enable_perf_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_timeout_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_TIMEOUT
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_latency_thresh_latency_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_LATENCY_THRESH
        .__PVT__LATENCY_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_pkt_mask_pkt_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_PKT_MASK
        .__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_err_cfg_err_select 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ERR_CFG
        .__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_err_cfg_err_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ERR_CFG
        .__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_mask1_timeout_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK1
        .__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_mask1_compl_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK1
        .__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_mask2_thresh_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK2
        .__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_mask2_perf_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK2
        .__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_mask3_addr_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK3
        .__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_rdmon_mask3_debug_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK3
        .__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_enable_mon_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__MON_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_enable_err_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_enable_compl_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__COMPL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_enable_timeout_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_enable_perf_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_timeout_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_TIMEOUT
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_latency_thresh_latency_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_LATENCY_THRESH
        .__PVT__LATENCY_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_pkt_mask_pkt_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_PKT_MASK
        .__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_err_cfg_err_select 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ERR_CFG
        .__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_err_cfg_err_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ERR_CFG
        .__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_mask1_timeout_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK1
        .__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_mask1_compl_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK1
        .__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_mask2_thresh_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK2
        .__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_mask2_perf_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK2
        .__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_mask3_addr_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK3
        .__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_wrmon_mask3_debug_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK3
        .__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_axi_xfer_config_rd_xfer_beats 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__AXI_XFER_CONFIG
        .__PVT__RD_XFER_BEATS.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_axi_xfer_config_wr_xfer_beats 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__AXI_XFER_CONFIG
        .__PVT__WR_XFER_BEATS.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_perf_config_perf_en 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__PERF_CONFIG
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_perf_config_perf_mode 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__PERF_CONFIG
        .__PVT__PERF_MODE.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__reg_perf_config_perf_clear 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__PERF_CONFIG
        .__PVT__PERF_CLEAR.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__sched_wr_burst_len 
        = (((QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                            .__PVT__AXI_XFER_CONFIG
                            .__PVT__WR_XFER_BEATS.__PVT__value)) 
            << 0x38U) | (((QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                                          .__PVT__AXI_XFER_CONFIG
                                          .__PVT__WR_XFER_BEATS
                                          .__PVT__value)) 
                          << 0x30U) | (((QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                                                        .__PVT__AXI_XFER_CONFIG
                                                        .__PVT__WR_XFER_BEATS
                                                        .__PVT__value)) 
                                        << 0x28U) | 
                                       (((QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                                                         .__PVT__AXI_XFER_CONFIG
                                                         .__PVT__WR_XFER_BEATS
                                                         .__PVT__value)) 
                                         << 0x20U) 
                                        | (((QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                                                            .__PVT__AXI_XFER_CONFIG
                                                            .__PVT__WR_XFER_BEATS
                                                            .__PVT__value)) 
                                            << 0x18U) 
                                           | (((QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                                                               .__PVT__AXI_XFER_CONFIG
                                                               .__PVT__WR_XFER_BEATS
                                                               .__PVT__value)) 
                                               << 0x10U) 
                                              | (((QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                                                                  .__PVT__AXI_XFER_CONFIG
                                                                  .__PVT__WR_XFER_BEATS
                                                                  .__PVT__value)) 
                                                  << 8U) 
                                                 | (QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                                                                   .__PVT__AXI_XFER_CONFIG
                                                                   .__PVT__WR_XFER_BEATS
                                                                   .__PVT__value)))))))));
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_perf_clear 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__PERF_CONFIG
        .__PVT__PERF_CLEAR.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_perf_mode 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__PERF_CONFIG
        .__PVT__PERF_MODE.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_axi_wr_xfer_beats 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__AXI_XFER_CONFIG
        .__PVT__WR_XFER_BEATS.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_axi_rd_xfer_beats 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__AXI_XFER_CONFIG
        .__PVT__RD_XFER_BEATS.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_debug_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK3
        .__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_debug_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK3
        .__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_addr_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK3
        .__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_addr_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK3
        .__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_perf_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK2
        .__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_perf_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK2
        .__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_thresh_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK2
        .__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_thresh_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK2
        .__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_compl_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK1
        .__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_compl_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK1
        .__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_timeout_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK1
        .__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_timeout_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_MASK1
        .__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_err_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ERR_CFG
        .__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_err_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ERR_CFG
        .__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_err_select 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ERR_CFG
        .__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_err_select 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ERR_CFG
        .__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_pkt_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_PKT_MASK
        .__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_pkt_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_PKT_MASK
        .__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_latency_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_LATENCY_THRESH
        .__PVT__LATENCY_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_latency_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_LATENCY_THRESH
        .__PVT__LATENCY_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_TIMEOUT
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_TIMEOUT
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__WRMON_ENABLE
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_debug_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK3
        .__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_debug_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK3
        .__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_addr_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK3
        .__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_addr_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK3
        .__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_perf_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK2
        .__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_perf_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK2
        .__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_thresh_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK2
        .__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_thresh_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK2
        .__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_compl_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK1
        .__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_compl_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK1
        .__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_timeout_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK1
        .__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_timeout_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_MASK1
        .__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_err_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ERR_CFG
        .__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_err_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ERR_CFG
        .__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_err_select 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ERR_CFG
        .__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_err_select 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ERR_CFG
        .__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_pkt_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_PKT_MASK
        .__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_pkt_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_PKT_MASK
        .__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_latency_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_LATENCY_THRESH
        .__PVT__LATENCY_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_latency_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_LATENCY_THRESH
        .__PVT__LATENCY_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_TIMEOUT
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_TIMEOUT
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__RDMON_ENABLE
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_debug_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK3
        .__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_debug_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK3
        .__PVT__DEBUG_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_addr_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK3
        .__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_addr_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK3
        .__PVT__ADDR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_perf_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK2
        .__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_perf_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK2
        .__PVT__PERF_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_thresh_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK2
        .__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_thresh_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK2
        .__PVT__THRESH_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_compl_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK1
        .__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_compl_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK1
        .__PVT__COMPL_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_timeout_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK1
        .__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_timeout_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_MASK1
        .__PVT__TIMEOUT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_err_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ERR_CFG
        .__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_err_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ERR_CFG
        .__PVT__ERR_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_err_select 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ERR_CFG
        .__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_err_select 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ERR_CFG
        .__PVT__ERR_SELECT.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_pkt_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_PKT_MASK
        .__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_pkt_mask 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_PKT_MASK
        .__PVT__PKT_MASK.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_latency_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_LATENCY_THRESH
        .__PVT__LATENCY_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_latency_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_LATENCY_THRESH
        .__PVT__LATENCY_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_TIMEOUT
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_TIMEOUT
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_CONFIG
        .__PVT__FIFO_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_CONFIG
        .__PVT__PREFETCH_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__COMPL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_TIMEOUT_CYCLES
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_enable 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DAXMON_ENABLE
           .__PVT__MON_EN.__PVT__value & vlSelfRef.stream_top_ch8__DOT__hwif_out
           .__PVT__GLOBAL_CTRL.__PVT__GLOBAL_EN.__PVT__value);
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_enable 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__GLOBAL_CTRL
           .__PVT__GLOBAL_EN.__PVT__value & vlSelfRef.stream_top_ch8__DOT__hwif_out
           .__PVT__RDMON_ENABLE.__PVT__MON_EN.__PVT__value);
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_enable 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__GLOBAL_CTRL
           .__PVT__GLOBAL_EN.__PVT__value & vlSelfRef.stream_top_ch8__DOT__hwif_out
           .__PVT__WRMON_ENABLE.__PVT__MON_EN.__PVT__value);
    vlSelfRef.stream_top_ch8__DOT__cfg_perf_clear = vlSelfRef.stream_top_ch8__DOT__hwif_out
        .__PVT__PERF_CONFIG.__PVT__PERF_CLEAR.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_sched_enable 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__GLOBAL_CTRL
           .__PVT__GLOBAL_EN.__PVT__value & vlSelfRef.stream_top_ch8__DOT__hwif_out
           .__PVT__SCHED_CONFIG.__PVT__SCHED_EN.__PVT__value);
    vlSelfRef.stream_top_ch8__DOT__cfg_desceng_enable 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_CONFIG
           .__PVT__DESCENG_EN.__PVT__value & vlSelfRef.stream_top_ch8__DOT__hwif_out
           .__PVT__GLOBAL_CTRL.__PVT__GLOBAL_EN.__PVT__value);
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__w_timeout_expired 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
           .__PVT__TIMEOUT_EN.__PVT__value & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__r_timeout_counter 
                                              >= vlSelfRef.stream_top_ch8__DOT__hwif_out
                                              .__PVT__SCHED_TIMEOUT_CYCLES
                                              .__PVT__TIMEOUT_CYCLES
                                              .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__w_timeout_expired 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
           .__PVT__TIMEOUT_EN.__PVT__value & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__r_timeout_counter 
                                              >= vlSelfRef.stream_top_ch8__DOT__hwif_out
                                              .__PVT__SCHED_TIMEOUT_CYCLES
                                              .__PVT__TIMEOUT_CYCLES
                                              .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__w_timeout_expired 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
           .__PVT__TIMEOUT_EN.__PVT__value & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__r_timeout_counter 
                                              >= vlSelfRef.stream_top_ch8__DOT__hwif_out
                                              .__PVT__SCHED_TIMEOUT_CYCLES
                                              .__PVT__TIMEOUT_CYCLES
                                              .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__w_timeout_expired 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
           .__PVT__TIMEOUT_EN.__PVT__value & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__r_timeout_counter 
                                              >= vlSelfRef.stream_top_ch8__DOT__hwif_out
                                              .__PVT__SCHED_TIMEOUT_CYCLES
                                              .__PVT__TIMEOUT_CYCLES
                                              .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__w_timeout_expired 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
           .__PVT__TIMEOUT_EN.__PVT__value & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__r_timeout_counter 
                                              >= vlSelfRef.stream_top_ch8__DOT__hwif_out
                                              .__PVT__SCHED_TIMEOUT_CYCLES
                                              .__PVT__TIMEOUT_CYCLES
                                              .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__w_timeout_expired 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
           .__PVT__TIMEOUT_EN.__PVT__value & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__r_timeout_counter 
                                              >= vlSelfRef.stream_top_ch8__DOT__hwif_out
                                              .__PVT__SCHED_TIMEOUT_CYCLES
                                              .__PVT__TIMEOUT_CYCLES
                                              .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__w_timeout_expired 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
           .__PVT__TIMEOUT_EN.__PVT__value & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__r_timeout_counter 
                                              >= vlSelfRef.stream_top_ch8__DOT__hwif_out
                                              .__PVT__SCHED_TIMEOUT_CYCLES
                                              .__PVT__TIMEOUT_CYCLES
                                              .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__w_timeout_expired 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
           .__PVT__TIMEOUT_EN.__PVT__value & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__r_timeout_counter 
                                              >= vlSelfRef.stream_top_ch8__DOT__hwif_out
                                              .__PVT__SCHED_TIMEOUT_CYCLES
                                              .__PVT__TIMEOUT_CYCLES
                                              .__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT____Vcellinp__u_perf_fifo__axi_aresetn 
        = ((~ (IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                      .__PVT__PERF_CONFIG.__PVT__PERF_CLEAR
                      .__PVT__value)) & (IData)(vlSelfRef.aresetn));
    vlSelfRef.stream_top_ch8__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__PERF_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__COMPL_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__ERR_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_CONFIG
        .__PVT__FIFO_THRESH.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__DESCENG_CONFIG
        .__PVT__PREFETCH_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_TIMEOUT_CYCLES
        .__PVT__TIMEOUT_CYCLES.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__SCHED_CONFIG
        .__PVT__TIMEOUT_EN.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset 
        = (0xffU & (vlSelfRef.stream_top_ch8__DOT__hwif_out
                    .__PVT__CHANNEL_RESET.__PVT__CH_RST
                    .__PVT__value | (- (IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                                               .__PVT__GLOBAL_CTRL
                                               .__PVT__GLOBAL_RST
                                               .__PVT__value))));
    vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__CHANNEL_ENABLE
           .__PVT__CH_EN.__PVT__value & (- (IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                                                   .__PVT__GLOBAL_CTRL
                                                   .__PVT__GLOBAL_EN
                                                   .__PVT__value)));
    vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__AXI_XFER_CONFIG
        .__PVT__WR_XFER_BEATS.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_axi_rd_xfer_beats 
        = vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__AXI_XFER_CONFIG
        .__PVT__RD_XFER_BEATS.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_perf_enable 
        = (vlSelfRef.stream_top_ch8__DOT__hwif_out.__PVT__GLOBAL_CTRL
           .__PVT__GLOBAL_EN.__PVT__value & vlSelfRef.stream_top_ch8__DOT__hwif_out
           .__PVT__PERF_CONFIG.__PVT__PERF_EN.__PVT__value);
    vlSelfRef.stream_top_ch8__DOT__cfg_perf_mode = vlSelfRef.stream_top_ch8__DOT__hwif_out
        .__PVT__PERF_CONFIG.__PVT__PERF_MODE.__PVT__value;
    vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base 
        = (QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                          .__PVT__DESCENG_ADDR0_BASE
                          .__PVT__ADDR0_BASE.__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit 
        = (QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                          .__PVT__DESCENG_ADDR0_LIMIT
                          .__PVT__ADDR0_LIMIT.__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base 
        = (QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                          .__PVT__DESCENG_ADDR1_BASE
                          .__PVT__ADDR1_BASE.__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit 
        = (QData)((IData)(vlSelfRef.stream_top_ch8__DOT__hwif_out
                          .__PVT__DESCENG_ADDR1_LIMIT
                          .__PVT__ADDR1_LIMIT.__PVT__value));
    vlSelfRef.stream_top_ch8__DOT__cfg_desc_mon_enable 
        = vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desc_mon_enable;
    vlSelfRef.stream_top_ch8__DOT__cfg_rdeng_mon_enable 
        = vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_rdeng_mon_enable;
    vlSelfRef.stream_top_ch8__DOT__cfg_wreng_mon_enable 
        = vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_wreng_mon_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_perf_clear 
        = vlSelfRef.stream_top_ch8__DOT__cfg_perf_clear;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_sched_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_sched_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_sched_enable;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desceng_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__u_perf_fifo__DOT__axi_aresetn 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT____Vcellinp__u_perf_fifo__axi_aresetn;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_sched_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_sched_compl_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_sched_err_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset) 
                 >> 0U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset) 
                 >> 1U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset) 
                 >> 2U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset) 
                 >> 3U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset) 
                 >> 4U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset) 
                 >> 5U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset) 
                 >> 6U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_reset) 
                 >> 7U));
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable) 
                 >> 0U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable) 
                 >> 1U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable) 
                 >> 2U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable) 
                 >> 3U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable) 
                 >> 4U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable) 
                 >> 5U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable) 
                 >> 6U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable 
        = (1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__cfg_channel_enable) 
                 >> 7U));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_axi_wr_xfer_beats 
        = vlSelfRef.stream_top_ch8__DOT__cfg_axi_wr_xfer_beats;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_axi_rd_xfer_beats 
        = vlSelfRef.stream_top_ch8__DOT__cfg_axi_rd_xfer_beats;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__cfg_perf_enable;
    if (vlSelfRef.stream_top_ch8__DOT__cfg_perf_mode) {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_perf_mode = 1U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_active_channel = 0U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_channel_event = 0U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk2__DOT__i = 0U;
        {
            while (VL_GTS_III(32, 8U, vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk2__DOT__i)) {
                if ((1U & ((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_idle_rising) 
                           >> (7U & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk2__DOT__i)))) {
                    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_active_channel 
                        = (7U & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk2__DOT__i);
                    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_channel_event = 1U;
                    goto __Vlabel1;
                }
                vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk2__DOT__i 
                    = ((IData)(1U) + vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk2__DOT__i);
            }
            __Vlabel1: ;
        }
    } else {
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_perf_mode = 0U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_active_channel = 0U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_channel_event = 0U;
        vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk1__DOT__i = 0U;
        {
            while (VL_GTS_III(32, 8U, vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk1__DOT__i)) {
                if ((1U & (((IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_idle_rising) 
                            | (IData)(vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_idle_falling)) 
                           >> (7U & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk1__DOT__i)))) {
                    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_active_channel 
                        = (7U & vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk1__DOT__i);
                    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_channel_event = 1U;
                    goto __Vlabel2;
                }
                vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk1__DOT__i 
                    = ((IData)(1U) + vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__unnamedblk1__DOT__i);
            }
            __Vlabel2: ;
        }
    }
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__u_config_block__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_addr_range_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_addr_range_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_addr_range_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_addr_range_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_addr_range_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_addr_range_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_addr_range_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_addr_range_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__r_axi_read_addr 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_valid 
        = (((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
             >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_base) 
            & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr0_limit)) 
           | ((vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
               >= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_base) 
              & (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__w_next_addr_extended 
                 <= vlSelfRef.stream_top_ch8__DOT__cfg_desceng_addr1_limit)));
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__cfg_clear 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_perf_clear;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__u_perf_fifo__DOT__write_pointer_inst__DOT__rst_n 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__u_perf_fifo__DOT__axi_aresetn;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__u_perf_fifo__DOT__read_pointer_inst__DOT__rst_n 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__u_perf_fifo__DOT__axi_aresetn;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__u_perf_fifo__DOT__fifo_control_inst__DOT__wr_rst_n 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__u_perf_fifo__DOT__axi_aresetn;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__u_perf_fifo__DOT__fifo_control_inst__DOT__rd_rst_n 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__u_perf_fifo__DOT__axi_aresetn;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_compl_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_err_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_reset 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_channel_reset;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_channel_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_channel_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_write_engine__DOT__cfg_axi_wr_xfer_beats 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_axi_wr_xfer_beats;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_axi_read_engine__DOT__cfg_axi_rd_xfer_beats 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_axi_rd_xfer_beats;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__cfg_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__cfg_mode 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_perf_mode;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_elapsed_time 
        = (vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__r_timestamp_counter 
           - vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__r_start_time
           [vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_perf_profiler__DOT__w_active_channel]);
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_sched_perf_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_perf_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_compl_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_compl_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_compl_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_compl_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_compl_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_compl_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_compl_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_sched_compl_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_compl_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_err_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_err_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_err_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_err_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_err_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_err_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_err_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_sched_err_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_err_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_fifo_threshold 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_fifo_threshold 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_fifo_threshold 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_fifo_threshold 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_fifo_threshold 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_fifo_threshold 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_fifo_threshold 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_fifo_threshold 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_fifo_thresh;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_prefetch_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_prefetch_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_prefetch_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_prefetch_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_prefetch_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_prefetch_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_prefetch_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_prefetch_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_prefetch;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_cycles 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_cycles;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_scheduler__DOT__cfg_sched_timeout_enable 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_sched_timeout_enable;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr0_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr0_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_base 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_base;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit;
    vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_descriptor_engine__DOT__cfg_addr1_limit 
        = vlSelfRef.stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__cfg_desceng_addr1_limit;
}
