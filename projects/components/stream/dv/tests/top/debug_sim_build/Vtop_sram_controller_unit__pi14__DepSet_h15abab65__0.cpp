// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop_sram_controller_unit__pi14.h"

extern const VlWide<16>/*511:0*/ Vtop__ConstPool__CONST_h93e1b771_0;

VL_INLINE_OPT void Vtop_sram_controller_unit__pi14___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__1(Vtop_sram_controller_unit__pi14* vlSelf) {
    (void)vlSelf;  // Prevent unused variable warning
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    VL_DEBUG_IF(VL_DBG_MSGF("+            Vtop_sram_controller_unit__pi14___nba_sequent__TOP__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit__1\n"); );
    auto &vlSelfRef = std::ref(*vlSelf).get();
    // Init
    SData/*12:0*/ __Vdly__u_alloc_ctrl__DOT__r_wr_ptr_bin;
    __Vdly__u_alloc_ctrl__DOT__r_wr_ptr_bin = 0;
    VlWide<16>/*511:0*/ __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0;
    VL_ZERO_W(512, __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0);
    SData/*11:0*/ __VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0;
    __VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0 = 0;
    VlWide<16>/*511:0*/ __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0;
    VL_ZERO_W(512, __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0);
    CData/*1:0*/ __VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0;
    __VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0 = 0;
    CData/*0:0*/ __VdlySet__u_channel_fifo__DOT__gen_auto__DOT__mem__v0;
    __VdlySet__u_channel_fifo__DOT__gen_auto__DOT__mem__v0 = 0;
    CData/*0:0*/ __VdlySet__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0;
    __VdlySet__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0 = 0;
    // Body
    if (VL_UNLIKELY((((IData)(vlSelfRef.rst_n) & (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_read)) 
                     & (~ (IData)(vlSelfRef.u_alloc_ctrl__DOT__r_rd_empty))))) {
        VL_WRITEF_NX("DRAIN @ %t: drained 1 beat, rd_ptr: %0# -> %0#, space_free will be %0#\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9,13,
                     (IData)(vlSelfRef.u_alloc_ctrl__DOT__r_rd_ptr_bin),
                     13,vlSelfRef.u_alloc_ctrl__DOT__w_rd_ptr_bin_next,
                     32,((IData)(0x1000U) - ((IData)(vlSelfRef.u_alloc_ctrl__DOT__r_wr_ptr_bin) 
                                             - (IData)(vlSelfRef.u_alloc_ctrl__DOT__w_rd_ptr_bin_next))));
    }
    if (VL_UNLIKELY((((IData)(vlSelfRef.rst_n) & (IData)(vlSelfRef.u_drain_ctrl__DOT__w_write)) 
                     & (~ (IData)(vlSelfRef.u_drain_ctrl__DOT__r_wr_full))))) {
        VL_WRITEF_NX("DRAIN_CTRL @ %t: data written, wr_ptr: %0# -> %0#, data_available will be %0#\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9,13,
                     (IData)(vlSelfRef.u_drain_ctrl__DOT__r_wr_ptr_bin),
                     13,vlSelfRef.u_drain_ctrl__DOT__w_wr_ptr_bin_next,
                     13,(0x1fffU & ((IData)(vlSelfRef.u_drain_ctrl__DOT__w_wr_ptr_bin_next) 
                                    - (IData)(vlSelfRef.u_drain_ctrl__DOT__r_rd_ptr_bin))));
    }
    if (VL_UNLIKELY(((IData)(vlSelfRef.u_channel_fifo__DOT__w_write) 
                     & (IData)(vlSelfRef.u_channel_fifo__DOT__r_wr_full)))) {
        VL_TIMEFORMAT_IINI(0xfffffff7U, 3U, std::string{" ns"}, 0xaU, vlSymsp->_vm_contextp__);
        VL_WRITEF_NX("Error: DEADF1F0 write while fifo full, %t\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9);
    }
    if (VL_UNLIKELY(((IData)(vlSelfRef.u_channel_fifo__DOT__w_read) 
                     & (IData)(vlSelfRef.u_channel_fifo__DOT__r_rd_empty)))) {
        VL_TIMEFORMAT_IINI(0xfffffff7U, 3U, std::string{" ns"}, 0xaU, vlSymsp->_vm_contextp__);
        VL_WRITEF_NX("Error: DEADF1F0 read while fifo empty, %t\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9);
    }
    __VdlySet__u_channel_fifo__DOT__gen_auto__DOT__mem__v0 = 0U;
    __Vdly__u_alloc_ctrl__DOT__r_wr_ptr_bin = vlSelfRef.u_alloc_ctrl__DOT__r_wr_ptr_bin;
    __VdlySet__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0 = 0U;
    if (VL_UNLIKELY(((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_write) 
                     & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_full)))) {
        VL_TIMEFORMAT_IINI(0xfffffff7U, 3U, std::string{" ns"}, 0xaU, vlSymsp->_vm_contextp__);
        VL_WRITEF_NX("Error: DEADF1F0 write while fifo full, %t\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9);
    }
    if (VL_UNLIKELY(((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_read) 
                     & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_empty)))) {
        VL_TIMEFORMAT_IINI(0xfffffff7U, 3U, std::string{" ns"}, 0xaU, vlSymsp->_vm_contextp__);
        VL_WRITEF_NX("Error: DEADF1F0 read while fifo empty, %t\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9);
    }
    if (VL_UNLIKELY(((IData)(vlSelfRef.axi_rd_sram_valid) 
                     & (IData)(vlSelfRef.axi_rd_sram_ready)))) {
        VL_WRITEF_NX("CH_UNIT @%t: FIFO WRITE, fifo_count will be %0# -> %0#, bridge_occ=%0#, axi_wr_drain_data_avail=%0#\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9,13,
                     (IData)(vlSelfRef.fifo_count),
                     32,((IData)(1U) + (IData)(vlSelfRef.fifo_count)),
                     3,(IData)(vlSelfRef.bridge_occupancy),
                     13,vlSelfRef.axi_wr_drain_data_avail);
    }
    if (VL_UNLIKELY(((IData)(vlSelfRef.fifo_rd_valid_internal) 
                     & (IData)(vlSelfRef.fifo_rd_ready_internal)))) {
        VL_WRITEF_NX("CH_UNIT @%t: FIFO DRAIN, fifo_count will be %0# -> %0#, bridge_occ=%0#, axi_wr_drain_data_avail=%0#\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9,13,
                     (IData)(vlSelfRef.fifo_count),
                     32,((IData)(vlSelfRef.fifo_count) 
                         - (IData)(1U)),3,(IData)(vlSelfRef.bridge_occupancy),
                     13,vlSelfRef.axi_wr_drain_data_avail);
    }
    if (VL_UNLIKELY(((IData)(vlSelfRef.axi_wr_sram_valid) 
                     & (IData)(vlSelfRef.axi_wr_sram_ready)))) {
        VL_WRITEF_NX("CH_UNIT @%t: OUTPUT DRAIN, fifo_count=%0#, bridge_occ=%0#, axi_wr_drain_data_avail=%0#\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9,13,
                     (IData)(vlSelfRef.fifo_count),
                     3,vlSelfRef.bridge_occupancy,13,
                     (IData)(vlSelfRef.axi_wr_drain_data_avail));
    }
    if (VL_UNLIKELY(((IData)(vlSelfRef.u_latency_bridge__DOT__occupancy) 
                     != (IData)(vlSelfRef.u_latency_bridge__DOT__r_prev_occupancy)))) {
        VL_WRITEF_NX("BRIDGE @%t: occupancy %0# -> %0# (r_drain_ip=%0#, skid_count=%0#, s_valid=%0#, s_ready=%0#, m_valid=%0#, m_ready=%0#)\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9,3,
                     (IData)(vlSelfRef.u_latency_bridge__DOT__r_prev_occupancy),
                     3,vlSelfRef.u_latency_bridge__DOT__occupancy,
                     1,(IData)(vlSelfRef.u_latency_bridge__DOT__r_drain_ip),
                     3,vlSelfRef.u_latency_bridge__DOT__skid_count,
                     1,(IData)(vlSelfRef.fifo_rd_valid_internal),
                     1,vlSelfRef.u_latency_bridge__DOT__s_ready,
                     1,(IData)(vlSelfRef.u_latency_bridge__DOT__m_valid),
                     1,vlSelfRef.axi_wr_sram_ready);
    }
    if (VL_UNLIKELY(vlSelfRef.fifo_rd_valid_internal)) {
        VL_WRITEF_NX("BRIDGE @%t: BACKPRESSURE CHECK: s_valid=%b s_ready=%b skid_count=%0# r_drain_ip=%b skid_wr_ready=%b skid_wr_valid=%b stalled=%b pending=%0# room=%b\n",0,
                     64,VL_TIME_UNITED_Q(1000),-9,1,
                     (IData)(vlSelfRef.fifo_rd_valid_internal),
                     1,vlSelfRef.u_latency_bridge__DOT__s_ready,
                     3,(IData)(vlSelfRef.u_latency_bridge__DOT__skid_count),
                     1,vlSelfRef.u_latency_bridge__DOT__r_drain_ip,
                     1,(IData)(vlSelfRef.u_latency_bridge__DOT__skid_wr_ready),
                     1,vlSelfRef.u_latency_bridge__DOT__skid_wr_valid,
                     1,(IData)(vlSelfRef.u_latency_bridge__DOT__w_write_stalled),
                     3,vlSelfRef.u_latency_bridge__DOT__pending_count,
                     1,(IData)(vlSelfRef.u_latency_bridge__DOT__w_room_available));
    }
    if (((IData)(vlSelfRef.u_channel_fifo__DOT__w_write) 
         & (~ (IData)(vlSelfRef.u_channel_fifo__DOT__r_wr_full)))) {
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0U] 
            = vlSelfRef.axi_rd_sram_data[0U];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[1U] 
            = vlSelfRef.axi_rd_sram_data[1U];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[2U] 
            = vlSelfRef.axi_rd_sram_data[2U];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[3U] 
            = vlSelfRef.axi_rd_sram_data[3U];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[4U] 
            = vlSelfRef.axi_rd_sram_data[4U];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[5U] 
            = vlSelfRef.axi_rd_sram_data[5U];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[6U] 
            = vlSelfRef.axi_rd_sram_data[6U];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[7U] 
            = vlSelfRef.axi_rd_sram_data[7U];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[8U] 
            = vlSelfRef.axi_rd_sram_data[8U];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[9U] 
            = vlSelfRef.axi_rd_sram_data[9U];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xaU] 
            = vlSelfRef.axi_rd_sram_data[0xaU];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xbU] 
            = vlSelfRef.axi_rd_sram_data[0xbU];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xcU] 
            = vlSelfRef.axi_rd_sram_data[0xcU];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xdU] 
            = vlSelfRef.axi_rd_sram_data[0xdU];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xeU] 
            = vlSelfRef.axi_rd_sram_data[0xeU];
        __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xfU] 
            = vlSelfRef.axi_rd_sram_data[0xfU];
        __VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0 
            = vlSelfRef.u_channel_fifo__DOT__r_wr_addr;
        __VdlySet__u_channel_fifo__DOT__gen_auto__DOT__mem__v0 = 1U;
    }
    if (vlSelfRef.rst_n) {
        if (VL_UNLIKELY(((IData)(vlSelfRef.u_alloc_ctrl__DOT__w_write) 
                         & (~ (IData)(vlSelfRef.u_alloc_ctrl__DOT__r_wr_full))))) {
            __Vdly__u_alloc_ctrl__DOT__r_wr_ptr_bin 
                = (0x1fffU & ((IData)(vlSelfRef.u_alloc_ctrl__DOT__r_wr_ptr_bin) 
                              + (IData)(vlSelfRef.axi_rd_alloc_size)));
            VL_WRITEF_NX("ALLOC @ %t: allocated %0# beats, wr_ptr: %0# -> %0#, space_free will be %0#\n",0,
                         64,VL_TIME_UNITED_Q(1000),
                         -9,8,(IData)(vlSelfRef.axi_rd_alloc_size),
                         13,vlSelfRef.u_alloc_ctrl__DOT__r_wr_ptr_bin,
                         13,(0x1fffU & ((IData)(vlSelfRef.u_alloc_ctrl__DOT__r_wr_ptr_bin) 
                                        + (IData)(vlSelfRef.axi_rd_alloc_size))),
                         32,((IData)(0x1000U) - (((IData)(vlSelfRef.u_alloc_ctrl__DOT__r_wr_ptr_bin) 
                                                  + (IData)(vlSelfRef.axi_rd_alloc_size)) 
                                                 - (IData)(vlSelfRef.u_alloc_ctrl__DOT__r_rd_ptr_bin))));
        }
    } else {
        __Vdly__u_alloc_ctrl__DOT__r_wr_ptr_bin = 0U;
    }
    if (vlSelfRef.rst_n) {
        if (((IData)(vlSelfRef.u_drain_ctrl__DOT__w_read) 
             & (~ (IData)(vlSelfRef.u_drain_ctrl__DOT__r_rd_empty)))) {
            vlSelfRef.u_drain_ctrl__DOT__r_rd_ptr_bin 
                = (0x1fffU & ((IData)(vlSelfRef.u_drain_ctrl__DOT__r_rd_ptr_bin) 
                              + (IData)(vlSelfRef.axi_wr_drain_size)));
        }
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed 
            = vlSelfRef.u_drain_ctrl__DOT__w_wr_ptr_bin_next;
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed 
            = vlSelfRef.u_alloc_ctrl__DOT__w_wr_ptr_bin_next;
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed 
            = vlSelfRef.u_channel_fifo__DOT__w_wr_ptr_bin_next;
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0U] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][0U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[1U] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][1U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[2U] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][2U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[3U] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][3U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[4U] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][4U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[5U] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][5U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[6U] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][6U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[7U] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][7U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[8U] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][8U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[9U] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][9U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xaU] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][0xaU];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xbU] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][0xbU];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xcU] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][0xcU];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xdU] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][0xdU];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xeU] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][0xeU];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xfU] 
            = vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem
            [vlSelfRef.u_channel_fifo__DOT__r_rd_addr][0xfU];
        vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr 
            = vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_next;
        vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr 
            = vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_next;
        vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr 
            = vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_next;
        vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr 
            = vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_next;
        vlSelfRef.axi_rd_alloc_space_free = vlSelfRef.alloc_space_free;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr 
            = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_next;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr 
            = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_next;
    } else {
        vlSelfRef.u_drain_ctrl__DOT__r_rd_ptr_bin = 0U;
        vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed = 0U;
        vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed = 0U;
        vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed = 0U;
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0U] 
            = Vtop__ConstPool__CONST_h93e1b771_0[0U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[1U] 
            = Vtop__ConstPool__CONST_h93e1b771_0[1U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[2U] 
            = Vtop__ConstPool__CONST_h93e1b771_0[2U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[3U] 
            = Vtop__ConstPool__CONST_h93e1b771_0[3U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[4U] 
            = Vtop__ConstPool__CONST_h93e1b771_0[4U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[5U] 
            = Vtop__ConstPool__CONST_h93e1b771_0[5U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[6U] 
            = Vtop__ConstPool__CONST_h93e1b771_0[6U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[7U] 
            = Vtop__ConstPool__CONST_h93e1b771_0[7U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[8U] 
            = Vtop__ConstPool__CONST_h93e1b771_0[8U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[9U] 
            = Vtop__ConstPool__CONST_h93e1b771_0[9U];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xaU] 
            = Vtop__ConstPool__CONST_h93e1b771_0[0xaU];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xbU] 
            = Vtop__ConstPool__CONST_h93e1b771_0[0xbU];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xcU] 
            = Vtop__ConstPool__CONST_h93e1b771_0[0xcU];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xdU] 
            = Vtop__ConstPool__CONST_h93e1b771_0[0xdU];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xeU] 
            = Vtop__ConstPool__CONST_h93e1b771_0[0xeU];
        vlSelfRef.u_channel_fifo__DOT__w_rd_data[0xfU] 
            = Vtop__ConstPool__CONST_h93e1b771_0[0xfU];
        vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr = 0U;
        vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr = 0U;
        vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr = 0U;
        vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr = 0U;
        vlSelfRef.axi_rd_alloc_space_free = 0x1000U;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr = 0U;
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr = 0U;
    }
    if (((IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__w_write) 
         & (~ (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_full)))) {
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0U] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0U];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[1U] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[1U];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[2U] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[2U];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[3U] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[3U];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[4U] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[4U];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[5U] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[5U];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[6U] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[6U];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[7U] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[7U];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[8U] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[8U];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[9U] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[9U];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xaU] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xaU];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xbU] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xbU];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xcU] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xcU];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xdU] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xdU];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xeU] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xeU];
        __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xfU] 
            = vlSelfRef.u_latency_bridge__DOT__skid_wr_data[0xfU];
        __VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0 
            = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_addr;
        __VdlySet__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0 = 1U;
    }
    vlSelfRef.u_alloc_ctrl__DOT__r_wr_ptr_bin = __Vdly__u_alloc_ctrl__DOT__r_wr_ptr_bin;
    if (__VdlySet__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0) {
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][0U] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0U];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][1U] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[1U];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][2U] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[2U];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][3U] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[3U];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][4U] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[4U];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][5U] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[5U];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][6U] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[6U];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][7U] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[7U];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][8U] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[8U];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][9U] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[9U];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][0xaU] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xaU];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][0xbU] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xbU];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][0xcU] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xcU];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][0xdU] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xdU];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][0xeU] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xeU];
        vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem[__VdlyDim0__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0][0xfU] 
            = __VdlyVal__u_latency_bridge__DOT__u_skid_buffer__DOT__gen_auto__DOT__mem__v0[0xfU];
    }
    vlSelfRef.u_latency_bridge__DOT__r_prev_occupancy 
        = vlSelfRef.u_latency_bridge__DOT__occupancy;
    vlSelfRef.u_latency_bridge__DOT__r_drain_ip = ((IData)(vlSelfRef.rst_n) 
                                                   && (IData)(vlSelfRef.u_latency_bridge__DOT__w_drain_fifo));
    if (__VdlySet__u_channel_fifo__DOT__gen_auto__DOT__mem__v0) {
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][0U] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0U];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][1U] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[1U];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][2U] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[2U];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][3U] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[3U];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][4U] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[4U];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][5U] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[5U];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][6U] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[6U];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][7U] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[7U];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][8U] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[8U];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][9U] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[9U];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][0xaU] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xaU];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][0xbU] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xbU];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][0xcU] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xcU];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][0xdU] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xdU];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][0xeU] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xeU];
        vlSelfRef.u_channel_fifo__DOT__gen_auto__DOT__mem[__VdlyDim0__u_channel_fifo__DOT__gen_auto__DOT__mem__v0][0xfU] 
            = __VdlyVal__u_channel_fifo__DOT__gen_auto__DOT__mem__v0[0xfU];
    }
    vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__w_wr_ptr_for_empty 
        = vlSelfRef.u_drain_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed;
    vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__w_wr_ptr_for_empty 
        = vlSelfRef.u_alloc_ctrl__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed;
    vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__w_wr_ptr_for_empty 
        = vlSelfRef.u_channel_fifo__DOT__fifo_control_inst__DOT__gen_flop_mode__DOT__r_rdom_wr_ptr_bin_delayed;
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
    vlSelfRef.u_drain_ctrl__DOT__r_wr_ptr_bin = vlSelfRef.u_drain_ctrl__DOT__write_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_alloc_ctrl__DOT__r_rd_ptr_bin = vlSelfRef.u_alloc_ctrl__DOT__read_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_channel_fifo__DOT__r_wr_ptr_bin = vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_channel_fifo__DOT__r_wr_addr = (0xfffU 
                                                & (IData)(vlSelfRef.u_channel_fifo__DOT__write_pointer_inst__DOT__counter_bin_curr));
    vlSelfRef.u_channel_fifo__DOT__r_rd_ptr_bin = vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_channel_fifo__DOT__r_rd_addr = (0xfffU 
                                                & (IData)(vlSelfRef.u_channel_fifo__DOT__read_pointer_inst__DOT__counter_bin_curr));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_wr_addr 
        = (3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__counter_bin_curr));
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_ptr_bin 
        = vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr;
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__r_rd_addr 
        = (3U & (IData)(vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__counter_bin_curr));
    vlSelfRef.u_latency_bridge__DOT__dbg_r_pending 
        = vlSelfRef.u_latency_bridge__DOT__r_drain_ip;
    vlSelfRef.u_latency_bridge__DOT__skid_wr_valid 
        = vlSelfRef.u_latency_bridge__DOT__r_drain_ip;
    vlSelfRef.dbg_bridge_pending = vlSelfRef.u_latency_bridge__DOT__r_drain_ip;
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
    vlSelfRef.u_latency_bridge__DOT__u_skid_buffer__DOT__wr_valid 
        = vlSelfRef.u_latency_bridge__DOT__skid_wr_valid;
}
