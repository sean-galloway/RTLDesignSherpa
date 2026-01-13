// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop_sram_controller_unit__pi14.h"

// Parameter definitions for Vtop_sram_controller_unit__pi14
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::DATA_WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::SRAM_DEPTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::SEG_COUNT_WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::DW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::SD;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::SCW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::ADDR_WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__DEPTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__ALMOST_WR_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__ALMOST_RD_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__REGISTERED;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__D;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__AW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__read_pointer_inst__DOT__WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__read_pointer_inst__DOT__MAX;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__ADDR_WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__DEPTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__ALMOST_WR_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__ALMOST_RD_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__REGISTERED;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__D;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__AW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__AFULL;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__AEMPTY;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__AFT;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_alloc_ctrl__DOT__fifo_control_inst__DOT__AET;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__DEPTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__ALMOST_WR_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__ALMOST_RD_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__REGISTERED;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__D;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__AW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__write_pointer_inst__DOT__WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__write_pointer_inst__DOT__MAX;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__ADDR_WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__DEPTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__ALMOST_WR_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__ALMOST_RD_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__REGISTERED;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__D;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__AW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__AFULL;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__AEMPTY;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__AFT;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_drain_ctrl__DOT__fifo_control_inst__DOT__AET;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__MEM_STYLE;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__REGISTERED;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__DATA_WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__DEPTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__ALMOST_WR_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__ALMOST_RD_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__DW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__D;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__AW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__write_pointer_inst__DOT__WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__write_pointer_inst__DOT__MAX;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__read_pointer_inst__DOT__WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__read_pointer_inst__DOT__MAX;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__ADDR_WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__DEPTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__ALMOST_WR_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__ALMOST_RD_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__REGISTERED;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__D;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__AW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__AFULL;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__AEMPTY;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__AFT;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__fifo_control_inst__DOT__AET;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__DATA_WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__SKID_DEPTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__DW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__MEM_STYLE;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__REGISTERED;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__DATA_WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__DEPTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__ALMOST_WR_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__ALMOST_RD_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__DW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__D;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__AW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__write_pointer_inst__DOT__MAX;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__read_pointer_inst__DOT__MAX;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__ADDR_WIDTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__DEPTH;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__ALMOST_WR_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__ALMOST_RD_MARGIN;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__REGISTERED;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__D;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__AW;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__AFULL;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__AEMPTY;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__AFT;
constexpr IData/*31:0*/ Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__fifo_control_inst__DOT__AET;
const std::string Vtop_sram_controller_unit__pi14::u_channel_fifo__DOT__INSTANCE_NAME = "DEADF1F0";
const std::string Vtop_sram_controller_unit__pi14::u_latency_bridge__DOT__u_skid_buffer__DOT__INSTANCE_NAME = "DEADF1F0";


void Vtop_sram_controller_unit__pi14___ctor_var_reset(Vtop_sram_controller_unit__pi14* vlSelf);

Vtop_sram_controller_unit__pi14::Vtop_sram_controller_unit__pi14(Vtop__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vtop_sram_controller_unit__pi14___ctor_var_reset(this);
}

void Vtop_sram_controller_unit__pi14::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

Vtop_sram_controller_unit__pi14::~Vtop_sram_controller_unit__pi14() {
}
