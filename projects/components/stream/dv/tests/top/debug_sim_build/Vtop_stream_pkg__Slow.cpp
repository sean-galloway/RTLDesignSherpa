// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop_stream_pkg.h"

// Parameter definitions for Vtop_stream_pkg
constexpr CData/*3:0*/ Vtop_stream_pkg::STREAM_EVENT_DESC_START;
constexpr CData/*3:0*/ Vtop_stream_pkg::STREAM_EVENT_DESC_COMPLETE;
constexpr CData/*3:0*/ Vtop_stream_pkg::STREAM_EVENT_READ_START;
constexpr CData/*3:0*/ Vtop_stream_pkg::STREAM_EVENT_READ_COMPLETE;
constexpr CData/*3:0*/ Vtop_stream_pkg::STREAM_EVENT_WRITE_START;
constexpr CData/*3:0*/ Vtop_stream_pkg::STREAM_EVENT_WRITE_COMPLETE;
constexpr CData/*3:0*/ Vtop_stream_pkg::STREAM_EVENT_CHAIN_FETCH;
constexpr CData/*3:0*/ Vtop_stream_pkg::STREAM_EVENT_IRQ;
constexpr CData/*3:0*/ Vtop_stream_pkg::STREAM_EVENT_ERROR;
constexpr IData/*31:0*/ Vtop_stream_pkg::STREAM_MAX_CHANNELS;
constexpr IData/*31:0*/ Vtop_stream_pkg::STREAM_ADDR_WIDTH;
constexpr IData/*31:0*/ Vtop_stream_pkg::STREAM_DATA_WIDTH;
constexpr IData/*31:0*/ Vtop_stream_pkg::STREAM_STRB_WIDTH;
constexpr IData/*31:0*/ Vtop_stream_pkg::STREAM_MAX_BURST_LEN;
constexpr IData/*31:0*/ Vtop_stream_pkg::STREAM_DEFAULT_BURST;
constexpr IData/*31:0*/ Vtop_stream_pkg::STREAM_MAX_DESCRIPTORS;
constexpr IData/*31:0*/ Vtop_stream_pkg::STREAM_DESCRIPTOR_WIDTH;


void Vtop_stream_pkg___ctor_var_reset(Vtop_stream_pkg* vlSelf);

Vtop_stream_pkg::Vtop_stream_pkg(Vtop__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vtop_stream_pkg___ctor_var_reset(this);
}

void Vtop_stream_pkg::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

Vtop_stream_pkg::~Vtop_stream_pkg() {
}
