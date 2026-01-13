// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop_stream_regs_pkg.h"

// Parameter definitions for Vtop_stream_regs_pkg
constexpr IData/*31:0*/ Vtop_stream_regs_pkg::STREAM_REGS_DATA_WIDTH;
constexpr IData/*31:0*/ Vtop_stream_regs_pkg::STREAM_REGS_MIN_ADDR_WIDTH;
constexpr IData/*31:0*/ Vtop_stream_regs_pkg::STREAM_REGS_SIZE;


void Vtop_stream_regs_pkg___ctor_var_reset(Vtop_stream_regs_pkg* vlSelf);

Vtop_stream_regs_pkg::Vtop_stream_regs_pkg(Vtop__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vtop_stream_regs_pkg___ctor_var_reset(this);
}

void Vtop_stream_regs_pkg::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

Vtop_stream_regs_pkg::~Vtop_stream_regs_pkg() {
}
