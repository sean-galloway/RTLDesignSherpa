// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop___024unit.h"

void Vtop___024unit___ctor_var_reset(Vtop___024unit* vlSelf);

Vtop___024unit::Vtop___024unit(Vtop__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vtop___024unit___ctor_var_reset(this);
}

void Vtop___024unit::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

Vtop___024unit::~Vtop___024unit() {
}
