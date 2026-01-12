// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop_monitor_common_pkg.h"

// Parameter definitions for Vtop_monitor_common_pkg
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeError;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeCompletion;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeThreshold;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeTimeout;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypePerf;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeCredit;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeChannel;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeStream;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeAddrMatch;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeAPB;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeReservedA;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeReservedB;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeReservedC;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeReservedD;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeReservedE;
constexpr CData/*3:0*/ Vtop_monitor_common_pkg::PktTypeDebug;


void Vtop_monitor_common_pkg___ctor_var_reset(Vtop_monitor_common_pkg* vlSelf);

Vtop_monitor_common_pkg::Vtop_monitor_common_pkg(Vtop__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vtop_monitor_common_pkg___ctor_var_reset(this);
}

void Vtop_monitor_common_pkg::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

Vtop_monitor_common_pkg::~Vtop_monitor_common_pkg() {
}
