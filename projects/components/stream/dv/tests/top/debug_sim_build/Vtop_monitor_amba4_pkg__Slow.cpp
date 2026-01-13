// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop_monitor_amba4_pkg.h"

// Parameter definitions for Vtop_monitor_amba4_pkg
constexpr CData/*3:0*/ Vtop_monitor_amba4_pkg::EVT_NONE;
constexpr CData/*3:0*/ Vtop_monitor_amba4_pkg::EVT_CMD_TIMEOUT;
constexpr CData/*3:0*/ Vtop_monitor_amba4_pkg::EVT_DATA_TIMEOUT;
constexpr CData/*3:0*/ Vtop_monitor_amba4_pkg::EVT_RESP_TIMEOUT;
constexpr CData/*3:0*/ Vtop_monitor_amba4_pkg::EVT_TRANS_COMPLETE;
constexpr CData/*3:0*/ Vtop_monitor_amba4_pkg::EVT_RESP_SLVERR;
constexpr CData/*3:0*/ Vtop_monitor_amba4_pkg::EVT_RESP_DECERR;
constexpr CData/*3:0*/ Vtop_monitor_amba4_pkg::EVT_DATA_ORPHAN;
constexpr CData/*3:0*/ Vtop_monitor_amba4_pkg::EVT_RESP_ORPHAN;
constexpr CData/*3:0*/ Vtop_monitor_amba4_pkg::EVT_PROTOCOL;


void Vtop_monitor_amba4_pkg___ctor_var_reset(Vtop_monitor_amba4_pkg* vlSelf);

Vtop_monitor_amba4_pkg::Vtop_monitor_amba4_pkg(Vtop__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vtop_monitor_amba4_pkg___ctor_var_reset(this);
}

void Vtop_monitor_amba4_pkg::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

Vtop_monitor_amba4_pkg::~Vtop_monitor_amba4_pkg() {
}
