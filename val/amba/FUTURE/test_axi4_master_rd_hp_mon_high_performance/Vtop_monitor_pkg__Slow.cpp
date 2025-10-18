// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop_monitor_pkg.h"

// Parameter definitions for Vtop_monitor_pkg
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeError;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeCompletion;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeThreshold;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeTimeout;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypePerf;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeCredit;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeChannel;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeStream;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeAddrMatch;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeAPB;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeReservedA;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeReservedB;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeReservedC;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeReservedD;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeReservedE;
constexpr CData/*3:0*/ Vtop_monitor_pkg::PktTypeDebug;
constexpr CData/*3:0*/ Vtop_monitor_pkg::EVT_NONE;
constexpr CData/*3:0*/ Vtop_monitor_pkg::EVT_CMD_TIMEOUT;
constexpr CData/*3:0*/ Vtop_monitor_pkg::EVT_DATA_TIMEOUT;
constexpr CData/*3:0*/ Vtop_monitor_pkg::EVT_RESP_TIMEOUT;
constexpr CData/*3:0*/ Vtop_monitor_pkg::EVT_TRANS_COMPLETE;
constexpr CData/*3:0*/ Vtop_monitor_pkg::EVT_RESP_SLVERR;
constexpr CData/*3:0*/ Vtop_monitor_pkg::EVT_RESP_DECERR;
constexpr CData/*3:0*/ Vtop_monitor_pkg::EVT_DATA_ORPHAN;
constexpr CData/*3:0*/ Vtop_monitor_pkg::EVT_RESP_ORPHAN;
constexpr CData/*3:0*/ Vtop_monitor_pkg::EVT_PROTOCOL;


void Vtop_monitor_pkg___ctor_var_reset(Vtop_monitor_pkg* vlSelf);

Vtop_monitor_pkg::Vtop_monitor_pkg(Vtop__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vtop_monitor_pkg___ctor_var_reset(this);
}

void Vtop_monitor_pkg::__Vconfigure(bool first) {
    if (false && first) {}  // Prevent unused
}

Vtop_monitor_pkg::~Vtop_monitor_pkg() {
}
