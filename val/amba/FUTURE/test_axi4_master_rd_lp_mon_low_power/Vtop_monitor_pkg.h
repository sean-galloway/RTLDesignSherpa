// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtop.h for the primary calling header

#ifndef VERILATED_VTOP_MONITOR_PKG_H_
#define VERILATED_VTOP_MONITOR_PKG_H_  // guard

#include "verilated.h"


class Vtop__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vtop_monitor_pkg final : public VerilatedModule {
  public:

    // INTERNAL VARIABLES
    Vtop__Syms* const vlSymsp;

    // PARAMETERS
    static constexpr CData/*3:0*/ PktTypeError = 0U;
    static constexpr CData/*3:0*/ PktTypeCompletion = 1U;
    static constexpr CData/*3:0*/ PktTypeThreshold = 2U;
    static constexpr CData/*3:0*/ PktTypeTimeout = 3U;
    static constexpr CData/*3:0*/ PktTypePerf = 4U;
    static constexpr CData/*3:0*/ PktTypeCredit = 5U;
    static constexpr CData/*3:0*/ PktTypeChannel = 6U;
    static constexpr CData/*3:0*/ PktTypeStream = 7U;
    static constexpr CData/*3:0*/ PktTypeAddrMatch = 8U;
    static constexpr CData/*3:0*/ PktTypeAPB = 9U;
    static constexpr CData/*3:0*/ PktTypeReservedA = 0x0aU;
    static constexpr CData/*3:0*/ PktTypeReservedB = 0x0bU;
    static constexpr CData/*3:0*/ PktTypeReservedC = 0x0cU;
    static constexpr CData/*3:0*/ PktTypeReservedD = 0x0dU;
    static constexpr CData/*3:0*/ PktTypeReservedE = 0x0eU;
    static constexpr CData/*3:0*/ PktTypeDebug = 0x0fU;
    static constexpr CData/*3:0*/ EVT_NONE = 0U;
    static constexpr CData/*3:0*/ EVT_CMD_TIMEOUT = 0U;
    static constexpr CData/*3:0*/ EVT_DATA_TIMEOUT = 1U;
    static constexpr CData/*3:0*/ EVT_RESP_TIMEOUT = 2U;
    static constexpr CData/*3:0*/ EVT_TRANS_COMPLETE = 0U;
    static constexpr CData/*3:0*/ EVT_RESP_SLVERR = 0U;
    static constexpr CData/*3:0*/ EVT_RESP_DECERR = 1U;
    static constexpr CData/*3:0*/ EVT_DATA_ORPHAN = 2U;
    static constexpr CData/*3:0*/ EVT_RESP_ORPHAN = 3U;
    static constexpr CData/*3:0*/ EVT_PROTOCOL = 4U;

    // CONSTRUCTORS
    Vtop_monitor_pkg(Vtop__Syms* symsp, const char* v__name);
    ~Vtop_monitor_pkg();
    VL_UNCOPYABLE(Vtop_monitor_pkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
