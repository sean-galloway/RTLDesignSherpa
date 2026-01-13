// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtop.h for the primary calling header

#ifndef VERILATED_VTOP_MONITOR_AMBA4_PKG_H_
#define VERILATED_VTOP_MONITOR_AMBA4_PKG_H_  // guard

#include "verilated.h"


class Vtop__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vtop_monitor_amba4_pkg final : public VerilatedModule {
  public:

    // INTERNAL VARIABLES
    Vtop__Syms* const vlSymsp;

    // PARAMETERS
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
    Vtop_monitor_amba4_pkg(Vtop__Syms* symsp, const char* v__name);
    ~Vtop_monitor_amba4_pkg();
    VL_UNCOPYABLE(Vtop_monitor_amba4_pkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
