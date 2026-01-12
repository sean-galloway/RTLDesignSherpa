// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design internal header
// See Vtop.h for the primary calling header

#ifndef VERILATED_VTOP_STREAM_PKG_H_
#define VERILATED_VTOP_STREAM_PKG_H_  // guard

#include "verilated.h"


class Vtop__Syms;

class alignas(VL_CACHE_LINE_BYTES) Vtop_stream_pkg final : public VerilatedModule {
  public:

    // INTERNAL VARIABLES
    Vtop__Syms* const vlSymsp;

    // PARAMETERS
    static constexpr CData/*3:0*/ STREAM_EVENT_DESC_START = 0U;
    static constexpr CData/*3:0*/ STREAM_EVENT_DESC_COMPLETE = 1U;
    static constexpr CData/*3:0*/ STREAM_EVENT_READ_START = 2U;
    static constexpr CData/*3:0*/ STREAM_EVENT_READ_COMPLETE = 3U;
    static constexpr CData/*3:0*/ STREAM_EVENT_WRITE_START = 4U;
    static constexpr CData/*3:0*/ STREAM_EVENT_WRITE_COMPLETE = 5U;
    static constexpr CData/*3:0*/ STREAM_EVENT_CHAIN_FETCH = 6U;
    static constexpr CData/*3:0*/ STREAM_EVENT_IRQ = 7U;
    static constexpr CData/*3:0*/ STREAM_EVENT_ERROR = 0x0fU;
    static constexpr IData/*31:0*/ STREAM_MAX_CHANNELS = 8U;
    static constexpr IData/*31:0*/ STREAM_ADDR_WIDTH = 0x00000040U;
    static constexpr IData/*31:0*/ STREAM_DATA_WIDTH = 0x00000200U;
    static constexpr IData/*31:0*/ STREAM_STRB_WIDTH = 0x00000040U;
    static constexpr IData/*31:0*/ STREAM_MAX_BURST_LEN = 0x00000100U;
    static constexpr IData/*31:0*/ STREAM_DEFAULT_BURST = 0x00000010U;
    static constexpr IData/*31:0*/ STREAM_MAX_DESCRIPTORS = 0x00000010U;
    static constexpr IData/*31:0*/ STREAM_DESCRIPTOR_WIDTH = 0x00000100U;

    // CONSTRUCTORS
    Vtop_stream_pkg(Vtop__Syms* symsp, const char* v__name);
    ~Vtop_stream_pkg();
    VL_UNCOPYABLE(Vtop_stream_pkg);

    // INTERNAL METHODS
    void __Vconfigure(bool first);
};


#endif  // guard
