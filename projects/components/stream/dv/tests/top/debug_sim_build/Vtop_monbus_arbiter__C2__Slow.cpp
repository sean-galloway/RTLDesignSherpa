// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See Vtop.h for the primary calling header

#include "Vtop__pch.h"
#include "Vtop__Syms.h"
#include "Vtop_monbus_arbiter__C2.h"

// Parameter definitions for Vtop_monbus_arbiter__C2
constexpr CData/*0:0*/ Vtop_monbus_arbiter__C2::INPUT_SKID_EN;
constexpr CData/*0:0*/ Vtop_monbus_arbiter__C2::OUTPUT_SKID_EN;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::CLIENTS;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::INPUT_SKID_ENABLE;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::OUTPUT_SKID_ENABLE;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::INPUT_SKID_DEPTH;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::OUTPUT_SKID_DEPTH;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::N;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::u_arbiter__DOT__CLIENTS;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::u_arbiter__DOT__WAIT_GNT_ACK;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::u_arbiter__DOT__N;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::u_arbiter__DOT__u_priority_encoder__DOT__CLIENTS;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::u_arbiter__DOT__u_priority_encoder__DOT__N;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DATA_WIDTH;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DEPTH;
constexpr VlWide<3>/*95:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__INSTANCE_NAME;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DW;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__BUF_WIDTH;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__0__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__BW;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DATA_WIDTH;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DEPTH;
constexpr VlWide<3>/*95:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__INSTANCE_NAME;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__DW;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__BUF_WIDTH;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_input_skid__BRA__1__KET____DOT__gen_input_skid_enabled__DOT__u_input_skid__DOT__BW;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_output_skid_enabled__DOT__u_output_skid__DOT__DATA_WIDTH;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_output_skid_enabled__DOT__u_output_skid__DOT__DEPTH;
constexpr VlWide<3>/*87:0*/ Vtop_monbus_arbiter__C2::gen_output_skid_enabled__DOT__u_output_skid__DOT__INSTANCE_NAME;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_output_skid_enabled__DOT__u_output_skid__DOT__DW;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_output_skid_enabled__DOT__u_output_skid__DOT__BUF_WIDTH;
constexpr IData/*31:0*/ Vtop_monbus_arbiter__C2::gen_output_skid_enabled__DOT__u_output_skid__DOT__BW;


void Vtop_monbus_arbiter__C2___ctor_var_reset(Vtop_monbus_arbiter__C2* vlSelf);

Vtop_monbus_arbiter__C2::Vtop_monbus_arbiter__C2(Vtop__Syms* symsp, const char* v__name)
    : VerilatedModule{v__name}
    , vlSymsp{symsp}
 {
    // Reset structure values
    Vtop_monbus_arbiter__C2___ctor_var_reset(this);
}

void Vtop_monbus_arbiter__C2::__Vconfigure(bool first) {
    (void)first;  // Prevent unused variable warning
}

Vtop_monbus_arbiter__C2::~Vtop_monbus_arbiter__C2() {
}
