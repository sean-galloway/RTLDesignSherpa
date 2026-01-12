// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "Vtop__pch.h"

//============================================================
// Constructors

Vtop::Vtop(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new Vtop__Syms(contextp(), _vcname__, this)}
    , aclk{vlSymsp->TOP.aclk}
    , aresetn{vlSymsp->TOP.aresetn}
    , pclk{vlSymsp->TOP.pclk}
    , presetn{vlSymsp->TOP.presetn}
    , s_apb_psel{vlSymsp->TOP.s_apb_psel}
    , s_apb_penable{vlSymsp->TOP.s_apb_penable}
    , s_apb_pwrite{vlSymsp->TOP.s_apb_pwrite}
    , s_apb_pstrb{vlSymsp->TOP.s_apb_pstrb}
    , s_apb_pready{vlSymsp->TOP.s_apb_pready}
    , s_apb_pslverr{vlSymsp->TOP.s_apb_pslverr}
    , m_axi_desc_arid{vlSymsp->TOP.m_axi_desc_arid}
    , m_axi_desc_arlen{vlSymsp->TOP.m_axi_desc_arlen}
    , m_axi_desc_arsize{vlSymsp->TOP.m_axi_desc_arsize}
    , m_axi_desc_arburst{vlSymsp->TOP.m_axi_desc_arburst}
    , m_axi_desc_arlock{vlSymsp->TOP.m_axi_desc_arlock}
    , m_axi_desc_arcache{vlSymsp->TOP.m_axi_desc_arcache}
    , m_axi_desc_arprot{vlSymsp->TOP.m_axi_desc_arprot}
    , m_axi_desc_arqos{vlSymsp->TOP.m_axi_desc_arqos}
    , m_axi_desc_arregion{vlSymsp->TOP.m_axi_desc_arregion}
    , m_axi_desc_aruser{vlSymsp->TOP.m_axi_desc_aruser}
    , m_axi_desc_arvalid{vlSymsp->TOP.m_axi_desc_arvalid}
    , m_axi_desc_arready{vlSymsp->TOP.m_axi_desc_arready}
    , m_axi_desc_rid{vlSymsp->TOP.m_axi_desc_rid}
    , m_axi_desc_rresp{vlSymsp->TOP.m_axi_desc_rresp}
    , m_axi_desc_rlast{vlSymsp->TOP.m_axi_desc_rlast}
    , m_axi_desc_ruser{vlSymsp->TOP.m_axi_desc_ruser}
    , m_axi_desc_rvalid{vlSymsp->TOP.m_axi_desc_rvalid}
    , m_axi_desc_rready{vlSymsp->TOP.m_axi_desc_rready}
    , m_axi_rd_arid{vlSymsp->TOP.m_axi_rd_arid}
    , m_axi_rd_arlen{vlSymsp->TOP.m_axi_rd_arlen}
    , m_axi_rd_arsize{vlSymsp->TOP.m_axi_rd_arsize}
    , m_axi_rd_arburst{vlSymsp->TOP.m_axi_rd_arburst}
    , m_axi_rd_arlock{vlSymsp->TOP.m_axi_rd_arlock}
    , m_axi_rd_arcache{vlSymsp->TOP.m_axi_rd_arcache}
    , m_axi_rd_arprot{vlSymsp->TOP.m_axi_rd_arprot}
    , m_axi_rd_arqos{vlSymsp->TOP.m_axi_rd_arqos}
    , m_axi_rd_arregion{vlSymsp->TOP.m_axi_rd_arregion}
    , m_axi_rd_aruser{vlSymsp->TOP.m_axi_rd_aruser}
    , m_axi_rd_arvalid{vlSymsp->TOP.m_axi_rd_arvalid}
    , m_axi_rd_arready{vlSymsp->TOP.m_axi_rd_arready}
    , m_axi_rd_rid{vlSymsp->TOP.m_axi_rd_rid}
    , m_axi_rd_rresp{vlSymsp->TOP.m_axi_rd_rresp}
    , m_axi_rd_rlast{vlSymsp->TOP.m_axi_rd_rlast}
    , m_axi_rd_ruser{vlSymsp->TOP.m_axi_rd_ruser}
    , m_axi_rd_rvalid{vlSymsp->TOP.m_axi_rd_rvalid}
    , m_axi_rd_rready{vlSymsp->TOP.m_axi_rd_rready}
    , m_axi_wr_awid{vlSymsp->TOP.m_axi_wr_awid}
    , m_axi_wr_awlen{vlSymsp->TOP.m_axi_wr_awlen}
    , m_axi_wr_awsize{vlSymsp->TOP.m_axi_wr_awsize}
    , m_axi_wr_awburst{vlSymsp->TOP.m_axi_wr_awburst}
    , m_axi_wr_awlock{vlSymsp->TOP.m_axi_wr_awlock}
    , m_axi_wr_awcache{vlSymsp->TOP.m_axi_wr_awcache}
    , m_axi_wr_awprot{vlSymsp->TOP.m_axi_wr_awprot}
    , m_axi_wr_awqos{vlSymsp->TOP.m_axi_wr_awqos}
    , m_axi_wr_awregion{vlSymsp->TOP.m_axi_wr_awregion}
    , m_axi_wr_awuser{vlSymsp->TOP.m_axi_wr_awuser}
    , m_axi_wr_awvalid{vlSymsp->TOP.m_axi_wr_awvalid}
    , m_axi_wr_awready{vlSymsp->TOP.m_axi_wr_awready}
    , m_axi_wr_wlast{vlSymsp->TOP.m_axi_wr_wlast}
    , m_axi_wr_wuser{vlSymsp->TOP.m_axi_wr_wuser}
    , m_axi_wr_wvalid{vlSymsp->TOP.m_axi_wr_wvalid}
    , m_axi_wr_wready{vlSymsp->TOP.m_axi_wr_wready}
    , m_axi_wr_bid{vlSymsp->TOP.m_axi_wr_bid}
    , m_axi_wr_bresp{vlSymsp->TOP.m_axi_wr_bresp}
    , m_axi_wr_buser{vlSymsp->TOP.m_axi_wr_buser}
    , m_axi_wr_bvalid{vlSymsp->TOP.m_axi_wr_bvalid}
    , m_axi_wr_bready{vlSymsp->TOP.m_axi_wr_bready}
    , s_axil_err_arvalid{vlSymsp->TOP.s_axil_err_arvalid}
    , s_axil_err_arready{vlSymsp->TOP.s_axil_err_arready}
    , s_axil_err_arprot{vlSymsp->TOP.s_axil_err_arprot}
    , s_axil_err_rvalid{vlSymsp->TOP.s_axil_err_rvalid}
    , s_axil_err_rready{vlSymsp->TOP.s_axil_err_rready}
    , s_axil_err_rresp{vlSymsp->TOP.s_axil_err_rresp}
    , m_axil_mon_awvalid{vlSymsp->TOP.m_axil_mon_awvalid}
    , m_axil_mon_awready{vlSymsp->TOP.m_axil_mon_awready}
    , m_axil_mon_awprot{vlSymsp->TOP.m_axil_mon_awprot}
    , m_axil_mon_wvalid{vlSymsp->TOP.m_axil_mon_wvalid}
    , m_axil_mon_wready{vlSymsp->TOP.m_axil_mon_wready}
    , m_axil_mon_wstrb{vlSymsp->TOP.m_axil_mon_wstrb}
    , m_axil_mon_bvalid{vlSymsp->TOP.m_axil_mon_bvalid}
    , m_axil_mon_bready{vlSymsp->TOP.m_axil_mon_bready}
    , m_axil_mon_bresp{vlSymsp->TOP.m_axil_mon_bresp}
    , stream_irq{vlSymsp->TOP.stream_irq}
    , debug_hwif_scheduler_idle{vlSymsp->TOP.debug_hwif_scheduler_idle}
    , debug_hwif_desc_engine_idle{vlSymsp->TOP.debug_hwif_desc_engine_idle}
    , debug_hwif_channel_idle{vlSymsp->TOP.debug_hwif_channel_idle}
    , debug_regblk_req{vlSymsp->TOP.debug_regblk_req}
    , debug_regblk_req_is_wr{vlSymsp->TOP.debug_regblk_req_is_wr}
    , debug_regblk_rd_ack{vlSymsp->TOP.debug_regblk_rd_ack}
    , debug_peakrdl_cmd_valid{vlSymsp->TOP.debug_peakrdl_cmd_valid}
    , debug_peakrdl_rsp_valid{vlSymsp->TOP.debug_peakrdl_rsp_valid}
    , debug_last_cpuif_rd_ack{vlSymsp->TOP.debug_last_cpuif_rd_ack}
    , debug_apb_cmd_valid{vlSymsp->TOP.debug_apb_cmd_valid}
    , debug_apb_cmd_ready{vlSymsp->TOP.debug_apb_cmd_ready}
    , debug_apb_cmd_pwrite{vlSymsp->TOP.debug_apb_cmd_pwrite}
    , debug_apb_rsp_valid{vlSymsp->TOP.debug_apb_rsp_valid}
    , debug_apb_rsp_ready{vlSymsp->TOP.debug_apb_rsp_ready}
    , debug_apb_rd_cmd_seen{vlSymsp->TOP.debug_apb_rd_cmd_seen}
    , debug_apb_rd_count{vlSymsp->TOP.debug_apb_rd_count}
    , debug_peakrdl_rd_count{vlSymsp->TOP.debug_peakrdl_rd_count}
    , debug_regblk_rd_count{vlSymsp->TOP.debug_regblk_rd_count}
    , s_apb_paddr{vlSymsp->TOP.s_apb_paddr}
    , debug_regblk_addr{vlSymsp->TOP.debug_regblk_addr}
    , debug_peakrdl_cmd_paddr{vlSymsp->TOP.debug_peakrdl_cmd_paddr}
    , debug_last_cpuif_addr{vlSymsp->TOP.debug_last_cpuif_addr}
    , debug_apb_cmd_paddr{vlSymsp->TOP.debug_apb_cmd_paddr}
    , debug_apb_rd_cmd_addr{vlSymsp->TOP.debug_apb_rd_cmd_addr}
    , s_apb_pwdata{vlSymsp->TOP.s_apb_pwdata}
    , s_apb_prdata{vlSymsp->TOP.s_apb_prdata}
    , m_axi_desc_rdata{vlSymsp->TOP.m_axi_desc_rdata}
    , m_axi_rd_rdata{vlSymsp->TOP.m_axi_rd_rdata}
    , m_axi_wr_wdata{vlSymsp->TOP.m_axi_wr_wdata}
    , s_axil_err_araddr{vlSymsp->TOP.s_axil_err_araddr}
    , s_axil_err_rdata{vlSymsp->TOP.s_axil_err_rdata}
    , m_axil_mon_awaddr{vlSymsp->TOP.m_axil_mon_awaddr}
    , m_axil_mon_wdata{vlSymsp->TOP.m_axil_mon_wdata}
    , debug_regblk_rd_data{vlSymsp->TOP.debug_regblk_rd_data}
    , debug_peakrdl_rsp_prdata{vlSymsp->TOP.debug_peakrdl_rsp_prdata}
    , debug_last_cpuif_rd_data{vlSymsp->TOP.debug_last_cpuif_rd_data}
    , debug_apb_rsp_prdata{vlSymsp->TOP.debug_apb_rsp_prdata}
    , debug_apb_rsp_prdata_captured{vlSymsp->TOP.debug_apb_rsp_prdata_captured}
    , m_axi_desc_araddr{vlSymsp->TOP.m_axi_desc_araddr}
    , m_axi_rd_araddr{vlSymsp->TOP.m_axi_rd_araddr}
    , m_axi_wr_awaddr{vlSymsp->TOP.m_axi_wr_awaddr}
    , m_axi_wr_wstrb{vlSymsp->TOP.m_axi_wr_wstrb}
    , __PVT__stream_regs_pkg{vlSymsp->TOP.__PVT__stream_regs_pkg}
    , __PVT__stream_pkg{vlSymsp->TOP.__PVT__stream_pkg}
    , __PVT__monitor_amba4_pkg{vlSymsp->TOP.__PVT__monitor_amba4_pkg}
    , __PVT__monitor_common_pkg{vlSymsp->TOP.__PVT__monitor_common_pkg}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit}
    , __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit{vlSymsp->TOP.__PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit}
    , rootp{&(vlSymsp->TOP)}
{
    // Register model with the context
    contextp()->addModel(this);
}

Vtop::Vtop(const char* _vcname__)
    : Vtop(Verilated::threadContextp(), _vcname__)
{
}

//============================================================
// Destructor

Vtop::~Vtop() {
    delete vlSymsp;
}

//============================================================
// Evaluation function

#ifdef VL_DEBUG
void Vtop___024root___eval_debug_assertions(Vtop___024root* vlSelf);
#endif  // VL_DEBUG
void Vtop___024root___eval_static(Vtop___024root* vlSelf);
void Vtop___024root___eval_initial(Vtop___024root* vlSelf);
void Vtop___024root___eval_settle(Vtop___024root* vlSelf);
void Vtop___024root___eval(Vtop___024root* vlSelf);

void Vtop::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate Vtop::eval_step\n"); );
#ifdef VL_DEBUG
    // Debug assertions
    Vtop___024root___eval_debug_assertions(&(vlSymsp->TOP));
#endif  // VL_DEBUG
    vlSymsp->__Vm_deleter.deleteAll();
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) {
        vlSymsp->__Vm_didInit = true;
        VL_DEBUG_IF(VL_DBG_MSGF("+ Initial\n"););
        Vtop___024root___eval_static(&(vlSymsp->TOP));
        Vtop___024root___eval_initial(&(vlSymsp->TOP));
        Vtop___024root___eval_settle(&(vlSymsp->TOP));
    }
    VL_DEBUG_IF(VL_DBG_MSGF("+ Eval\n"););
    Vtop___024root___eval(&(vlSymsp->TOP));
    // Evaluate cleanup
    Verilated::endOfEval(vlSymsp->__Vm_evalMsgQp);
}

//============================================================
// Events and timing
bool Vtop::eventsPending() { return false; }

uint64_t Vtop::nextTimeSlot() {
    VL_FATAL_MT(__FILE__, __LINE__, "", "%Error: No delays in the design");
    return 0;
}

//============================================================
// Utilities

const char* Vtop::name() const {
    return vlSymsp->name();
}

//============================================================
// Invoke final blocks

void Vtop___024root___eval_final(Vtop___024root* vlSelf);

VL_ATTR_COLD void Vtop::final() {
    Vtop___024root___eval_final(&(vlSymsp->TOP));
}

//============================================================
// Implementations of abstract methods from VerilatedModel

const char* Vtop::hierName() const { return vlSymsp->name(); }
const char* Vtop::modelName() const { return "Vtop"; }
unsigned Vtop::threads() const { return 1; }
void Vtop::prepareClone() const { contextp()->prepareClone(); }
void Vtop::atClone() const {
    contextp()->threadPoolpOnClone();
}
