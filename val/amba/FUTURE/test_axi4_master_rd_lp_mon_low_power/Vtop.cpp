// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Model implementation (design independent parts)

#include "Vtop__pch.h"
#include "verilated_fst_c.h"

//============================================================
// Constructors

Vtop::Vtop(VerilatedContext* _vcontextp__, const char* _vcname__)
    : VerilatedModel{*_vcontextp__}
    , vlSymsp{new Vtop__Syms(contextp(), _vcname__, this)}
    , aclk_lp{vlSymsp->TOP.aclk_lp}
    , aresetn_lp{vlSymsp->TOP.aresetn_lp}
    , aclk{vlSymsp->TOP.aclk}
    , aresetn{vlSymsp->TOP.aresetn}
    , fub_axi_arid{vlSymsp->TOP.fub_axi_arid}
    , fub_axi_arlen{vlSymsp->TOP.fub_axi_arlen}
    , fub_axi_arsize{vlSymsp->TOP.fub_axi_arsize}
    , fub_axi_arburst{vlSymsp->TOP.fub_axi_arburst}
    , fub_axi_arlock{vlSymsp->TOP.fub_axi_arlock}
    , fub_axi_arcache{vlSymsp->TOP.fub_axi_arcache}
    , fub_axi_arprot{vlSymsp->TOP.fub_axi_arprot}
    , fub_axi_arqos{vlSymsp->TOP.fub_axi_arqos}
    , fub_axi_arregion{vlSymsp->TOP.fub_axi_arregion}
    , fub_axi_aruser{vlSymsp->TOP.fub_axi_aruser}
    , fub_axi_arvalid{vlSymsp->TOP.fub_axi_arvalid}
    , fub_axi_arready{vlSymsp->TOP.fub_axi_arready}
    , fub_axi_rid{vlSymsp->TOP.fub_axi_rid}
    , fub_axi_rresp{vlSymsp->TOP.fub_axi_rresp}
    , fub_axi_rlast{vlSymsp->TOP.fub_axi_rlast}
    , fub_axi_ruser{vlSymsp->TOP.fub_axi_ruser}
    , fub_axi_rvalid{vlSymsp->TOP.fub_axi_rvalid}
    , fub_axi_rready{vlSymsp->TOP.fub_axi_rready}
    , m_axi_arid{vlSymsp->TOP.m_axi_arid}
    , m_axi_arlen{vlSymsp->TOP.m_axi_arlen}
    , m_axi_arsize{vlSymsp->TOP.m_axi_arsize}
    , m_axi_arburst{vlSymsp->TOP.m_axi_arburst}
    , m_axi_arlock{vlSymsp->TOP.m_axi_arlock}
    , m_axi_arcache{vlSymsp->TOP.m_axi_arcache}
    , m_axi_arprot{vlSymsp->TOP.m_axi_arprot}
    , m_axi_arqos{vlSymsp->TOP.m_axi_arqos}
    , m_axi_arregion{vlSymsp->TOP.m_axi_arregion}
    , m_axi_aruser{vlSymsp->TOP.m_axi_aruser}
    , m_axi_arvalid{vlSymsp->TOP.m_axi_arvalid}
    , m_axi_arready{vlSymsp->TOP.m_axi_arready}
    , m_axi_rid{vlSymsp->TOP.m_axi_rid}
    , m_axi_rresp{vlSymsp->TOP.m_axi_rresp}
    , m_axi_rlast{vlSymsp->TOP.m_axi_rlast}
    , m_axi_ruser{vlSymsp->TOP.m_axi_ruser}
    , m_axi_rvalid{vlSymsp->TOP.m_axi_rvalid}
    , m_axi_rready{vlSymsp->TOP.m_axi_rready}
    , cfg_monitor_enable{vlSymsp->TOP.cfg_monitor_enable}
    , cfg_error_enable{vlSymsp->TOP.cfg_error_enable}
    , cfg_timeout_enable{vlSymsp->TOP.cfg_timeout_enable}
    , cfg_perf_enable{vlSymsp->TOP.cfg_perf_enable}
    , cfg_lp_enable{vlSymsp->TOP.cfg_lp_enable}
    , cfg_sleep_enable{vlSymsp->TOP.cfg_sleep_enable}
    , cfg_sleep_threshold{vlSymsp->TOP.cfg_sleep_threshold}
    , cfg_coalesce_enable{vlSymsp->TOP.cfg_coalesce_enable}
    , cfg_coalesce_window{vlSymsp->TOP.cfg_coalesce_window}
    , cfg_power_budget_enable{vlSymsp->TOP.cfg_power_budget_enable}
    , cfg_power_budget_window{vlSymsp->TOP.cfg_power_budget_window}
    , cfg_dvfs_enable{vlSymsp->TOP.cfg_dvfs_enable}
    , cfg_vf_level{vlSymsp->TOP.cfg_vf_level}
    , cfg_vf_auto{vlSymsp->TOP.cfg_vf_auto}
    , cfg_power_sample_rate{vlSymsp->TOP.cfg_power_sample_rate}
    , cfg_cg_enable{vlSymsp->TOP.cfg_cg_enable}
    , cfg_cg_idle_threshold{vlSymsp->TOP.cfg_cg_idle_threshold}
    , cfg_cg_force_on{vlSymsp->TOP.cfg_cg_force_on}
    , cfg_cg_ultra_aggressive{vlSymsp->TOP.cfg_cg_ultra_aggressive}
    , monbus_valid{vlSymsp->TOP.monbus_valid}
    , monbus_ready{vlSymsp->TOP.monbus_ready}
    , busy{vlSymsp->TOP.busy}
    , active_transactions{vlSymsp->TOP.active_transactions}
    , sleep_mode_active{vlSymsp->TOP.sleep_mode_active}
    , wake_up_pending{vlSymsp->TOP.wake_up_pending}
    , current_vf_level{vlSymsp->TOP.current_vf_level}
    , power_budget_exceeded{vlSymsp->TOP.power_budget_exceeded}
    , power_efficiency{vlSymsp->TOP.power_efficiency}
    , cg_monitor_gated{vlSymsp->TOP.cg_monitor_gated}
    , cg_reporter_gated{vlSymsp->TOP.cg_reporter_gated}
    , cg_timers_gated{vlSymsp->TOP.cg_timers_gated}
    , cg_deep_sleep{vlSymsp->TOP.cg_deep_sleep}
    , cfg_conflict_error{vlSymsp->TOP.cfg_conflict_error}
    , power_management_error{vlSymsp->TOP.power_management_error}
    , dvfs_error{vlSymsp->TOP.dvfs_error}
    , cfg_timeout_cycles{vlSymsp->TOP.cfg_timeout_cycles}
    , cfg_power_budget_limit{vlSymsp->TOP.cfg_power_budget_limit}
    , cfg_axi_pkt_mask{vlSymsp->TOP.cfg_axi_pkt_mask}
    , cfg_axi_err_select{vlSymsp->TOP.cfg_axi_err_select}
    , cfg_axi_error_mask{vlSymsp->TOP.cfg_axi_error_mask}
    , cfg_axi_timeout_mask{vlSymsp->TOP.cfg_axi_timeout_mask}
    , cfg_axi_compl_mask{vlSymsp->TOP.cfg_axi_compl_mask}
    , cfg_axi_thresh_mask{vlSymsp->TOP.cfg_axi_thresh_mask}
    , cfg_axi_perf_mask{vlSymsp->TOP.cfg_axi_perf_mask}
    , cfg_axi_addr_mask{vlSymsp->TOP.cfg_axi_addr_mask}
    , cfg_axi_debug_mask{vlSymsp->TOP.cfg_axi_debug_mask}
    , cfg_power_event_mask{vlSymsp->TOP.cfg_power_event_mask}
    , error_count{vlSymsp->TOP.error_count}
    , power_consumption{vlSymsp->TOP.power_consumption}
    , cg_power_saved_percent{vlSymsp->TOP.cg_power_saved_percent}
    , fub_axi_araddr{vlSymsp->TOP.fub_axi_araddr}
    , fub_axi_rdata{vlSymsp->TOP.fub_axi_rdata}
    , m_axi_araddr{vlSymsp->TOP.m_axi_araddr}
    , m_axi_rdata{vlSymsp->TOP.m_axi_rdata}
    , cfg_latency_threshold{vlSymsp->TOP.cfg_latency_threshold}
    , transaction_count{vlSymsp->TOP.transaction_count}
    , cg_cycles_saved{vlSymsp->TOP.cg_cycles_saved}
    , monbus_packet{vlSymsp->TOP.monbus_packet}
    , __PVT__monitor_pkg{vlSymsp->TOP.__PVT__monitor_pkg}
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
    vlSymsp->__Vm_activity = true;
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
std::unique_ptr<VerilatedTraceConfig> Vtop::traceConfig() const {
    return std::unique_ptr<VerilatedTraceConfig>{new VerilatedTraceConfig{false, false, false}};
};

//============================================================
// Trace configuration

void Vtop___024root__trace_decl_types(VerilatedFst* tracep);

void Vtop___024root__trace_init_top(Vtop___024root* vlSelf, VerilatedFst* tracep);

VL_ATTR_COLD static void trace_init(void* voidSelf, VerilatedFst* tracep, uint32_t code) {
    // Callback from tracep->open()
    Vtop___024root* const __restrict vlSelf VL_ATTR_UNUSED = static_cast<Vtop___024root*>(voidSelf);
    Vtop__Syms* const __restrict vlSymsp VL_ATTR_UNUSED = vlSelf->vlSymsp;
    if (!vlSymsp->_vm_contextp__->calcUnusedSigs()) {
        VL_FATAL_MT(__FILE__, __LINE__, __FILE__,
            "Turning on wave traces requires Verilated::traceEverOn(true) call before time 0.");
    }
    vlSymsp->__Vm_baseCode = code;
    tracep->pushPrefix(std::string{vlSymsp->name()}, VerilatedTracePrefixType::SCOPE_MODULE);
    Vtop___024root__trace_decl_types(tracep);
    Vtop___024root__trace_init_top(vlSelf, tracep);
    tracep->popPrefix();
}

VL_ATTR_COLD void Vtop___024root__trace_register(Vtop___024root* vlSelf, VerilatedFst* tracep);

VL_ATTR_COLD void Vtop::trace(VerilatedFstC* tfp, int levels, int options) {
    if (tfp->isOpen()) {
        vl_fatal(__FILE__, __LINE__, __FILE__,"'Vtop::trace()' shall not be called after 'VerilatedFstC::open()'.");
    }
    if (false && levels && options) {}  // Prevent unused
    tfp->spTrace()->addModel(this);
    tfp->spTrace()->addInitCb(&trace_init, &(vlSymsp->TOP));
    Vtop___024root__trace_register(&(vlSymsp->TOP), tfp->spTrace());
}
