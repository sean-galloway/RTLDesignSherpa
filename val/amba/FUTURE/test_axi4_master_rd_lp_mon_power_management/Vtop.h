// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary model header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef VERILATED_VTOP_H_
#define VERILATED_VTOP_H_  // guard

#include "verilated.h"
#include "svdpi.h"

class Vtop__Syms;
class Vtop___024root;
class VerilatedFstC;
class Vtop_monitor_pkg;


// This class is the main interface to the Verilated model
class alignas(VL_CACHE_LINE_BYTES) Vtop VL_NOT_FINAL : public VerilatedModel {
  private:
    // Symbol table holding complete model state (owned by this class)
    Vtop__Syms* const vlSymsp;

  public:

    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(&aclk_lp,0,0);
    VL_IN8(&aresetn_lp,0,0);
    VL_IN8(&aclk,0,0);
    VL_IN8(&aresetn,0,0);
    VL_IN8(&fub_axi_arid,7,0);
    VL_IN8(&fub_axi_arlen,7,0);
    VL_IN8(&fub_axi_arsize,2,0);
    VL_IN8(&fub_axi_arburst,1,0);
    VL_IN8(&fub_axi_arlock,0,0);
    VL_IN8(&fub_axi_arcache,3,0);
    VL_IN8(&fub_axi_arprot,2,0);
    VL_IN8(&fub_axi_arqos,3,0);
    VL_IN8(&fub_axi_arregion,3,0);
    VL_IN8(&fub_axi_aruser,0,0);
    VL_IN8(&fub_axi_arvalid,0,0);
    VL_OUT8(&fub_axi_arready,0,0);
    VL_OUT8(&fub_axi_rid,7,0);
    VL_OUT8(&fub_axi_rresp,1,0);
    VL_OUT8(&fub_axi_rlast,0,0);
    VL_OUT8(&fub_axi_ruser,0,0);
    VL_OUT8(&fub_axi_rvalid,0,0);
    VL_IN8(&fub_axi_rready,0,0);
    VL_OUT8(&m_axi_arid,7,0);
    VL_OUT8(&m_axi_arlen,7,0);
    VL_OUT8(&m_axi_arsize,2,0);
    VL_OUT8(&m_axi_arburst,1,0);
    VL_OUT8(&m_axi_arlock,0,0);
    VL_OUT8(&m_axi_arcache,3,0);
    VL_OUT8(&m_axi_arprot,2,0);
    VL_OUT8(&m_axi_arqos,3,0);
    VL_OUT8(&m_axi_arregion,3,0);
    VL_OUT8(&m_axi_aruser,0,0);
    VL_OUT8(&m_axi_arvalid,0,0);
    VL_IN8(&m_axi_arready,0,0);
    VL_IN8(&m_axi_rid,7,0);
    VL_IN8(&m_axi_rresp,1,0);
    VL_IN8(&m_axi_rlast,0,0);
    VL_IN8(&m_axi_ruser,0,0);
    VL_IN8(&m_axi_rvalid,0,0);
    VL_OUT8(&m_axi_rready,0,0);
    VL_IN8(&cfg_monitor_enable,0,0);
    VL_IN8(&cfg_error_enable,0,0);
    VL_IN8(&cfg_timeout_enable,0,0);
    VL_IN8(&cfg_perf_enable,0,0);
    VL_IN8(&cfg_lp_enable,0,0);
    VL_IN8(&cfg_sleep_enable,0,0);
    VL_IN8(&cfg_sleep_threshold,7,0);
    VL_IN8(&cfg_coalesce_enable,0,0);
    VL_IN8(&cfg_coalesce_window,7,0);
    VL_IN8(&cfg_power_budget_enable,0,0);
    VL_IN8(&cfg_power_budget_window,7,0);
    VL_IN8(&cfg_dvfs_enable,0,0);
    VL_IN8(&cfg_vf_level,1,0);
    VL_IN8(&cfg_vf_auto,0,0);
    VL_IN8(&cfg_power_sample_rate,7,0);
    VL_IN8(&cfg_cg_enable,0,0);
    VL_IN8(&cfg_cg_idle_threshold,7,0);
    VL_IN8(&cfg_cg_force_on,0,0);
    VL_IN8(&cfg_cg_ultra_aggressive,0,0);
    VL_OUT8(&monbus_valid,0,0);
    VL_IN8(&monbus_ready,0,0);
    VL_OUT8(&busy,0,0);
    VL_OUT8(&active_transactions,7,0);
    VL_OUT8(&sleep_mode_active,0,0);
    VL_OUT8(&wake_up_pending,0,0);
    VL_OUT8(&current_vf_level,1,0);
    VL_OUT8(&power_budget_exceeded,0,0);
    VL_OUT8(&power_efficiency,7,0);
    VL_OUT8(&cg_monitor_gated,0,0);
    VL_OUT8(&cg_reporter_gated,0,0);
    VL_OUT8(&cg_timers_gated,0,0);
    VL_OUT8(&cg_deep_sleep,0,0);
    VL_OUT8(&cfg_conflict_error,0,0);
    VL_OUT8(&power_management_error,0,0);
    VL_OUT8(&dvfs_error,0,0);
    VL_IN16(&cfg_timeout_cycles,15,0);
    VL_IN16(&cfg_power_budget_limit,15,0);
    VL_IN16(&cfg_axi_pkt_mask,15,0);
    VL_IN16(&cfg_axi_err_select,15,0);
    VL_IN16(&cfg_axi_error_mask,15,0);
    VL_IN16(&cfg_axi_timeout_mask,15,0);
    VL_IN16(&cfg_axi_compl_mask,15,0);
    VL_IN16(&cfg_axi_thresh_mask,15,0);
    VL_IN16(&cfg_axi_perf_mask,15,0);
    VL_IN16(&cfg_axi_addr_mask,15,0);
    VL_IN16(&cfg_axi_debug_mask,15,0);
    VL_IN16(&cfg_power_event_mask,15,0);
    VL_OUT16(&error_count,15,0);
    VL_OUT16(&power_consumption,15,0);
    VL_OUT16(&cg_power_saved_percent,15,0);
    VL_IN(&fub_axi_araddr,31,0);
    VL_OUT(&fub_axi_rdata,31,0);
    VL_OUT(&m_axi_araddr,31,0);
    VL_IN(&m_axi_rdata,31,0);
    VL_IN(&cfg_latency_threshold,31,0);
    VL_OUT(&transaction_count,31,0);
    VL_OUT(&cg_cycles_saved,31,0);
    VL_OUT64(&monbus_packet,63,0);

    // CELLS
    // Public to allow access to /* verilator public */ items.
    // Otherwise the application code can consider these internals.
    Vtop_monitor_pkg* const __PVT__monitor_pkg;

    // Root instance pointer to allow access to model internals,
    // including inlined /* verilator public_flat_* */ items.
    Vtop___024root* const rootp;

    // CONSTRUCTORS
    /// Construct the model; called by application code
    /// If contextp is null, then the model will use the default global context
    /// If name is "", then makes a wrapper with a
    /// single model invisible with respect to DPI scope names.
    explicit Vtop(VerilatedContext* contextp, const char* name = "TOP");
    explicit Vtop(const char* name = "TOP");
    /// Destroy the model; called (often implicitly) by application code
    virtual ~Vtop();
  private:
    VL_UNCOPYABLE(Vtop);  ///< Copying not allowed

  public:
    // API METHODS
    /// Evaluate the model.  Application must call when inputs change.
    void eval() { eval_step(); }
    /// Evaluate when calling multiple units/models per time step.
    void eval_step();
    /// Evaluate at end of a timestep for tracing, when using eval_step().
    /// Application must call after all eval() and before time changes.
    void eval_end_step() {}
    /// Simulation complete, run final blocks.  Application must call on completion.
    void final();
    /// Are there scheduled events to handle?
    bool eventsPending();
    /// Returns time at next time slot. Aborts if !eventsPending()
    uint64_t nextTimeSlot();
    /// Trace signals in the model; called by application code
    void trace(VerilatedFstC* tfp, int levels, int options = 0);
    /// Retrieve name of this model instance (as passed to constructor).
    const char* name() const;

    // Abstract methods from VerilatedModel
    const char* hierName() const override final;
    const char* modelName() const override final;
    unsigned threads() const override final;
    /// Prepare for cloning the model at the process level (e.g. fork in Linux)
    /// Release necessary resources. Called before cloning.
    void prepareClone() const;
    /// Re-init after cloning the model at the process level (e.g. fork in Linux)
    /// Re-allocate necessary resources. Called after cloning.
    void atClone() const;
    std::unique_ptr<VerilatedTraceConfig> traceConfig() const override final;
};

#endif  // guard
