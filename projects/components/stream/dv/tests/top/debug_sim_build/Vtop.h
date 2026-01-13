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
class Vtop_monbus_arbiter__C2;
class Vtop_monitor_amba4_pkg;
class Vtop_monitor_common_pkg;
class Vtop_sram_controller_unit__pi14;
class Vtop_stream_pkg;
#include "Vtop_stream_regs_pkg.h"


// This class is the main interface to the Verilated model
class alignas(VL_CACHE_LINE_BYTES) Vtop VL_NOT_FINAL : public VerilatedModel {
  private:
    // Symbol table holding complete model state (owned by this class)
    Vtop__Syms* const vlSymsp;

  public:

    // CONSTEXPR CAPABILITIES
    // Verilated with --trace?
    static constexpr bool traceCapable = false;

    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(&aclk,0,0);
    VL_IN8(&aresetn,0,0);
    VL_IN8(&pclk,0,0);
    VL_IN8(&presetn,0,0);
    VL_IN8(&s_apb_psel,0,0);
    VL_IN8(&s_apb_penable,0,0);
    VL_IN8(&s_apb_pwrite,0,0);
    VL_IN8(&s_apb_pstrb,3,0);
    VL_OUT8(&s_apb_pready,0,0);
    VL_OUT8(&s_apb_pslverr,0,0);
    VL_OUT8(&m_axi_desc_arid,7,0);
    VL_OUT8(&m_axi_desc_arlen,7,0);
    VL_OUT8(&m_axi_desc_arsize,2,0);
    VL_OUT8(&m_axi_desc_arburst,1,0);
    VL_OUT8(&m_axi_desc_arlock,0,0);
    VL_OUT8(&m_axi_desc_arcache,3,0);
    VL_OUT8(&m_axi_desc_arprot,2,0);
    VL_OUT8(&m_axi_desc_arqos,3,0);
    VL_OUT8(&m_axi_desc_arregion,3,0);
    VL_OUT8(&m_axi_desc_aruser,2,0);
    VL_OUT8(&m_axi_desc_arvalid,0,0);
    VL_IN8(&m_axi_desc_arready,0,0);
    VL_IN8(&m_axi_desc_rid,7,0);
    VL_IN8(&m_axi_desc_rresp,1,0);
    VL_IN8(&m_axi_desc_rlast,0,0);
    VL_IN8(&m_axi_desc_ruser,2,0);
    VL_IN8(&m_axi_desc_rvalid,0,0);
    VL_OUT8(&m_axi_desc_rready,0,0);
    VL_OUT8(&m_axi_rd_arid,7,0);
    VL_OUT8(&m_axi_rd_arlen,7,0);
    VL_OUT8(&m_axi_rd_arsize,2,0);
    VL_OUT8(&m_axi_rd_arburst,1,0);
    VL_OUT8(&m_axi_rd_arlock,0,0);
    VL_OUT8(&m_axi_rd_arcache,3,0);
    VL_OUT8(&m_axi_rd_arprot,2,0);
    VL_OUT8(&m_axi_rd_arqos,3,0);
    VL_OUT8(&m_axi_rd_arregion,3,0);
    VL_OUT8(&m_axi_rd_aruser,2,0);
    VL_OUT8(&m_axi_rd_arvalid,0,0);
    VL_IN8(&m_axi_rd_arready,0,0);
    VL_IN8(&m_axi_rd_rid,7,0);
    VL_IN8(&m_axi_rd_rresp,1,0);
    VL_IN8(&m_axi_rd_rlast,0,0);
    VL_IN8(&m_axi_rd_ruser,2,0);
    VL_IN8(&m_axi_rd_rvalid,0,0);
    VL_OUT8(&m_axi_rd_rready,0,0);
    VL_OUT8(&m_axi_wr_awid,7,0);
    VL_OUT8(&m_axi_wr_awlen,7,0);
    VL_OUT8(&m_axi_wr_awsize,2,0);
    VL_OUT8(&m_axi_wr_awburst,1,0);
    VL_OUT8(&m_axi_wr_awlock,0,0);
    VL_OUT8(&m_axi_wr_awcache,3,0);
    VL_OUT8(&m_axi_wr_awprot,2,0);
    VL_OUT8(&m_axi_wr_awqos,3,0);
    VL_OUT8(&m_axi_wr_awregion,3,0);
    VL_OUT8(&m_axi_wr_awuser,2,0);
    VL_OUT8(&m_axi_wr_awvalid,0,0);
    VL_IN8(&m_axi_wr_awready,0,0);
    VL_OUT8(&m_axi_wr_wlast,0,0);
    VL_OUT8(&m_axi_wr_wuser,2,0);
    VL_OUT8(&m_axi_wr_wvalid,0,0);
    VL_IN8(&m_axi_wr_wready,0,0);
    VL_IN8(&m_axi_wr_bid,7,0);
    VL_IN8(&m_axi_wr_bresp,1,0);
    VL_IN8(&m_axi_wr_buser,2,0);
    VL_IN8(&m_axi_wr_bvalid,0,0);
    VL_OUT8(&m_axi_wr_bready,0,0);
    VL_IN8(&s_axil_err_arvalid,0,0);
    VL_OUT8(&s_axil_err_arready,0,0);
    VL_IN8(&s_axil_err_arprot,2,0);
    VL_OUT8(&s_axil_err_rvalid,0,0);
    VL_IN8(&s_axil_err_rready,0,0);
    VL_OUT8(&s_axil_err_rresp,1,0);
    VL_OUT8(&m_axil_mon_awvalid,0,0);
    VL_IN8(&m_axil_mon_awready,0,0);
    VL_OUT8(&m_axil_mon_awprot,2,0);
    VL_OUT8(&m_axil_mon_wvalid,0,0);
    VL_IN8(&m_axil_mon_wready,0,0);
    VL_OUT8(&m_axil_mon_wstrb,3,0);
    VL_IN8(&m_axil_mon_bvalid,0,0);
    VL_OUT8(&m_axil_mon_bready,0,0);
    VL_IN8(&m_axil_mon_bresp,1,0);
    VL_OUT8(&stream_irq,0,0);
    VL_OUT8(&debug_hwif_scheduler_idle,7,0);
    VL_OUT8(&debug_hwif_desc_engine_idle,7,0);
    VL_OUT8(&debug_hwif_channel_idle,7,0);
    VL_OUT8(&debug_regblk_req,0,0);
    VL_OUT8(&debug_regblk_req_is_wr,0,0);
    VL_OUT8(&debug_regblk_rd_ack,0,0);
    VL_OUT8(&debug_peakrdl_cmd_valid,0,0);
    VL_OUT8(&debug_peakrdl_rsp_valid,0,0);
    VL_OUT8(&debug_last_cpuif_rd_ack,0,0);
    VL_OUT8(&debug_apb_cmd_valid,0,0);
    VL_OUT8(&debug_apb_cmd_ready,0,0);
    VL_OUT8(&debug_apb_cmd_pwrite,0,0);
    VL_OUT8(&debug_apb_rsp_valid,0,0);
    VL_OUT8(&debug_apb_rsp_ready,0,0);
    VL_OUT8(&debug_apb_rd_cmd_seen,0,0);
    VL_OUT8(&debug_apb_rd_count,7,0);
    VL_OUT8(&debug_peakrdl_rd_count,7,0);
    VL_OUT8(&debug_regblk_rd_count,7,0);
    VL_IN16(&s_apb_paddr,11,0);
    VL_OUT16(&debug_regblk_addr,11,0);
    VL_OUT16(&debug_peakrdl_cmd_paddr,11,0);
    VL_OUT16(&debug_last_cpuif_addr,9,0);
    VL_OUT16(&debug_apb_cmd_paddr,11,0);
    VL_OUT16(&debug_apb_rd_cmd_addr,11,0);
    VL_IN(&s_apb_pwdata,31,0);
    VL_OUT(&s_apb_prdata,31,0);
    VL_INW(&m_axi_desc_rdata,255,0,8);
    VL_INW(&m_axi_rd_rdata,511,0,16);
    VL_OUTW(&m_axi_wr_wdata,511,0,16);
    VL_IN(&s_axil_err_araddr,31,0);
    VL_OUT(&s_axil_err_rdata,31,0);
    VL_OUT(&m_axil_mon_awaddr,31,0);
    VL_OUT(&m_axil_mon_wdata,31,0);
    VL_OUT(&debug_regblk_rd_data,31,0);
    VL_OUT(&debug_peakrdl_rsp_prdata,31,0);
    VL_OUT(&debug_last_cpuif_rd_data,31,0);
    VL_OUT(&debug_apb_rsp_prdata,31,0);
    VL_OUT(&debug_apb_rsp_prdata_captured,31,0);
    VL_OUT64(&m_axi_desc_araddr,63,0);
    VL_OUT64(&m_axi_rd_araddr,63,0);
    VL_OUT64(&m_axi_wr_awaddr,63,0);
    VL_OUT64(&m_axi_wr_wstrb,63,0);

    // CELLS
    // Public to allow access to /* verilator public */ items.
    // Otherwise the application code can consider these internals.
    Vtop_stream_regs_pkg* const __PVT__stream_regs_pkg;
    Vtop_stream_pkg* const __PVT__stream_pkg;
    Vtop_monitor_amba4_pkg* const __PVT__monitor_amba4_pkg;
    Vtop_monitor_common_pkg* const __PVT__monitor_common_pkg;
    Vtop_monbus_arbiter__C2* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__0__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator;
    Vtop_monbus_arbiter__C2* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__1__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator;
    Vtop_monbus_arbiter__C2* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__2__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator;
    Vtop_monbus_arbiter__C2* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__3__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator;
    Vtop_monbus_arbiter__C2* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__4__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator;
    Vtop_monbus_arbiter__C2* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__5__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator;
    Vtop_monbus_arbiter__C2* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__6__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator;
    Vtop_monbus_arbiter__C2* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_scheduler_group_array__DOT__gen_scheduler_groups__BRA__7__KET____DOT__u_scheduler_group__DOT__u_monbus_aggregator;
    Vtop_sram_controller_unit__pi14* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__0__KET____DOT__u_channel_unit;
    Vtop_sram_controller_unit__pi14* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__1__KET____DOT__u_channel_unit;
    Vtop_sram_controller_unit__pi14* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__2__KET____DOT__u_channel_unit;
    Vtop_sram_controller_unit__pi14* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__3__KET____DOT__u_channel_unit;
    Vtop_sram_controller_unit__pi14* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__4__KET____DOT__u_channel_unit;
    Vtop_sram_controller_unit__pi14* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__5__KET____DOT__u_channel_unit;
    Vtop_sram_controller_unit__pi14* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__6__KET____DOT__u_channel_unit;
    Vtop_sram_controller_unit__pi14* const __PVT__stream_top_ch8__DOT__g_stream_core__DOT__u_stream_core__DOT__u_sram_controller__DOT__gen_channel_units__BRA__7__KET____DOT__u_channel_unit;

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
    void trace(VerilatedTraceBaseC* tfp, int levels, int options = 0) { contextp()->trace(tfp, levels, options); }
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
  private:
    // Internal functions - trace registration
    void traceBaseModel(VerilatedTraceBaseC* tfp, int levels, int options);
};

#endif  // guard
