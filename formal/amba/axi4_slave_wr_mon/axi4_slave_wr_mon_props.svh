// axi4_slave_wr_mon_props.svh -- spliced into rtl/amba/axi4/axi4_slave_wr_mon.sv before endmodule
// by formal/amba/axi4_slave_wr_mon/Makefile and formal/amba/axi4_slave_wr_mon_cg/Makefile.
// Not an include file for the RTL: the RTL carries no assertions.

    // ------------------------------------------------------------------------
    // Wrapper gating contract. These properties are spliced into the module
    // body (just before endmodule) of the formal flow's temp copy of the RTL
    // by this directory's Makefile, so the RTL itself carries no assertions
    // (owner rule) while the properties still see the real internal nets.
    // They cannot live in the sby harness: a plain-Verilog harness cannot form
    // hierarchical references: `dut.w_block_ready` elaborated as an implicitly-declared
    // FREE wire, which made the old harness-side P6/P7 gating properties
    // vacuous (guard over a free variable). In-module, the real nets are
    // visible and the contract is enforceable:
    //   * enabled + blocked -> upstream ready is forced low
    //   * disabled          -> the wrapper is transparent (a disabled
    //                          ocelus must never stall the datapath)
    // ------------------------------------------------------------------------
    always_comb begin
        if (aresetn && cfg_monitor_enable && !w_block_ready)
            ap_block_ready_gating: assert (!s_axi_awready);
        if (aresetn && !cfg_monitor_enable)
            ap_disabled_never_stalls: assert (s_axi_awready == w_core_s_axi_awready);
    end
