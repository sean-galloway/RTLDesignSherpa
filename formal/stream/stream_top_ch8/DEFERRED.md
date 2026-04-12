# stream_top_ch8 -- DEFERRED

## Status: DEFERRED

## Blocker: Dependency complexity exceeds sv2v tractability

stream_top_ch8 is the top-level STREAM wrapper (1648 lines) that integrates:

1. **APB interface** -- apb_slave_cdc or apb_slave (conditional on CDC_ENABLE)
2. **Command/Response routing** -- cmdrsp_router (address-based routing)
3. **Descriptor kick-off** -- apbtodescr (channel kick-off, 0x000-0x03F)
4. **PeakRDL registers** -- peakrdl_to_cmdrsp + stream_regs (PeakRDL-generated, 0x100-0x3FF)
5. **Register mapping** -- stream_config_block
6. **DMA core** -- stream_core (conditionally monitors enabled/disabled)
7. **Monitor bus** -- monbus_axil_group (AXI-Lite conversion)

### Specific blockers

1. **PeakRDL-generated stream_regs.sv**: Located at
   `projects/components/stream/regs/generated/rtl/stream_regs.sv`.
   This is auto-generated code with a large register map. Adding it to
   the sv2v dependency chain significantly increases flattened Verilog size
   and formal state space.

2. **peakrdl_to_cmdrsp.sv**: Protocol converter at
   `projects/components/converters/rtl/peakrdl_to_cmdrsp.sv`.
   Additional dependency from a different component area.

3. **apb_slave_cdc.sv**: Clock-domain crossing module at
   `rtl/amba/apb/apb_slave_cdc.sv`. Even with CDC_ENABLE=0, the generate
   block still needs both modules available for sv2v.

4. **stream_config_block.sv**: Register-to-config mapping at
   `projects/components/stream/rtl/top/stream_config_block.sv`.
   Large combinational mapping logic.

5. **Transitive dependency count**: stream_top_ch8 requires ~40+ source files
   for sv2v flattening, producing 10,000+ lines of Verilog. The formal
   state space at this size makes BMC impractical even at depth 10.

### Properties that would be verified

If this module becomes tractable:

- Reset clears APB outputs (s_apb_prdata=0, s_apb_pready=0, s_apb_pslverr=0)
- Reset clears all AXI master outputs (desc/rd/wr arvalid/awvalid/wvalid=0)
- Reset clears interrupt output (stream_irq=0)
- APB address decoding correctness (routing to correct sub-block)

### Recommendation

The individual sub-modules that compose stream_top_ch8 are already formally
verified (or have proofs in progress):

- stream_core: formal/stream/stream_core/ (PROVED)
- monbus_axil_group: formal/stream/monbus_axil_group/ (PROVED)
- apbtodescr: formal/stream/apbtodescr/ (PROVED)
- scheduler, descriptor_engine, etc.: All individually proved

The top-level integration is best verified through simulation-based testing
rather than formal BMC at this design size.
