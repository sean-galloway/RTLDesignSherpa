// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: 2026 sean galloway
//
// Package: ref_cva6_cfg_pkg
// Purpose:
//   The CVA6 configuration the reference rig hands to the vendored write-back
//   std_nbdcache (cache-ip common-ip TASK-003). It is upstream's
//   cv64a6_imafdc_sv39_wb_config_pkg (vendor/cva6-dcache/core/include) with
//   the fields the cache reads changed to the pair rig's point, so the
//   blocking reference matches amber and jet set for set:
//     DcacheByteSize 32 KB, DcacheSetAssoc 4, DcacheLineWidth 512 (64 B)
//     AxiDataWidth 64, AxiIdWidth 8, AxiUserWidth 1 (the rig's AXI4 memory)
//     DcacheIdWidth 1, one cached region covering the rig memory
//   Everything the core-side configuration carries that the cache does not
//   read (ISA extensions, PMP, triggers, branch prediction, ...) is left at
//   upstream's values. std_nbdcache reads: AxiDataWidth, AxiIdWidth,
//   DcacheIdWidth, DCACHE_{INDEX,TAG,LINE,OFFSET}_WIDTH, DCACHE_NUM_WORDS,
//   DCACHE_SET_ASSOC(_WIDTH), MaxOutstandingStores, PLEN, XLEN (all derived
//   by build_config_pkg::build_config from the user fields below).
//
// Author: sean galloway
// Created: 2026-11-11
package ref_cva6_cfg_pkg;

  localparam config_pkg::cva6_user_cfg_t cva6_user_cfg = '{
      XLEN: unsigned'(64),
      VLEN: unsigned'(64),
      FpgaEn: bit'(1),
      FpgaAlteraEn: bit'(0),
      TechnoCut: bit'(0),
      SuperscalarEn: bit'(0),
      ALUBypass: bit'(0),
      NrCommitPorts: unsigned'(2),
      AxiAddrWidth: unsigned'(64),
      AxiDataWidth: unsigned'(64),
      AxiIdWidth: unsigned'(8),
      AxiUserWidth: unsigned'(1),
      MemTidWidth: unsigned'(2),
      NrLoadBufEntries: unsigned'(2),
      RVF: bit'(1),
      RVD: bit'(1),
      XF16: bit'(0),
      XF16ALT: bit'(0),
      XF8: bit'(0),
      RVA: bit'(1),
      RVB: bit'(1),
      ZKN: bit'(0),
      RVV: bit'(0),
      RVC: bit'(1),
      RVH: bit'(0),
      RVZCB: bit'(1),
      RVZCMT: bit'(0),
      RVZCMP: bit'(0),
      XFVec: bit'(0),
      CvxifEn: bit'(1),
      CoproType: config_pkg::COPRO_NONE,
      RVZiCond: bit'(1),
      RVZiCbom: bit'(0),
      RVZicntr: bit'(1),
      RVZihpm: bit'(1),
      NrScoreboardEntries: unsigned'(8),
      PerfCounterEn: bit'(1),
      MmuPresent: bit'(1),
      RVS: bit'(1),
      RVU: bit'(1),
      SoftwareInterruptEn: bit'(1),
      HaltAddress: 64'h800,
      ExceptionAddress: 64'h808,
      RASDepth: unsigned'(2),
      BTBEntries: unsigned'(32),
      BPType: config_pkg::BHT,
      BHTEntries: unsigned'(128),
      BHTHist: unsigned'(3),
      DmBaseAddress: 64'h0,
      TvalEn: bit'(1),
      DirectVecOnly: bit'(0),
      NrPMPEntries: unsigned'(8),
      PMPCfgRstVal: {64{64'h0}},
      PMPAddrRstVal: {64{64'h0}},
      PMPEntryReadOnly: 64'd0,
      PMPNapotEn: bit'(1),
      NOCType: config_pkg::NOC_TYPE_AXI4_ATOP,
      NrNonIdempotentRules: unsigned'(2),
      NonIdempotentAddrBase: 1024'({64'b0, 64'b0}),
      NonIdempotentLength: 1024'({64'b0, 64'b0}),
      NrExecuteRegionRules: unsigned'(3),
      ExecuteRegionAddrBase: 1024'({64'h8000_0000, 64'h1_0000, 64'h0}),
      ExecuteRegionLength: 1024'({64'h40000000, 64'h10000, 64'h1000}),
      NrCachedRegionRules: unsigned'(1),
      CachedRegionAddrBase: 1024'({64'h0}),
      CachedRegionLength: 1024'({64'h8_0000}),   // the rig's 512 KB memory
      MaxOutstandingStores: unsigned'(7),
      DebugEn: bit'(1),
      Sdtrig: bit'(0),
      SdtrigMcontrol6: bit'(0),
      SdtrigMcontrol6ExecAddr: bit'(0),
      SdtrigMcontrol6ExecData: bit'(0),
      SdtrigMcontrol6Store: bit'(0),
      SdtrigMcontrol6LoadAddr: bit'(0),
      SdtrigMcontrol6LoadData: bit'(0),
      SdtrigIcount: bit'(0),
      SdtrigEtrigger: bit'(0),
      SdtrigItrigger: bit'(0),
      SdtrigNrTriggers: int'(4),
      SdtrigTriggerChaining: bit'(0),
      SdtrigSupportedActions: 2'b01,
      SdtrigSupportedMatch: 10'b00_0000_0001,
      SdtrigSupportTextra: bit'(0),
      AxiBurstWriteEn: bit'(0),
      IcacheByteSize: unsigned'(16384),
      IcacheSetAssoc: unsigned'(4),
      IcacheLineWidth: unsigned'(128),
      DCacheType: config_pkg::WB,
      DcacheByteSize: unsigned'(32768),
      DcacheSetAssoc: unsigned'(4),
      DcacheLineWidth: unsigned'(512),
      DcacheFlushOnFence: bit'(0),
      DcacheFlushOnFenceI: bit'(1),
      DcacheInvalidateOnFlush: bit'(0),
      DcacheEccEnable: bit'(0),
      DcacheEccScrubberEnable: bit'(0),
      DataUserEn: unsigned'(0),
      WtDcacheWbufDepth: int'(8),
      FetchUserWidth: unsigned'(64),
      FetchUserEn: unsigned'(0),
      InstrTlbEntries: int'(16),
      DataTlbEntries: int'(16),
      UseSharedTlb: bit'(0),
      SvnapotEn: bit'(0),
      SharedTlbDepth: int'(64),
      NrLoadPipeRegs: int'(1),
      NrStorePipeRegs: int'(0),
      DcacheIdWidth: int'(1)
  };

  localparam config_pkg::cva6_cfg_t CVA6Cfg = build_config_pkg::build_config(cva6_user_cfg);

endpackage : ref_cva6_cfg_pkg
