package vexriscv.demo

import vexriscv.plugin._
import vexriscv.{plugin, VexRiscv, VexRiscvConfig}
import spinal.core._

/**
 * HIVE-C master controller core (RTL Design Sherpa, hive-serv component).
 *
 * Specification source: hive HAS ch3 Block 1 — RV32IM, 5-stage class,
 * no compressed instructions, no MMU, no caches. The native ibus/dbus
 * simple busses are wired to tightly-coupled 32 KB BRAM memories by
 * hive_c_controller. Modeled on upstream GenSmallAndProductive with the
 * M extension added via the iterative mul/div unit (area-efficient) and
 * illegal-instruction catching enabled so firmware bugs trap instead of
 * vanishing. Reset vector 0x0000_0000 matches the HAS firmware memory map.
 *
 * This file is copied into the VexRiscv source tree by
 * bin/generate_hive_cores.sh and compiled there; it lives in the hive
 * repo so the exact core configuration is pinned and reviewable.
 */
object HiveCGen extends App{
  def cpu() = new VexRiscv(
    config = VexRiscvConfig(
      plugins = List(
        new IBusSimplePlugin(
          resetVector = 0x00000000l,
          cmdForkOnSecondStage = false,
          cmdForkPersistence = false,
          prediction = NONE,
          catchAccessFault = false,
          compressedGen = false
        ),
        new DBusSimplePlugin(
          catchAddressMisaligned = false,
          catchAccessFault = false
        ),
        new CsrPlugin(CsrPluginConfig.smallest),
        new DecoderSimplePlugin(
          catchIllegalInstruction = true
        ),
        new RegFilePlugin(
          regFileReadyKind = plugin.SYNC,
          zeroBoot = false
        ),
        new IntAluPlugin,
        new SrcPlugin(
          separatedAddSub = false,
          executeInsertion = true
        ),
        new LightShifterPlugin,
        new MulDivIterativePlugin(
          genMul = true,
          genDiv = true,
          mulUnrollFactor = 1,
          divUnrollFactor = 1
        ),
        new HazardSimplePlugin(
          bypassExecute           = true,
          bypassMemory            = true,
          bypassWriteBack         = true,
          bypassWriteBackBuffer   = true,
          pessimisticUseSrc       = false,
          pessimisticWriteRegFile = false,
          pessimisticAddressMatch = false
        ),
        new BranchPlugin(
          earlyBranch = false,
          catchAddressMisaligned = false
        ),
        new YamlPlugin("hive_c.yaml")
      )
    )
  )

  SpinalVerilog(cpu())
}
