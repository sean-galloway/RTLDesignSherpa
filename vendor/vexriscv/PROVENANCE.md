# PROVENANCE — vendor/vexriscv

Generated netlist for the HIVE-C master controller core (RTL Design Sherpa
hive-serv component).

- **Upstream:** https://github.com/SpinalHDL/VexRiscv
- **Version:** baf7dc82f855eddaf5b0a20a6802c526f127e38a (clone commit baf7dc82f855eddaf5b0a20a6802c526f127e38a)
- **Configuration:** `projects/components/compute-eng-ip/hive-serv/bin/vexriscv/HiveCGen.scala`
  (RV32IM, no compressed, no MMU, no caches, machine CSRs, reset 0x0000_0000)
- **Generated:** 2026-10-13 by `hive-serv/bin/generate_hive_cores.sh`
- **Toolchain note:** upstream `project/build.properties` (sbt 1.6.0) is
  overridden to sbt 1.10.7 for Java 21 compatibility; see the
  header comment in the generator script for why the 1.0.1 tag is not used.
- **Netlist sha256:** d172750ead79fdfd9cb2407ffac9d08cbd6e5045571053ded5bcc72e9168cafb
- **License:** MIT (VexRiscv, SpinalHDL; see upstream COPYING at the tag above)

## Regenerate

```bash
projects/components/compute-eng-ip/hive-serv/bin/generate_hive_cores.sh --force
```

Requires java + sbt on PATH. The emitted Verilog is checked in so simulation,
lint, and CI do not need the Scala toolchain — regeneration is a deliberate,
reviewed act.
