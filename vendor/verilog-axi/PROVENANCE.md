# PROVENANCE — vendor/verilog-axi

Vendored subset of Alex Forencich's Verilog AXI components: the AXI4
crossbar, used as leg C1 of the Genesys 2 fabric benchmark
(`projects/fpga-systems/Genesys2/fabric-benchmark`).

- **Upstream:** https://github.com/alexforencich/verilog-axi
- **Version:** commit `516bd5dadc3365b7f9e225d2af8fe0b8d804fe53` (2025-02-27,
  the last commit; the repo has no release tags)
- **Vendored:** 2026-10-23
- **License:** MIT (see `COPYING`; same as the repo)
- **Kept:** `rtl/axi_crossbar.v` and the seven files it instantiates
  (`axi_crossbar_addr/rd/wr.v`, `arbiter.v`, `priority_encoder.v`,
  `axi_register_rd/wr.v`), upstream `README.md`, `AUTHORS`, `COPYING`
- **Dropped:** every other component, `tb/`, `syn/`, the Python wrapper
  generators
- **Local edits:** none

**Why this repo and not its successor.** Upstream is deprecated in favour of
https://github.com/fpganinja/taxi, whose crossbar is the maintained version.
taxi is licensed CERN-OHL-S-2.0 (strongly reciprocal), which cannot be
vendored into this MIT repository; verilog-axi is MIT.

## Update procedure

```bash
rm -rf /tmp/vaxi-up && git clone https://github.com/alexforencich/verilog-axi /tmp/vaxi-up
cd vendor/verilog-axi
cp /tmp/vaxi-up/{COPYING,README.md,AUTHORS} .
for f in axi_crossbar axi_crossbar_addr axi_crossbar_rd axi_crossbar_wr arbiter \
         priority_encoder axi_register_rd axi_register_wr; do
    cp /tmp/vaxi-up/rtl/$f.v rtl/
done
# bump the commit line above, then: fabric-benchmark make sim and make ooc LEG=forencich
```
