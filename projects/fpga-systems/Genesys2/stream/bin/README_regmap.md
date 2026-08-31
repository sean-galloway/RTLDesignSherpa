# harness_csr registers come from RDL

`regs/harness_csr.rdl` is the single source for the harness CSR **map**.
Regenerate with:

    cd $REPO_ROOT && source env_python
    python3 bin/peakrdl_generate.py \
        projects/fpga-systems/Genesys2/stream/regs/harness_csr.rdl \
        --regmap --regmap-output \
        projects/fpga-systems/Genesys2/stream/rtl/harness_csr_regmap.py

`bin/gen_harness_regmap.py` — a hand-maintained Python table — is gone. It
drifted from the RTL and declared ten registers `harness_csr.sv` does not
decode, which three host tools then read as zeros off a running board.

The RTL is still hand-written. `harness_csr.sv` has self-clearing pulse bits, a
soft-reset latch and a 9-bit decode that PeakRDL regblock cannot express; those
few one-offs are deliberate. What binds map to hardware is a test, not care:
`bin/tests/test_harness_regmap.py::test_every_regmap_register_is_actually_decoded`
parses the decode's case labels and asserts every register in the map has one.
