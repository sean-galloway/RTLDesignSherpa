# Generating the LiteDRAM a7ddrphy (real PHY for Vivado)

`rtl-vivado/a7ddrphy/a7ddrphy_generated.v` is the **real** Artix-7 DDR2 PHY
(LiteDRAM `A7DDRPHY`, 4359 lines, full OSERDESE2/ISERDESE2/IDELAYE2 serdes
stack). It replaces `a7ddrphy_stub.sv` in the **Vivado** fileset only. The stub
stays for verilator/cocotb (Verilator cannot simulate the Xilinx IOB serdes).

## The one thing that matters: the version cocktail

LiteDRAM/LiteX autoname their CSRs by walking Python **bytecode** (migen's
`fhdl.tracer`). migen 0.9.2 only knows `CALL_FUNCTION`/`CALL_METHOD` opcodes ->
it works on **Python <= 3.10 only**. On 3.11/3.12 every unnamed CSR throws
`ValueError: Cannot extract CSR name from code`. So the generator MUST run under
Python 3.10.

Working, reproducible recipe (uv fetches a standalone 3.10):

```bash
uv venv --python 3.10 /tmp/litex-venv310
source /tmp/litex-venv310/bin/activate
uv pip install migen "litex==2024.12" "litedram==2024.12" pyyaml
python3 bin/elaborate_a7ddrphy.py \
    --out rtl-vivado/a7ddrphy/a7ddrphy_generated.v
```

`litedram.gen` is NOT used: it always bundles LiteDRAM's own controller +
crossbar (no PHY-only mode). `elaborate_a7ddrphy.py` instead elaborates just
`A7DDRPHY` and breaks out its DFI + calibration CSR bus + clocks + pads as
top-level ports via `migen.fhdl.verilog.convert`.

## Generated interface (what the harness must drive)

- **DFI, 4-phase** (`dfi_p0..p3`): DDR2 is 4:1 on Artix-7 (nphases=4,
  DDR_clk = 4*sys -> 800 Mbps at sys=100 MHz). 13-bit address (ROW_WIDTH=13),
  32-bit wrdata/phase (dfi_databits = 2*16 for the x16 part), 4-bit mask.
  Drive from our controller at **DFI_RATE=4** via the (4-phase) adapter.
- **Calibration CSR bus**: `adr[9:0]`, `we`, `dat_w[31:0]`, `dat_r[31:0]`.
  Read/write leveling is done by FIRMWARE over UART writing these registers
  (no leveling FSM). Bridge this bus into a harness AXIL window.
- **Clocks**: `sys` (100), `sys2x` (200), `sys4x` (400), `sys4x_dqs`
  (400, 90-deg) -- harness MMCM. `IDELAYCTRL` + its 200 MHz ref are provided by
  the harness (the PHY emits 0 IDELAYCTRL instances).
- **ddram pads**: verified Nexys A7 pinout (banks 34/35), SSTL18_II /
  DIFF_SSTL18_II, dq IN_TERM=UNTUNED_SPLIT_50, SLEW=FAST.

## CSR register map

Dump the offsets for the firmware/host with (same venv):

```bash
python3 bin/elaborate_a7ddrphy.py --dump-csr-map
```
