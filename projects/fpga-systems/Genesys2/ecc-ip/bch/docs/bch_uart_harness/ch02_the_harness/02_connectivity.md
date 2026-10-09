# How The Pieces Connect

## Register path

The host talks by name, not by offset: `BchLoopDriver` wraps
`UARTAxiBridge` with `UartRegisterMap` over `bch_loop_regs_regmap.py`. The
diagram shows the path from the laptop to the three APB windows.

```mermaid
flowchart LR
    subgraph host ["Host"]
        py["python3<br/>bin/run_smoke.py"]
    end
    py -->|"/dev/ttyUSB0 115200"| uart["uart_axil_bridge"]
    uart --> axil["bridge_bch_loop_axil<br/>1x3 AXIL-APB fabric"]
    axil -->|0x00000000| win0["bch_loop_apb<br/>apb4_to_peakrdl<br/>bch_loop_regs"]
    axil -->|0x00010000| win1["bch_regs_apb<br/>axi4_intf_master_observer<br/>(AXI4 live / AXIS read-0 stub)"]
    axil -->|0x00020000| win2["obs_apb<br/>axis4_intf_observer<br/>AXIS seams"]
    win0 --> ctrl["CTRL / GO / GEN_BLOCKS / INJ_CFG<br/>BUILD_ID / SCRATCH / PROFILE / TOPOLOGY"]

    subgraph loop ["Codec loop"]
        gen["axis4_master_injector<br/>LFSR + CRC-32"]
        enc["bch_encoder_core"]
        inj["error_injector<br/>SYMBOL_WIDTH=1"]
        dec["bch_decoder_core<br/>riBM"]
        chk["axis4_slave_pattern_check"]
    end
    gen --> enc --> inj --> dec --> chk
```

The register path is the same in both flavours. The only raw addresses in the
host code are the two expansion-window bases used to attach observer register
maps: `OBS_AXI4_BASE = 0x00010000` and `OBS_AXIS_BASE = 0x00020000` in
`build-loop/host/bch_loop.py`. Those bases match
`rtl/bridges/generated/bridge_bch_loop_axil/bridge_bch_loop_axil.toml`; if a
window moves, the bridge is regenerated and the host picks it up in one
place.

## AXI4 flavour datapath

The AXI4 flavour replaces the streaming middle with a memory-to-memory job
chain across three job memories.

```mermaid
flowchart LR
    subgraph axi4 ["AXI4 flavour only"]
        m1["M1 seed memory"]
        enc["encoder"]
        m2["M2 codeword memory"]
        inj["injector on decoder R channel"]
        dec["decoder"]
        m4["M4 recovered-message memory"]
    end
    m1 --> enc --> m2 --> inj --> dec --> m4
```

## Clock and reset

Clock and reset come from `bch_loop_genesys2_top`: the 200 MHz LVDS system
clock passes through `IBUFDS` and an `MMCME2_BASE` with `CLKFBOUT_MULT_F = 6`
and `CLKOUT0_DIVIDE_F = 12`, giving a 100 MHz harness clock. The Nexys A7 top
runs the same 100 MHz directly. That frequency was chosen because the BCH
loop and the UART divisor both close timing comfortably at 100 MHz on the
k325t-2, and it keeps the AXIS and AXI4 flavours interchangeable from the
host's point of view.
