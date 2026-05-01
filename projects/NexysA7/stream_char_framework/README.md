# stream_char_framework

Shared instrumentation library for the FPGA characterization flows under
`projects/NexysA7/flows-*`. Each flow is a complete, self-contained build
(its own Makefile, RTL top, sweep CSVs, plots, doc); each one pulls the
hooks below in via `$FRAMEWORK_ROOT`.

## What lives here

```
stream_char_framework/
├── rtl/
│   ├── axi_response_delay.sv           pipelined memory-controller delay queue
│   ├── axil_decode_5s.sv               AXIL 5-slave decoder
│   ├── axil2apb.sv                     AXIL → APB bridge
│   ├── harness_csr.sv                  CSRs: kick-burst, delay, cycle timer
│   ├── desc_ram.sv                     descriptor BRAM
│   ├── debug_sram.sv                   monitor-trace BRAM
│   ├── led_status_driver.sv            CDC-isolated LED driver
│   ├── seven_seg_4digit.sv             7-segment display
│   └── filelists/
│       └── instrumentation.f           pulls all of the above in
│
├── host/
│   └── plot_results.py                 DUT-agnostic CSV → PNG plotter
│
└── docs_template/                      (TBD: corporate styles / title page /
                                         logo for per-flow report generators)
```

## What does NOT live here

- DUT-specific RTL (any flow's top, harness, cfg pkg).
- DUT-specific host scripts (descriptor builders, register maps).
- Flow-specific characterization writeups, plots, sweep CSVs, bitstreams.

Anything that the next DUT swap (Vivado MCDMA, Vivado bridge, …) will
need to override goes in the per-flow directory, not here.

## Used by

- `projects/NexysA7/flows-stream-bridge/`           in-house STREAM + in-house bridge
- `projects/NexysA7/flows-vivado-mcdma/`            Vivado MCDMA + in-house bridge (pending)
- `projects/NexysA7/flows-stream-vivado-bridge/`    in-house STREAM + Vivado bridge (future)
- `projects/NexysA7/flows-vivado-mcdma-vivado-bridge/`  Vivado × Vivado (future)

Each flow's Makefile exports `FRAMEWORK_ROOT` so RTL filelists and host
scripts can resolve shared modules with one path.
