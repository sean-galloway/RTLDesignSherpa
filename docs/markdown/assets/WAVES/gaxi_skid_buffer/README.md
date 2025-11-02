# GAXI Skid Buffer Waveforms

This directory contains timing diagram assets for the `gaxi_skid_buffer` module.

## Expected Files

The following waveforms should be generated from `val/amba/test_gaxi_wavedrom_example.py`:

- `zero_latency_bypass_001.json` - Write to empty buffer (zero-latency bypass)
- `burst_write_full_001.json` - Burst writes until buffer full (backpressure)
- `simultaneous_rdwr_001.json` - Simultaneous read/write (pass-through)
- `burst_read_empty_001.json` - Burst reads until empty
- `fill_then_drain_001.json` - Complete fill then drain pattern
- `alternating_rdwr_001.json` - Alternating read/write operations

## Generating Waveforms

Run the WaveDrom test to generate JSON files:

```bash
env ENABLE_WAVEDROM=1 pytest val/amba/test_gaxi_wavedrom_example.py::test_gaxi_comprehensive_wavedrom -v
```

Then copy the generated files:

```bash
cp val/amba/local_sim_build/test_gaxi_skid_buffer_w32_d4_default_wd/*.json docs/markdown/assets/WAVES/gaxi_skid_buffer/
```

## Optional: Generate PNG/SVG

If desired, PNG and SVG files can be generated from the JSON using WaveDrom rendering tools.
