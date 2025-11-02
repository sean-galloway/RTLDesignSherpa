# APB Master Waveforms

This directory contains timing diagram assets for the `apb_master` module.

## Expected Files

The following waveforms should be generated from `val/amba/test_apb_master.py`:

- `apb_write_sequence_001.json`
- `apb_read_sequence_001.json`
- `apb_back_to_back_writes_001.json`
- `apb_back_to_back_reads_001.json`
- `apb_write_to_read_001.json`
- `apb_read_to_write_001.json`
- `apb_error_001.json`

## Generating Waveforms

Run the WaveDrom test to generate JSON files:

```bash
env ENABLE_WAVEDROM=1 pytest "val/amba/test_apb_master.py::test_apb_master_wavedrom[32-32-6-6]" -v
```

Then copy the generated files:

```bash
cp val/amba/local_sim_build/test_apb_master_aw032_dw032_mq006_sq006_wd/*.json docs/markdown/assets/WAVES/apb_master/
```
