# apbtodescr Tests

Tests for the APB-to-Descriptor router module (`apbtodescr.sv`).

## Test Coverage

### test_basic_all_channels
Tests basic write to all 8 channels sequentially:
- Address decode (BASE+0x00 through BASE+0x1C)
- One-hot valid generation
- Descriptor address routing (32-bit → 64-bit zero-extend)

### test_backpressure_single
Tests single channel with descriptor engine back-pressure:
- Descriptor engine ready = 0
- APB transaction blocks correctly
- Completes when ready = 1
- Cycle count includes stall

### test_backpressure_multiple
Tests multiple channels with varying back-pressure:
- Different channels with different stall durations
- Sequential back-pressure scenarios

### test_errors
Tests error cases:
- Out-of-range address (beyond CH7)
- Read request (not supported)
- Verify error flag asserted

### test_rapid_fire
Tests rapid sequential writes:
- Multiple channels in quick succession
- Minimal inter-transaction delay
- Verify no crosstalk

## Running Tests

### Run all tests
```bash
cd projects/components/stream/dv/tests/fub_tests/apbtodescr
pytest test_apbtodescr.py -v
```

### Run specific test
```bash
pytest test_apbtodescr.py::test_apbtodescr -v
```

### Run with waveforms
```bash
WAVES=1 pytest test_apbtodescr.py -v
```

### View waveforms
```bash
gtkwave local_sim_build/test_apbtodescr_*/dump.vcd
```

## Expected Results

All tests should pass with output similar to:
```
test_basic_all_channels ...................... PASSED
test_backpressure_single ..................... PASSED
test_backpressure_multiple ................... PASSED
test_errors .................................. PASSED
test_rapid_fire .............................. PASSED
```

## Test Parameters

Default configuration:
- ADDR_WIDTH = 32
- DATA_WIDTH = 32
- NUM_CHANNELS = 8
- BASE_ADDR = 0x00000000

## Verification Points

| Test | Verifies |
|------|----------|
| Basic | Address decode, channel routing |
| Back-pressure | FSM stall handling, cycle counting |
| Errors | Error detection and reporting |
| Rapid-fire | Sequential operation, no state leakage |

## Integration Notes

This module is designed to work with:
- **Upstream:** PeakRDL APB slave (CMD/RSP interface)
- **Downstream:** descriptor_engine APB ports (8 channels)

See `projects/components/stream/docs/stream_spec/ch02_blocks/00_apbtodescr.md` for complete documentation.
