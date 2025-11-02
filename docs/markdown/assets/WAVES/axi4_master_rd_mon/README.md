# AXI4 Master Read Monitor Waveforms

This directory contains timing diagram assets for the `axi4_master_rd_mon` module.

## Status

**Infrastructure:** ✅ Test framework complete
**Signal Binding:** ✅ Using `signal_map` for AXI4 protocols
**Waveforms:** ✅ **WORKING** - 3 waveforms successfully generated
**Test:** ✅ PASSING

## Generated Waveforms

### Primary Waveform

**single_beat_read_001.json** - Complete single-beat read transaction
- Shows all three phases of a read operation:
  1. **AR Channel**: Address request handshake (arvalid → arready)
  2. **R Channel**: Read data response (rvalid with data, rid, rlast, rresp)
  3. **Monitor Bus**: Monitor packet generation (monbus_valid/ready)
- Demonstrates timing relationships between all channels
- ID matching between AR and R channels (0xD5)
- Single-beat transaction (arlen=0, rlast asserted immediately)

### Individual Channel Waveforms (for reference)

These were generated during development to isolate specific behaviors:
- **ar_handshake_001.json** - AR channel handshake only
- **r_response_001.json** - R channel response only
- **monbus_packet_001.json** - Monitor bus packet only

## Key Lesson Learned

**CRITICAL**: When specifying signals like "AR" or "AW", always use the actual interface signals (`m_axi_arvalid`, `m_axi_arready`, etc.), not the monitor's internal FUB signals (`fub_axi_*`).

The monitor's FUB interface is the monitor's output (where it acts as a slave), while the `m_axi_*` signals are the actual AXI master interface being monitored. The FUB side signals like `fub_axi_arready` are often static (always high), so constraints looking for transitions won't match.

### Problem

The constraint solver is not successfully matching AXI4 handshake patterns. The test uses:

1. **AR Channel Constraint**: Detect when both `arvalid` and `arready` are high (handshake)
2. **R Channel Constraint**: Detect when `rvalid`, `rready`, and `rlast` are all high (handshake)

However, the solver reports:
```
Failed constraints: ['fub_axi_ar_handshake', 'fub_axi_r_handshake']
```

### Root Cause

From the simulation logs, we can see the transactions ARE occurring:
- **AR handshake**: 440-450ns (arvalid asserts at 440ns, handshake completes at 450ns)
- **R handshake**: 500-515ns (rvalid asserts at 500ns, handshake completes at 510-515ns)

The constraint solver is attempting to match but failing. Possible reasons:

1. **CONCURRENT relation** may not be working as expected for detecting multiple signals high at the same time
2. **SEQUENCE relation** with static patterns may have timing issues
3. The solver may not be correctly sampling the signals during the handshake window

### Attempted Solutions (All Failed)

1. **SEQUENCE with two transitions** (APB pattern): `arvalid(0→1) → arready(0→1)`
   - Result: Failed to match

2. **SEQUENCE with transitions + static patterns**: `arvalid(0→1) → arvalid(=1) → arready(=1)`
   - Result: Failed to match

3. **CONCURRENT with static patterns**: Both signals high simultaneously
   - Result: Failed to match

4. **Single transition test**: Just `arvalid(0→1)` alone
   - Result: Failed to match

5. **Reset transition test**: `aresetn(0→1)` (known to occur)
   - Result: Failed to match

6. **With add_interface()**: Logical name mapping like APB
   - Result: Failed to match

7. **Without add_interface()**: Direct DUT signal names
   - Result: Failed to match

8. **With field_config**: Matching APB initialization
   - Result: Failed to match

9. **Library functions from `tbclasses/wavedrom_user/axi4.py`**: Pre-built patterns
   - Result: Failed to match

### Requirements

Per user specification, waveforms MUST:
- Use constraint-based pattern detection (not manual JSON)
- Capture real signal timing from simulation
- Fail if RTL changes break expected patterns

This is critical for regression testing.

## Signal Groups

The waveforms show the following signal groups:

### Clock and Reset
- `aclk` - AXI clock
- `aresetn` - Active-low asynchronous reset

### AR Channel (Read Address) - Master Interface
- `m_axi_arvalid` - Address read valid
- `m_axi_arready` - Address read ready
- `m_axi_arid` - Read transaction ID
- `m_axi_araddr` - Read address
- `m_axi_arlen` - Burst length (0 for single-beat)

### R Channel (Read Data) - Master Interface
- `m_axi_rvalid` - Read data valid
- `m_axi_rready` - Read data ready
- `m_axi_rid` - Read response ID (matches arid)
- `m_axi_rdata` - Read data
- `m_axi_rlast` - Last beat indicator
- `m_axi_rresp` - Read response (OKAY, SLVERR, DECERR)

### Monitor Bus - Monitor Output
- `monbus_valid` - Monitor packet valid
- `monbus_ready` - Monitor packet ready

**Note**: The waveforms show the `m_axi_*` signals (the actual AXI master interface being monitored), not the `fub_axi_*` signals (monitor's internal FUB interface).

## Waveform Details

### Single-Beat Read Transaction Flow

The `single_beat_read_001.json` waveform demonstrates:

1. **Address Phase** (~440-450ns):
   - Master asserts `arvalid` with address 0x1000 and ID 0xD5
   - Slave asserts `arready` after 1 cycle
   - Handshake completes

2. **Data Phase** (~500-510ns):
   - Slave asserts `rvalid` with data 0x10000000
   - `rid` matches the request ID (0xD5)
   - `rlast` asserted (single-beat transaction)
   - `rresp` = OKAY (0x0)
   - Master already has `rready` high

3. **Monitor Packet** (~595ns):
   - Monitor generates completion packet on `monbus_valid`
   - Packet contains transaction summary
   - Downstream accepts with `monbus_ready`

## Implementation Notes

1. ✅ Constraint-based waveform generation (not manual JSON)
2. ✅ Captures real signal timing from simulation
3. ✅ Test fails if RTL changes break expected patterns
4. ✅ Uses `signal_map` to explicitly bind correct signals
5. ✅ Monitors actual AXI interface (`m_axi_*`), not internal FUB interface

## Fixed: Signal Pattern Conflict

**RESOLVED:** The signal conflict issue has been fixed by adding `signal_map` support to the `axi4_read_wavedrom` protocol.

### Problem
The automatic signal discovery pattern included BOTH AR and R channel fields:
```python
'multi_sig_true': [
    '{prefix}ar{field_name}',  # Matches: fub_axi_arid, fub_axi_araddr, etc.
    '{prefix}r{field_name}',   # Matches: fub_axi_rid, fub_axi_rdata, etc.
]
```

This caused `field_id_sig` to match BOTH `fub_axi_arid` AND `fub_axi_rid`, creating a conflict.

### Solution
Added `signal_map` support to `signal_mapping_helper.py`:
```python
ar_signal_map = {
    'arvalid': 'fub_axi_arvalid',
    'arready': 'fub_axi_arready',
    'rvalid': 'fub_axi_rvalid',
    'rready': 'fub_axi_rready',
    'addr': 'fub_axi_araddr',  # Explicitly AR channel
    'id': 'fub_axi_arid',      # Explicitly AR channel (not rid!)
    'len': 'fub_axi_arlen',
    # ... other AR fields
}
wave_solver.auto_bind_signals('axi4_read', signal_map=ar_signal_map, field_config=ar_config)
```

**Result:** ✅ All 14 signals successfully bound with no conflicts

## Remaining Issue: Constraint Matching

With signal binding now working, we're back to the original constraint solver issue.

**Current Status:**
- ✅ All 14 signals successfully bound
- ✅ Sampling window configured correctly (380-720ns)
- ✅ Transactions occurring in RTL (arvalid @ 440ns, arready @ 450ns)
- ❌ Constraint solver reports 0 pattern matches

**Constraint Definition:**
```python
ar_constraint = TemporalConstraint(
    name="axi4_ar_transaction",
    events=[
        TemporalEvent("arvalid_start", SignalTransition("fub_axi_arvalid", 0, 1)),
        TemporalEvent("arready_response", SignalTransition("fub_axi_arready", 0, 1))
    ],
    temporal_relation=TemporalRelation.SEQUENCE,
    ...
)
```

**Next Steps:**
1. Debug TemporalConstraintSolver to understand why it's not detecting the transitions
2. Compare with working APB/GAXI tests to identify differences
3. Add debug instrumentation to see what signals the solver is actually sampling

## Generating Waveforms (When Fixed)

Run the WaveDrom test:

```bash
env ENABLE_WAVEDROM=1 pytest "val/amba/test_axi4_master_rd_mon.py::test_axi4_master_rd_mon_wavedrom" -v
```

## Test File Location

- Test: `/val/amba/test_axi4_master_rd_mon.py`
- WaveDrom test function: `axi4_master_rd_mon_wavedrom_test`
- Infrastructure: `CocoTBFramework/components/wavedrom/*`
- User library: `CocoTBFramework/tbclasses/wavedrom_user/axi4.py`

## References

- APB wavedrom tests (working reference): `val/amba/test_apb_slave.py`
- Constraint solver: `CocoTBFramework/components/wavedrom/constraint_solver.py`
- WaveDrom requirements: `bin/CocoTBFramework/tbclasses/wavedrom_user/WAVEDROM_REQUIREMENTS.md`
