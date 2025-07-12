# axi_write_splitter_scoreboard.py

This module provides the AXI Write Splitter Scoreboard for tracking and verifying AXI write transaction splits. The scoreboard handles the more complex write transaction flow with three-channel coordination (AW → W → B) and ensures proper data distribution and response consolidation.

## Purpose

The write splitter scoreboard serves as the verification engine for AXI write splitter functionality by:
- Tracking write address, data, and response phases independently
- Correlating split write transactions with original requests
- Verifying write data distribution across split boundaries
- Monitoring write response consolidation
- Ensuring proper WLAST signal handling at split boundaries
- Providing comprehensive write-specific error detection and reporting

## Key Features

### Three-Channel Write Flow Management
- **Write Address (AW) Phase**: May be split across boundaries
- **Write Data (W) Phase**: Data must be properly distributed across splits
- **Write Response (B) Phase**: Responses must be properly consolidated

### Enhanced Write Transaction Tracking
- Independent tracking of address, data, and response phases
- Write data distribution verification
- WLAST verification for split boundaries
- Single response per original transaction validation
- Write strobe pattern verification

## Core Class: AxiWriteSplitterScoreboard

### Initialization

```python
def __init__(self, alignment_mask=0xFFF, log=None, component_name="AXI_WR_SPLITTER_SB",
             id_width=8, addr_width=32, data_width=32, user_width=1)
```

**Parameters:**
- `alignment_mask`: Boundary alignment mask (default: 0xFFF for 4KB boundaries)
- `log`: Logger instance for debug output
- `component_name`: Component name for logging
- `id_width`: Transaction ID width in bits
- `addr_width`: Address width in bits
- `data_width`: Data width in bits
- `user_width`: User signal width in bits

**Setup Actions:**
- Creates write-specific field configurations for AW, W, and B channels
- Initializes three-phase transaction tracking dictionaries
- Sets up write data distribution tracking
-