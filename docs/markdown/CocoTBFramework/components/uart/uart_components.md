<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

**[← Back to Components Index](../components_index.md)** | **[Main Index](../components_index.md)**

# UART BFM Components

**Package:** `bin/CocoTBFramework/components/uart/`
**Last Updated:** 2025-11-09

---

## Overview

The UART BFM (Bus Functional Model) package provides CocoTB-based verification components for UART protocol testing. These components implement the standard 8N1 UART protocol (8 data bits, no parity, 1 stop bit) with configurable baud rates.

### Package Contents

| Component | Purpose | Direction |
|-----------|---------|-----------|
| **UARTMaster** | UART transmitter | TX (sends data) |
| **UARTMonitor** | UART receiver monitor | RX (captures data) |
| **UARTSlave** | UART responder | RX/TX (echo, respond) |

---

## UARTMaster

### Purpose

Transmits UART data for stimulating DUT UART receivers. Used to drive commands and test data into UART-based designs.

### Features

- Configurable baud rate (via `clks_per_bit`)
- Automatic start/stop bit generation
- String and byte transmission
- Non-blocking async transmission
- Transaction logging

### Usage

```python
from CocoTBFramework.components.uart import UARTMaster

class MyTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(dut)

        # Initialize UART master
        self.uart_tx = UARTMaster(
            entity=dut,
            title="UART_TX",
            signal_name="i_uart_rx",  # DUT input signal name
            clock=dut.aclk,
            clks_per_bit=868,  # 100 MHz / 115200 baud
            direction='TX',
            log=self.log
        )

    async def send_command(self, cmd):
        """Send UART command string"""
        await self.uart_tx.send_string(cmd)

    async def send_byte(self, byte_val):
        """Send single byte"""
        await self.uart_tx.send_byte(byte_val)
```

### API

#### Constructor
```python
UARTMaster(
    entity,           # CocoTB DUT entity
    title,            # String for logging (e.g., "UART_TX")
    signal_name,      # DUT signal name (e.g., "i_uart_rx")
    clock,            # Clock signal handle
    clks_per_bit,     # Clocks per UART bit
    direction='TX',   # Direction string (for logging)
    log=None          # Logger instance (optional)
)
```

#### Methods

**`async send_byte(data: int)`**
- Transmits single byte over UART
- `data`: 8-bit value (0-255)
- Automatically adds start/stop bits
- Non-blocking (awaitable)

**`async send_string(text: str)`**
- Transmits ASCII string over UART
- `text`: String to transmit
- Sends each character sequentially
- Non-blocking (awaitable)

### Timing

**Per-Byte Transmission Time:**
```
T_byte = clks_per_bit * 10 clock cycles
       = (1 start) + (8 data) + (1 stop) bits

Example (115200 baud, 100 MHz clock):
clks_per_bit = 868
T_byte = 868 * 10 = 8680 clocks = 86.8 µs
```

### Example

```python
@cocotb.test()
async def test_uart_commands(dut):
    tb = UARTBridgeTB(dut)
    await tb.setup_clocks_and_reset()

    # Send write command
    await tb.uart_tx.send_string("W 1000 DEADBEEF\n")

    # Wait for response
    await tb.wait_clocks('clk', 100000)

    # Check UART response via monitor
    # (see UARTMonitor section)
```

---

## UARTMonitor

### Purpose

Monitors UART output from DUT transmitters. Captures transmitted data for verification and analysis.

### Features

- Configurable baud rate (via `clks_per_bit`)
- Automatic start/stop bit detection
- Queue-based transaction capture (`_recvQ`)
- Transaction logging
- Data validation

### Usage

```python
from CocoTBFramework.components.uart import UARTMonitor

class MyTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(dut)

        # Initialize UART monitor
        self.uart_rx_monitor = UARTMonitor(
            entity=dut,
            title="UART_RX_MON",
            signal_name="o_uart_tx",  # DUT output signal name
            clock=dut.aclk,
            clks_per_bit=868,  # 100 MHz / 115200 baud
            direction='RX',
            log=self.log
        )

    async def check_response(self, expected_str):
        """Verify UART response"""
        # Wait for data
        await self.wait_clocks('clk', 10000)

        # Check queue
        if len(self.uart_rx_monitor._recvQ) >= len(expected_str):
            received = ""
            for _ in range(len(expected_str)):
                pkt = self.uart_rx_monitor._recvQ.popleft()
                received += chr(pkt.data)

            assert received == expected_str, f"Expected '{expected_str}', got '{received}'"
            return True
        return False
```

### API

#### Constructor
```python
UARTMonitor(
    entity,           # CocoTB DUT entity
    title,            # String for logging (e.g., "UART_RX_MON")
    signal_name,      # DUT signal name (e.g., "o_uart_tx")
    clock,            # Clock signal handle
    clks_per_bit,     # Clocks per UART bit
    direction='RX',   # Direction string (for logging)
    log=None          # Logger instance (optional)
)
```

#### Attributes

**`_recvQ`** - `collections.deque`
- Queue of received UART packets
- Access with `.popleft()` to retrieve oldest packet
- Each packet is a `UARTPacket` object

**`UARTPacket` Structure:**
```python
class UARTPacket:
    data: int      # 8-bit received data
    timestamp: int # Simulation time (ns)
```

#### Methods

Monitor runs automatically in background. Access received data via `_recvQ`.

**Common Patterns:**
```python
# Check if data available
if len(self.uart_rx_monitor._recvQ) > 0:
    pkt = self.uart_rx_monitor._recvQ.popleft()
    byte_val = pkt.data
    timestamp = pkt.timestamp

# Clear queue
self.uart_rx_monitor._recvQ.clear()

# Collect string response
response = ""
while len(self.uart_rx_monitor._recvQ) > 0:
    pkt = self.uart_rx_monitor._recvQ.popleft()
    response += chr(pkt.data)
```

### Example

```python
@cocotb.test()
async def test_uart_echo(dut):
    tb = UARTTestbench(dut)
    await tb.setup_clocks_and_reset()

    # Clear any stale data
    tb.uart_rx_monitor._recvQ.clear()

    # Send command
    await tb.uart_tx.send_string("HELLO\n")

    # Wait for response
    await tb.wait_clocks('clk', 50000)

    # Collect response
    response = ""
    while len(tb.uart_rx_monitor._recvQ) > 0:
        pkt = tb.uart_rx_monitor._recvQ.popleft()
        response += chr(pkt.data)
        tb.log.debug(f"Received: 0x{pkt.data:02X} ({chr(pkt.data)})")

    # Verify
    assert response == "HELLO\n", f"Echo failed: {response}"
```

---

## UARTSlave

### Purpose

Simulates UART slave device that can respond to received commands. Useful for testing UART masters.

### Features

- Receives commands via UART
- Generates responses
- Configurable response patterns
- Automatic echo mode
- Custom response callbacks

### Usage

```python
from CocoTBFramework.components.uart import UARTSlave

class MyTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(dut)

        # Initialize UART slave
        self.uart_slave = UARTSlave(
            entity=dut,
            title="UART_SLAVE",
            rx_signal_name="o_uart_tx",  # Receive from DUT TX
            tx_signal_name="i_uart_rx",  # Transmit to DUT RX
            clock=dut.aclk,
            clks_per_bit=868,
            log=self.log,
            echo_mode=True  # Echo received bytes
        )

    async def setup_custom_response(self):
        """Configure custom response callback"""
        async def custom_handler(byte_val):
            if byte_val == ord('?'):
                return "READY\n"
            elif byte_val == ord('V'):
                return "VERSION 1.0\n"
            return None  # No response

        self.uart_slave.set_response_handler(custom_handler)
```

### API

#### Constructor
```python
UARTSlave(
    entity,           # CocoTB DUT entity
    title,            # String for logging
    rx_signal_name,   # DUT TX signal name (slave receives from)
    tx_signal_name,   # DUT RX signal name (slave transmits to)
    clock,            # Clock signal handle
    clks_per_bit,     # Clocks per UART bit
    log=None,         # Logger instance
    echo_mode=False   # Echo received bytes back
)
```

#### Methods

**`set_response_handler(callback)`**
- Set custom response callback
- `callback`: async function(byte) -> str or None
- Called for each received byte
- Return string to transmit response, None for no response

**`enable_echo_mode()`**
- Enable automatic echo of received bytes

**`disable_echo_mode()`**
- Disable automatic echo

### Example

```python
@cocotb.test()
async def test_uart_slave(dut):
    tb = UARTTestbench(dut)
    await tb.setup_clocks_and_reset()

    # Configure slave responses
    async def command_handler(byte_val):
        if byte_val == ord('R'):
            return "READ_OK\n"
        elif byte_val == ord('W'):
            return "WRITE_OK\n"
        return None

    tb.uart_slave.set_response_handler(command_handler)

    # Master sends command
    # Slave automatically responds based on handler
```

---

## Protocol Details

### UART 8N1 Protocol

**Frame Format:**

```wavedrom
{ signal: [
  { name: "UART Frame", wave: "x0.2345678.1x", data: ["Start","D0","D1","D2","D3","D4","D5","D6","D7","Stop"] }
],
  head: { text: "UART 8N1 Frame: Start (0) + 8 Data (LSB first) + Stop (1) = 10 bits" }
}
```

| Bit | Name | Description |
|-----|------|-------------|
| 1 | Start | Always 0 |
| 2-9 | D0-D7 | Data (LSB first) |
| 10 | Stop | Always 1 |

*Total: 10 bits per byte*

**Bit Timing:**
```
Bit Duration = clks_per_bit clock cycles

Baud Rate = Clock_Frequency / clks_per_bit

Common Baud Rates:
- 9600:   clks_per_bit = 10417 (100 MHz clock)
- 115200: clks_per_bit = 868   (100 MHz clock)
- 230400: clks_per_bit = 434   (100 MHz clock)
```

### Timing Constraints

**Minimum Requirements:**
- Clock frequency >> baud rate (at least 16x recommended)
- Stable clock during transmission
- Proper CDC for async UART inputs

**Typical Timing:**
| Baud Rate | Bit Time | Byte Time |
|-----------|----------|-----------|
| 9600 | 104.2 µs | 1.042 ms |
| 115200 | 8.68 µs | 86.8 µs |
| 230400 | 4.34 µs | 43.4 µs |

---

## Integration Examples

### Complete UART Bridge Testbench

```python
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.uart import UARTMaster, UARTMonitor

class UARTBridgeTB(TBBase):
    """Testbench for UART to AXI4-Lite bridge"""

    def __init__(self, dut):
        super().__init__(dut)

        # UART master (sends commands to bridge)
        self.uart_tx = UARTMaster(
            entity=dut,
            title="UART_TX",
            signal_name="i_uart_rx",
            clock=dut.aclk,
            clks_per_bit=868,
            direction='TX',
            log=self.log
        )

        # UART monitor (captures responses from bridge)
        self.uart_rx_monitor = UARTMonitor(
            entity=dut,
            title="UART_RX_MON",
            signal_name="o_uart_tx",
            clock=dut.aclk,
            clks_per_bit=868,
            direction='RX',
            log=self.log
        )

    async def send_write_command(self, addr, data):
        """Send UART write command"""
        cmd = f"W {addr:X} {data:X}\n"
        self.uart_rx_monitor._recvQ.clear()
        await self.uart_tx.send_string(cmd)

        # Wait for response
        await self.wait_clocks('clk', 200000)

        # Check for "OK\n"
        if len(self.uart_rx_monitor._recvQ) >= 3:
            response = ""
            for _ in range(3):
                pkt = self.uart_rx_monitor._recvQ.popleft()
                response += chr(pkt.data)
            return response == "OK\n"
        return False

    async def send_read_command(self, addr):
        """Send UART read command"""
        cmd = f"R {addr:X}\n"
        self.uart_rx_monitor._recvQ.clear()
        await self.uart_tx.send_string(cmd)

        # Wait for response
        await self.wait_clocks('clk', 200000)

        # Parse "0x<hex>\n"
        if len(self.uart_rx_monitor._recvQ) >= 11:
            response = ""
            for _ in range(11):
                pkt = self.uart_rx_monitor._recvQ.popleft()
                response += chr(pkt.data)

            if response.startswith("0x") and response.endswith("\n"):
                data_hex = response[2:-1]
                return int(data_hex, 16)
        return None
```

---

## Testing UART Components

### Unit Tests

Located in: `bin/CocoTBFramework/components/uart/test_uart_components.py`

**Test Coverage:**
- Byte transmission accuracy
- Start/stop bit generation
- Baud rate timing
- String transmission
- Monitor capture accuracy
- Queue management

### Running Tests

```bash
cd bin/CocoTBFramework/components/uart
pytest test_uart_components.py -v
```

---

## Design Notes

### Clock Domain Crossing

UART inputs are asynchronous and require CDC:
- Use 2-FF synchronizer for RX input
- Implemented in UART RX modules (e.g., `uart_rx.sv`)
- BFM assumes single clock domain (testbench synchronous)

### Baud Rate Calculation

```python
def calculate_clks_per_bit(clock_mhz, baud_rate):
    """Calculate clks_per_bit parameter"""
    clock_hz = clock_mhz * 1_000_000
    return int(clock_hz / baud_rate)

# Examples
clks_per_bit_100mhz_115200 = calculate_clks_per_bit(100, 115200)  # 868
clks_per_bit_50mhz_115200 = calculate_clks_per_bit(50, 115200)    # 434
```

### Performance Considerations

**Testbench Performance:**
- UART is slow - expect long test times
- 115200 baud ≈ 11.5 KB/s max throughput
- Use higher baud rates for faster tests (if DUT supports)
- Consider parallel testing for throughput-intensive tests

**Simulation Optimization:**
```python
# For faster testing, use higher baud rate
FAST_CLKS_PER_BIT = 100  # ~1 Mbaud at 100 MHz

# Or skip UART BFM for bulk data
# Use direct AXI4-Lite transaction injection
```

---

## Known Issues

None currently documented.

---

## Future Enhancements

1. **Parity Support** - 8E1, 8O1 modes
2. **Flow Control** - RTS/CTS hardware handshaking
3. **Break Detection** - Extended low period detection
4. **Framing Error Detection** - Invalid stop bit detection
5. **Configurable Stop Bits** - 1, 1.5, 2 stop bits

---

## References

**Internal:**
- Converters Project - Usage example
- [CocoTB Framework Overview](../components_overview.md)
- TBBase *(see tbclasses/misc)*

**External:**
- [UART Wikipedia](https://en.wikipedia.org/wiki/Universal_asynchronous_receiver-transmitter)
- [CocoTB Documentation](https://docs.cocotb.org/)

---

**Version:** 1.0
**Last Review:** 2025-11-09
**Maintained By:** RTL Design Sherpa Project
