# UART BFM Components

**Purpose:** UART Bus Functional Models for CocoTB verification

**Components:**
- `UARTPacket` - Transaction data structure
- `UARTMonitor` - UART line monitor with packet capture
- `UARTMaster` - UART transmitter driver
- `UARTSlave` - UART receiver with auto-response capability

---

## Quick Start

### Basic UART Transmission

```python
import cocotb
from cocotb.triggers import Timer
from CocoTBFramework.components.uart import UARTMaster, UARTMonitor

@cocotb.test()
async def test_uart_loopback(dut):
    """Test UART loopback using BFMs"""

    # Create UART TX master
    uart_tx = UARTMaster(
        entity=dut,
        title="UART_TX",
        signal_name="i_uart_rx",  # DUT's RX input
        clock=dut.aclk,
        clks_per_bit=868  # 100MHz / 115200 baud
    )

    # Create UART RX monitor
    uart_rx_mon = UARTMonitor(
        entity=dut,
        title="UART_RX_MON",
        signal_name="o_uart_tx",  # DUT's TX output
        clock=dut.aclk,
        clks_per_bit=868,
        direction='RX'
    )

    # Send command: "W 1000 DEADBEEF\n"
    await uart_tx.send_string("W 1000 DEADBEEF\n")

    # Wait for response
    await Timer(100, units='us')

    # Check response: "OK\n"
    assert len(uart_rx_mon._recvQ) == 3
    pkt0 = uart_rx_mon._recvQ.popleft()
    pkt1 = uart_rx_mon._recvQ.popleft()
    pkt2 = uart_rx_mon._recvQ.popleft()

    assert pkt0.data == ord('O')
    assert pkt1.data == ord('K')
    assert pkt2.data == ord('\n')
```

### Using UART Slave with Auto-Response

```python
from CocoTBFramework.components.uart import UARTSlave

# Create UART slave (DUT perspective)
uart_slave = UARTSlave(
    entity=dut,
    title="UART_SLAVE",
    rx_signal_name="i_uart_rx",  # DUT receives on this
    tx_signal_name="o_uart_tx",  # DUT transmits on this
    clock=dut.aclk,
    clks_per_bit=868
)

# Add auto-responses
uart_slave.add_response(ord('?'), "READY\n")  # '?' → "READY\n"
uart_slave.add_response(ord('R'), "0xDEADBEEF\n")  # 'R' → "0xDEADBEEF\n"

# Slave automatically responds when it receives these bytes
```

### Monitoring UART Traffic

```python
# Monitor captures all transactions
uart_mon = UARTMonitor(
    entity=dut,
    title="UART_MON",
    signal_name="uart_tx",
    clock=dut.aclk,
    clks_per_bit=868,
    direction='TX'
)

# ... run test ...

# Check captured packets
for packet in uart_mon._recvQ:
    print(packet.formatted(compact=True))
    # Output: "#1 TX @ 1234.5ns: 0x41 (A)"
    # Output: "#2 TX @ 2345.6ns: 0x42 (B)"

# Queue-based verification
if uart_mon._recvQ:
    pkt = uart_mon._recvQ.popleft()
    assert pkt.data == 0x41  # 'A'
    assert pkt.direction == 'TX'
    assert not pkt.has_errors()
```

---

## API Reference

### UARTPacket

**Data Structure for UART Transactions**

```python
packet = UARTPacket(
    start_time=1234.5,    # Simulation time (ns)
    count=1,              # Transaction counter
    data=0x41,            # Byte value (0-255)
    parity=None,          # Optional parity bit
    parity_error=False,   # Parity error flag
    framing_error=False,  # Framing error flag
    direction='TX'        # 'TX' or 'RX'
)

# Methods
packet.formatted(compact=True)  # "#1 TX @ 1234.5ns: 0x41 (A)"
packet.is_printable()           # True if 32 <= data <= 126
packet.as_char()                # 'A' or '?' if non-printable
packet.has_errors()             # True if any error flags set
```

### UARTMonitor

**Monitor UART line and capture transactions**

```python
monitor = UARTMonitor(
    entity=dut,              # CocoTB DUT
    title="UART_MON",        # Name for logging
    signal_name="uart_tx",   # Signal to monitor
    clock=dut.clk,           # Reference clock
    clks_per_bit=868,        # Clocks per bit period
    direction='TX',          # 'TX' or 'RX' label
    log=None                 # Optional logger
)

# Access captured packets
if monitor._recvQ:
    packet = monitor._recvQ.popleft()
```

**Protocol:** 8N1 (8 data bits, no parity, 1 stop bit)

### UARTMaster

**Transmit UART data**

```python
master = UARTMaster(
    entity=dut,
    title="UART_TX",
    signal_name="uart_tx",
    clock=dut.clk,
    clks_per_bit=868
)

# Send single byte
await master.send(0x55)
await master.send('A')  # Character

# Send multiple bytes
await master.send_bytes([0x41, 0x42, 0x43])  # ABC
await master.send_bytes(b"ABC")              # bytes object

# Send string
await master.send_string("Hello, World!\n")
```

### UARTSlave

**Receive UART data with auto-response**

```python
slave = UARTSlave(
    entity=dut,
    title="UART_SLAVE",
    rx_signal_name="uart_rx",  # DUT RX input
    tx_signal_name="uart_tx",  # DUT TX output
    clock=dut.clk,
    clks_per_bit=868
)

# Add auto-responses
slave.add_response(ord('?'), "READY\n")
slave.add_response(0x05, [0x06, 0x07])  # ENQ → ACK, BEL

# Manual receive checking
byte_val = slave.get_received()  # Non-blocking
if byte_val is not None:
    print(f"Received: 0x{byte_val:02X}")

# Wait for specific byte
success = await slave.wait_for_byte('A', timeout_cycles=1000)
```

---

## Configuration

### Baud Rate Calculation

```python
# Formula: clks_per_bit = clock_freq / baud_rate
#
# Examples:
# - 100 MHz / 115200 baud = 868 clocks/bit
# - 50 MHz / 115200 baud = 434 clocks/bit
# - 100 MHz / 9600 baud = 10417 clocks/bit

clks_per_bit = int(clock_freq_hz / baud_rate)
```

### Common Baud Rates

| Baud Rate | Clock Freq | clks_per_bit |
|-----------|------------|--------------|
| 115200    | 100 MHz    | 868          |
| 115200    | 50 MHz     | 434          |
| 9600      | 100 MHz    | 10417        |
| 9600      | 50 MHz     | 5208         |

---

## Design Patterns

### Pattern 1: Command-Response Testing

```python
# Send command, verify response
await uart_tx.send_string("W 1000 DEADBEEF\n")

# Wait for processing
await Timer(50, units='us')

# Verify response
assert len(uart_rx_mon._recvQ) >= 3
response = ''.join([chr(p.data) for p in uart_rx_mon._recvQ])
assert "OK" in response
```

### Pattern 2: Loopback Verification

```python
# Send test pattern
test_data = [0x55, 0xAA, 0xF0, 0x0F]
await uart_tx.send_bytes(test_data)

# Verify echoed back
await Timer(100, units='us')

for i, expected in enumerate(test_data):
    assert len(uart_rx_mon._recvQ) > 0
    packet = uart_rx_mon._recvQ.popleft()
    assert packet.data == expected, f"Byte {i}: expected 0x{expected:02X}, got 0x{packet.data:02X}"
```

### Pattern 3: ASCII Protocol Testing

```python
# Test ASCII command protocol
commands = [
    ("R 0000\n", "0xDEADBEEF\n"),
    ("W 1000 12345678\n", "OK\n"),
]

for cmd, expected_resp in commands:
    # Clear previous responses
    uart_rx_mon._recvQ.clear()

    # Send command
    await uart_tx.send_string(cmd)

    # Wait for response
    await Timer(100, units='us')

    # Collect response
    response = ''.join([chr(p.data) for p in uart_rx_mon._recvQ])
    assert response == expected_resp
```

---

## Integration with Testbenches

### Using with TBBase

```python
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.uart import UARTMaster, UARTMonitor

class UARTBridgeTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)

        # Create UART components
        self.uart_tx = UARTMaster(
            entity=dut,
            title="UART_TX",
            signal_name="i_uart_rx",
            clock=dut.aclk,
            clks_per_bit=868,
            log=self.log
        )

        self.uart_rx_mon = UARTMonitor(
            entity=dut,
            title="UART_RX_MON",
            signal_name="o_uart_tx",
            clock=dut.aclk,
            clks_per_bit=868,
            direction='RX',
            log=self.log
        )

    async def setup_clocks_and_reset(self):
        await self.start_clock('aclk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('aclk', 10)
        await self.deassert_reset()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def write_command(self, addr, data):
        """Send AXI write command via UART"""
        cmd = f"W {addr:X} {data:X}\n"
        await self.uart_tx.send_string(cmd)

        # Wait for "OK" response
        await Timer(100, units='us')
        response = ''.join([chr(p.data) for p in self.uart_rx_mon._recvQ])
        return "OK" in response
```

---

## Examples

See test examples in:
- `projects/components/converters/dv/tests/test_uart_axi_bridge.py` (when created)

---

**Version:** 1.0
**Created:** 2025-11-09
**Author:** RTL Design Sherpa Project
