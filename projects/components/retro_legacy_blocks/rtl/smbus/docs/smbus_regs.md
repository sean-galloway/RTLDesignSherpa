<!---
Markdown description for SystemRDL register map.

Don't override. Generated from: $root
-->

## smbus_regs address map

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x3C

<p>System Management Bus controller with master/slave modes</p>

|Offset|    Identifier   |              Name             |
|------|-----------------|-------------------------------|
| 0x00 |  SMBUS_CONTROL  |     SMBus Control Register    |
| 0x04 |   SMBUS_STATUS  |     SMBus Status Register     |
| 0x08 |  SMBUS_COMMAND  |     SMBus Command Register    |
| 0x0C | SMBUS_SLAVE_ADDR|  SMBus Slave Address Register |
| 0x10 |    SMBUS_DATA   |      SMBus Data Register      |
| 0x14 |  SMBUS_TX_FIFO  |     SMBus TX FIFO Register    |
| 0x18 |  SMBUS_RX_FIFO  |     SMBus RX FIFO Register    |
| 0x1C |SMBUS_FIFO_STATUS|   SMBus FIFO Status Register  |
| 0x20 |  SMBUS_CLK_DIV  |  SMBus Clock Divider Register |
| 0x24 |  SMBUS_TIMEOUT  |     SMBus Timeout Register    |
| 0x28 |  SMBUS_OWN_ADDR |   SMBus Own Address Register  |
| 0x2C | SMBUS_INT_ENABLE|SMBus Interrupt Enable Register|
| 0x30 | SMBUS_INT_STATUS|SMBus Interrupt Status Register|
| 0x34 |    SMBUS_PEC    |       SMBus PEC Register      |
| 0x38 |SMBUS_BLOCK_COUNT|   SMBus Block Count Register  |

### SMBUS_CONTROL register

- Absolute Address: 0x0
- Base Offset: 0x0
- Size: 0x4

<p>Global SMBus configuration and control</p>

|Bits|Identifier|Access|Reset|     Name    |
|----|----------|------|-----|-------------|
|  0 | master_en|  rw  | 0x0 |Master Enable|
|  1 | slave_en |  rw  | 0x0 | Slave Enable|
|  2 |  pec_en  |  rw  | 0x0 |  PEC Enable |
|  3 | fast_mode|  rw  | 0x0 |  Fast Mode  |
|  4 |fifo_reset|  rw  | 0x0 |  FIFO Reset |
|  5 |soft_reset|  rw  | 0x0 |  Soft Reset |
|31:6| reserved |   r  | 0x0 |   Reserved  |

#### master_en field

<p>Enable master mode (0=disabled, 1=enabled)</p>

#### slave_en field

<p>Enable slave mode (0=disabled, 1=enabled)</p>

#### pec_en field

<p>Enable Packet Error Checking (0=disabled, 1=enabled)</p>

#### fast_mode field

<p>Clock speed: 0=standard (100kHz), 1=fast (400kHz)</p>

#### fifo_reset field

<p>Reset TX/RX FIFOs (write 1, auto-clears)</p>

#### soft_reset field

<p>Soft reset controller (write 1, auto-clears)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_STATUS register

- Absolute Address: 0x4
- Base Offset: 0x4
- Size: 0x4

<p>SMBus controller status flags</p>

| Bits|   Identifier  |Access|Reset|        Name        |
|-----|---------------|------|-----|--------------------|
|  0  |      busy     |   r  |  —  |        Busy        |
|  1  |   bus_error   |   r  |  —  |      Bus Error     |
|  2  | timeout_error |   r  |  —  |    Timeout Error   |
|  3  |   pec_error   |   r  |  —  |      PEC Error     |
|  4  |    arb_lost   |   r  |  —  |  Arbitration Lost  |
|  5  |  nak_received |   r  |  —  |    NAK Received    |
|  6  |slave_addressed|   r  |  —  |   Slave Addressed  |
|  7  |    complete   |   r  |  —  |Transaction Complete|
| 11:8|   fsm_state   |   r  |  —  |      FSM State     |
|31:12|    reserved   |   r  | 0x0 |      Reserved      |

#### busy field

<p>Transaction in progress (0=idle, 1=busy)</p>

#### bus_error field

<p>Bus error detected (NAK, arbitration loss, etc.)</p>

#### timeout_error field

<p>Transaction timeout (&gt;25ms)</p>

#### pec_error field

<p>PEC mismatch detected</p>

#### arb_lost field

<p>Multi-master arbitration lost</p>

#### nak_received field

<p>NAK received from slave</p>

#### slave_addressed field

<p>This device addressed as slave</p>

#### complete field

<p>Transaction completed successfully</p>

#### fsm_state field

<p>Current state machine state (for debugging)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_COMMAND register

- Absolute Address: 0x8
- Base Offset: 0x8
- Size: 0x4

<p>Transaction command and control</p>

| Bits|Identifier|Access|Reset|      Name      |
|-----|----------|------|-----|----------------|
| 3:0 |trans_type|  rw  | 0x0 |Transaction Type|
| 15:8| cmd_code |  rw  | 0x0 |  Command Code  |
|  16 |   start  |  rw  | 0x0 |      Start     |
|  17 |   stop   |  rw  | 0x0 |      Stop      |
|31:18| reserved |   r  | 0x0 |    Reserved    |

#### trans_type field

<p>Transaction type: 0=Quick, 1=SendByte, 2=RecvByte, 3=WriteByte, 4=ReadByte, 5=WriteWord, 6=ReadWord, 7=BlockWrite, 8=BlockRead, 9=BlockProc</p>

#### cmd_code field

<p>SMBus command byte (for transactions that use it)</p>

#### start field

<p>Start transaction (write 1, auto-clears)</p>

#### stop field

<p>Force stop/abort current transaction (write 1, auto-clears)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_SLAVE_ADDR register

- Absolute Address: 0xC
- Base Offset: 0xC
- Size: 0x4

<p>Target slave address for master transactions</p>

|Bits|Identifier|Access|Reset|     Name    |
|----|----------|------|-----|-------------|
| 6:0|slave_addr|  rw  | 0x0 |Slave Address|
|31:7| reserved |   r  | 0x0 |   Reserved  |

#### slave_addr field

<p>7-bit slave address (bits[7:1]), bit[0] is R/W (set by controller)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_DATA register

- Absolute Address: 0x10
- Base Offset: 0x10
- Size: 0x4

<p>Single byte data for simple transactions</p>

|Bits|Identifier|Access|Reset|   Name  |
|----|----------|------|-----|---------|
| 7:0|   data   |  rw  | 0x0 |Data Byte|
|31:8| reserved |   r  | 0x0 | Reserved|

#### data field

<p>Data byte for Send/Receive Byte transactions</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_TX_FIFO register

- Absolute Address: 0x14
- Base Offset: 0x14
- Size: 0x4

<p>Transmit FIFO write port for block transactions</p>

|Bits|Identifier|Access|Reset|  Name  |
|----|----------|------|-----|--------|
| 7:0|  tx_data |   w  | 0x0 | TX Data|
|31:8| reserved |   r  | 0x0 |Reserved|

#### tx_data field

<p>Write data byte to TX FIFO</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_RX_FIFO register

- Absolute Address: 0x18
- Base Offset: 0x18
- Size: 0x4

<p>Receive FIFO read port for block transactions</p>

|Bits|Identifier|Access|Reset|  Name  |
|----|----------|------|-----|--------|
| 7:0|  rx_data |   r  |  —  | RX Data|
|31:8| reserved |   r  | 0x0 |Reserved|

#### rx_data field

<p>Read data byte from RX FIFO</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_FIFO_STATUS register

- Absolute Address: 0x1C
- Base Offset: 0x1C
- Size: 0x4

<p>TX/RX FIFO levels and status flags</p>

| Bits|Identifier|Access|Reset|     Name    |
|-----|----------|------|-----|-------------|
| 5:0 | tx_level |   r  |  —  |TX FIFO Level|
|  6  |  tx_full |   r  |  —  | TX FIFO Full|
|  7  | tx_empty |   r  |  —  |TX FIFO Empty|
| 13:8| rx_level |   r  |  —  |RX FIFO Level|
|  14 |  rx_full |   r  |  —  | RX FIFO Full|
|  15 | rx_empty |   r  |  —  |RX FIFO Empty|
|31:16| reserved |   r  | 0x0 |   Reserved  |

#### tx_level field

<p>Number of bytes in TX FIFO (0-32)</p>

#### tx_full field

<p>TX FIFO full flag</p>

#### tx_empty field

<p>TX FIFO empty flag</p>

#### rx_level field

<p>Number of bytes in RX FIFO (0-32)</p>

#### rx_full field

<p>RX FIFO full flag</p>

#### rx_empty field

<p>RX FIFO empty flag</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_CLK_DIV register

- Absolute Address: 0x20
- Base Offset: 0x20
- Size: 0x4

<p>Clock divider for SCL generation</p>

| Bits|Identifier|Access|Reset|     Name    |
|-----|----------|------|-----|-------------|
| 15:0|  clk_div |  rw  | 0xF9|Clock Divider|
|31:16| reserved |   r  | 0x0 |   Reserved  |

#### clk_div field

<p>SCL clock divider: SCL_freq = sys_clk / (4 * (div + 1)), default 100kHz @ 100MHz sys_clk</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_TIMEOUT register

- Absolute Address: 0x24
- Base Offset: 0x24
- Size: 0x4

<p>Timeout threshold configuration</p>

| Bits|Identifier|Access|  Reset |     Name    |
|-----|----------|------|--------|-------------|
| 23:0|  timeout |  rw  |0x2625A0|Timeout Value|
|31:24| reserved |   r  |   0x0  |   Reserved  |

#### timeout field

<p>Timeout threshold in clock cycles (default ~25-35ms)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_OWN_ADDR register

- Absolute Address: 0x28
- Base Offset: 0x28
- Size: 0x4

<p>Own slave address (for slave mode operation)</p>

|Bits|Identifier|Access|Reset|     Name     |
|----|----------|------|-----|--------------|
| 6:0| own_addr |  rw  | 0x0 |  Own Address |
|  7 |  addr_en |  rw  | 0x0 |Address Enable|
|31:8| reserved |   r  | 0x0 |   Reserved   |

#### own_addr field

<p>7-bit own slave address</p>

#### addr_en field

<p>Enable own address matching (slave mode)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_INT_ENABLE register

- Absolute Address: 0x2C
- Base Offset: 0x2C
- Size: 0x4

<p>Interrupt enable mask</p>

|Bits|  Identifier |Access|Reset|            Name           |
|----|-------------|------|-----|---------------------------|
|  0 | complete_en |  rw  | 0x0 |Transaction Complete Enable|
|  1 |   error_en  |  rw  | 0x0 |   Error Interrupt Enable  |
|  2 | tx_thresh_en|  rw  | 0x0 |  TX FIFO Threshold Enable |
|  3 | rx_thresh_en|  rw  | 0x0 |  RX FIFO Threshold Enable |
|  4 |slave_addr_en|  rw  | 0x0 |   Slave Addressed Enable  |
|31:5|   reserved  |   r  | 0x0 |          Reserved         |

#### complete_en field

<p>Enable interrupt on transaction complete</p>

#### error_en field

<p>Enable interrupt on bus error</p>

#### tx_thresh_en field

<p>Enable interrupt when TX FIFO below threshold</p>

#### rx_thresh_en field

<p>Enable interrupt when RX FIFO above threshold</p>

#### slave_addr_en field

<p>Enable interrupt when addressed as slave</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_INT_STATUS register

- Absolute Address: 0x30
- Base Offset: 0x30
- Size: 0x4

<p>Interrupt status flags (write 1 to clear)</p>

|Bits|  Identifier  |  Access |Reset|        Name        |
|----|--------------|---------|-----|--------------------|
|  0 | complete_int |rw, woclr| 0x0 |Transaction Complete|
|  1 |   error_int  |rw, woclr| 0x0 |   Error Interrupt  |
|  2 | tx_thresh_int|rw, woclr| 0x0 |  TX FIFO Threshold |
|  3 | rx_thresh_int|rw, woclr| 0x0 |  RX FIFO Threshold |
|  4 |slave_addr_int|rw, woclr| 0x0 |   Slave Addressed  |
|31:5|   reserved   |    r    | 0x0 |      Reserved      |

#### complete_int field

<p>Transaction completed (W1C)</p>

#### error_int field

<p>Bus error occurred (W1C)</p>

#### tx_thresh_int field

<p>TX FIFO below threshold (W1C)</p>

#### rx_thresh_int field

<p>RX FIFO above threshold (W1C)</p>

#### slave_addr_int field

<p>Device addressed as slave (W1C)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_PEC register

- Absolute Address: 0x34
- Base Offset: 0x34
- Size: 0x4

<p>Packet Error Checking value</p>

|Bits|Identifier|Access|Reset|   Name  |
|----|----------|------|-----|---------|
| 7:0|    pec   |  rw  | 0x0 |PEC Value|
|31:8| reserved |   r  | 0x0 | Reserved|

#### pec field

<p>Current/expected PEC value (CRC-8)</p>

#### reserved field

<p>Reserved bits</p>

### SMBUS_BLOCK_COUNT register

- Absolute Address: 0x38
- Base Offset: 0x38
- Size: 0x4

<p>Block transfer byte count</p>

|Bits| Identifier|Access|Reset|    Name   |
|----|-----------|------|-----|-----------|
| 5:0|block_count|  rw  | 0x0 |Block Count|
|31:6|  reserved |   r  | 0x0 |  Reserved |

#### block_count field

<p>Number of bytes for block transfer (1-32)</p>

#### reserved field

<p>Reserved bits</p>
