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

# 1. Configuration Register Bank

## 1.1 Register Map

Each router/tile has configuration registers:

```
Base + 0x00: MODE_SELECT       (RW) - Active context [1:0]
Base + 0x04: ROUTE_TABLE_BASE  (RO) - Current routing table address
Base + 0x08: CUSTOM_ROUTE_0    (RW) - User routing entry 0
Base + 0x0C: CUSTOM_ROUTE_1    (RW) - User routing entry 1
     ...
Base + 0x1C: CUSTOM_ROUTE_7    (RW) - User routing entry 7
Base + 0x20: FILTER_ENABLE     (RW) - Enable packet type filtering
Base + 0x24: ALLOWED_TYPES     (RW) - Permitted TUSER values (bitmask)
Base + 0x28: RATE_LIMIT        (RW) - Max injection rate (pkts/1000 cyc)
Base + 0x2C: STATUS            (RO) - Router state, buffer occupancy
Base + 0x30: ERROR_FLAGS       (RW1C) - Protocol violations, overflows
Base + 0x34: PKT_COUNT_TX      (RO) - Packets transmitted (this tile)
Base + 0x38: PKT_COUNT_RX      (RO) - Packets received (this tile)
Base + 0x3C: VC0_CREDITS       (RO) - Available VC0 credits
Base + 0x40: VC1_CREDITS       (RO) - Available VC1 credits
```

## 1.2 MODE_SELECT Register (Offset 0x00)

```
Bits [1:0]: context_id
  00 = Mesh (XY routing)
  01 = Systolic (nearest-neighbor)
  10 = Tree (reduction topology)
  11 = Custom (user-defined)

Bits [31:2]: Reserved (write 0)
```

**Write:** Changes active routing context (takes effect immediately)
**Read:** Returns current context ID

## 1.3 CUSTOM_ROUTE_x Registers (Offsets 0x08-0x1C)

```
Custom routing table entries (8 total):

Bits [2:0]:   output_port (0=N, 1=S, 2=E, 3=W, 4=L)
Bits [6:3]:   dest_tile (0-15)
Bits [8:7]:   packet_type (00=DATA, 01=DESC, 10=CONFIG, 11=STATUS)
Bits [31:9]:  Reserved
```

**Use Case:** Context 3 (Custom) uses these entries for user-defined routing

## 1.4 FILTER_ENABLE Register (Offset 0x20)

```
Bit [0]: enable_filter
  0 = Accept all packet types
  1 = Filter based on ALLOWED_TYPES register

Bits [31:1]: Reserved
```

## 1.5 ALLOWED_TYPES Register (Offset 0x24)

```
Bit [0]: allow_PKT_DATA
Bit [1]: allow_PKT_DESC
Bit [2]: allow_PKT_CONFIG
Bit [3]: allow_PKT_STATUS
Bits [31:4]: Reserved

Default: 0xF (allow all)
```

**Note:** FILTER_ENABLE must be 1 for this to take effect

---

**Next:** [Router Status Registers](02_status_registers.md)
