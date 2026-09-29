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

# 2. Router Status Registers

## 2.1 STATUS Register (Offset 0x2C)

```
Bits [2:0]:   router_state
  000 = IDLE (no packets)
  001 = ROUTING (active packet routing)
  010 = CONGESTED (buffers >75% full)
  011 = QUIESCENT (context switch prep)
  100 = ERROR (protocol violation detected)

Bits [7:3]:   north_buf_occupancy [0-8] (input buffer)
Bits [12:8]:  south_buf_occupancy [0-8]
Bits [17:13]: east_buf_occupancy [0-8]
Bits [22:18]: west_buf_occupancy [0-8]
Bits [27:23]: local_buf_occupancy [0-8]

Bits [31:28]: Reserved
```

**Read-Only:** Reflects current router state and buffer occupancy

## 2.2 ERROR_FLAGS Register (Offset 0x30)

```
Bit [0]: protocol_violation (invalid TUSER/TDEST combination)
Bit [1]: buffer_overflow (attempted write to full buffer)
Bit [2]: unauthorized_type (tile sent disallowed packet type)
Bit [3]: routing_error (destination unreachable)
Bit [4]: credit_underflow (sent flit without credits)
Bit [5]: deadlock_detected (circular dependency in VC allocation)
Bits [31:6]: Reserved

Write-1-to-Clear (W1C): Write 1 to clear error flag
```

**Example:**

```c
// Check for errors
uint32_t errors = read_reg(ERROR_FLAGS);
if (errors & (1 << 0)) {
    // Handle protocol violation
    log_error("Protocol violation on router");
}

// Clear errors
write_reg(ERROR_FLAGS, errors);  // W1C
```

## 2.3 Credit Status Registers

### VC0_CREDITS Register (Offset 0x3C)

```
Bits [3:0]:   north_vc0_credits [0-4]
Bits [7:4]:   south_vc0_credits [0-4]
Bits [11:8]:  east_vc0_credits [0-4]
Bits [15:12]: west_vc0_credits [0-4]
Bits [19:16]: local_vc0_credits [0-4]
Bits [31:20]: Reserved
```

### VC1_CREDITS Register (Offset 0x40)

```
Bits [3:0]:   north_vc1_credits [0-8]
Bits [7:4]:   south_vc1_credits [0-8]
Bits [11:8]:  east_vc1_credits [0-8]
Bits [15:12]: west_vc1_credits [0-8]
Bits [19:16]: local_vc1_credits [0-8]
Bits [31:20]: Reserved
```

**Use Case:** Monitoring flow control state, detecting congestion

---

**Next:** [Performance Counters](03_performance_counters.md)
