### APB PIT 8254 - Register Map

#### Address Map Overview

| Address | Name | Access | Description |
|---------|------|--------|-------------|
| `0x000` | PIT_CONFIG | RW | Global configuration |
| `0x004` | PIT_CONTROL | WO | Control word (8254-compatible) |
| `0x008` | PIT_STATUS | RO | Status readback (3 bytes) |
| `0x00C` | RESERVED | - | Reserved |
| `0x010` | COUNTER0_DATA | RW | Counter 0 value |
| `0x014` | COUNTER1_DATA | RW | Counter 1 value |
| `0x018` | COUNTER2_DATA | RW | Counter 2 value |

---

#### PIT_CONFIG (0x000) - Global Configuration

**Access:** Read/Write
**Reset Value:** `0x00000000`

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| [31:2] | RESERVED | RO | 0 | Reserved, read as 0 |
| [1] | CLOCK_SELECT | RW | 0 | Clock source select (future use) |
| [0] | PIT_ENABLE | RW | 0 | Global PIT enable<br>0 = PIT disabled (counters paused)<br>1 = PIT enabled (counters active) |

**Programming Notes:**
- Setting `PIT_ENABLE=0` stops all counters immediately
- Counters preserve their current count values when disabled
- Recommended to disable PIT before reprogramming counters

---

#### PIT_CONTROL (0x004) - Control Word

**Access:** Write-Only
**Reset Value:** N/A

| Bits | Name | Description |
|------|------|-------------|
| [7:6] | SC[1:0] | Counter Select<br>`00` = Counter 0<br>`01` = Counter 1<br>`10` = Counter 2<br>`11` = Read-back command (not implemented) |
| [5:4] | RW[1:0] | Read/Write Mode<br>`00` = Counter latch (not implemented)<br>`01` = LSB only<br>`10` = MSB only<br>`11` = LSB then MSB (recommended) |
| [3:1] | M[2:0] | Counter Mode<br>`000` = Mode 0 (Interrupt on terminal count)<br>`001`-`101` = Modes 1-5 (not implemented) |
| [0] | BCD | Counting Mode<br>`0` = Binary (16-bit, 0-65535)<br>`1` = BCD (4 digits, 0-9999) |

**Control Word Format (8254-Compatible):**
```
    7    6    5    4    3    2    1    0
┌────┬────┬────┬────┬────┬────┬────┬────┐
│ SC │ SC │ RW │ RW │ M  │ M  │ M  │BCD │
└────┴────┴────┴────┴────┴────┴────┴────┘
```

**Programming Example:**
```c
// Configure Counter 0 for Mode 0, binary, LSB+MSB access
uint32_t control_word = (0 << 6) |  // Counter 0
                        (3 << 4) |  // LSB+MSB
                        (0 << 1) |  // Mode 0
                        (0 << 0);   // Binary
write_register(PIT_CONTROL, control_word);  // Write 0x30
```

---

#### PIT_STATUS (0x008) - Status Readback

**Access:** Read-Only
**Reset Value:** `0x303030` (all counters in reset state)

| Bits | Name | Description |
|------|------|-------------|
| [31:24] | RESERVED | Reserved, read as 0 |
| [23:16] | COUNTER2_STATUS | Counter 2 status byte |
| [15:8] | COUNTER1_STATUS | Counter 1 status byte |
| [7:0] | COUNTER0_STATUS | Counter 0 status byte |

**Status Byte Format (per counter):**
```
    7       6       5    4       3    2    1       0
┌───────┬───────┬────┬────┬────┬────┬────┬────────┐
│  OUT  │ NULL  │ RW │ RW │ M  │ M  │ M  │  BCD   │
└───────┴───────┴────┴────┴────┴────┴────┴────────┘
```

| Bit | Name | Description |
|-----|------|-------------|
| [7] | OUT | Counter OUT pin state<br>`0` = OUT low (counting)<br>`1` = OUT high (terminal count reached) |
| [6] | NULL_COUNT | No count loaded flag<br>`0` = Count value loaded<br>`1` = No count loaded yet |
| [5:4] | RW_MODE | Read/Write mode (mirrors control word) |
| [3:1] | MODE | Counter mode (mirrors control word) |
| [0] | BCD | BCD/Binary mode (mirrors control word) |

**Reading Example:**
```c
uint32_t status = read_register(PIT_STATUS);
uint8_t counter0_status = status & 0xFF;
bool out_high = (counter0_status >> 7) & 0x1;
bool null_count = (counter0_status >> 6) & 0x1;
uint8_t rw_mode = (counter0_status >> 4) & 0x3;
uint8_t mode = (counter0_status >> 1) & 0x7;
bool bcd = counter0_status & 0x1;
```

---

#### COUNTERx_DATA (0x010, 0x014, 0x018) - Counter Values

**Access:** Read/Write
**Reset Value:** `0x00000000`

| Bits | Name | Access | Description |
|------|------|--------|-------------|
| [31:16] | RESERVED | RO | Reserved, read as 0 |
| [15:0] | COUNT | RW | Counter value (16-bit) |

**Write Behavior:**
- Must program control word BEFORE writing counter data
- Counter loads value immediately
- If `GATE` high and `PIT_ENABLE=1`, counter starts decrementing
- Writes while counting update the reload value and restart counting

**Read Behavior:**
- Returns current counter value (not reload value)
- Counter continues decrementing while being read
- For stable reads, disable PIT first or use very fast access

**Programming Example:**
```c
// Program Counter 0 with count value 1000
write_register(PIT_CONTROL, 0x30);  // Counter 0, LSB+MSB, Mode 0
write_register(COUNTER0_DATA, 1000);

// Counter will:
// 1. Load 1000 into internal counter
// 2. Start decrementing if GATE=1 and PIT_ENABLE=1
// 3. Set OUT=1 when count reaches 0
```

**Read Example:**
```c
// Read current count value
uint32_t count = read_register(COUNTER0_DATA) & 0xFFFF;
```

---

#### Register Access Timing

**Write Timing:**
```
APB Write → Register Update (1 cycle) → Counter Load (1 cycle) → Start Counting
```

**Read Timing:**
```
APB Read → Counter Sample (1 cycle) → Register Read (1 cycle) → APB Response
```

**Important:** Due to APB and counter pipeline delays, there may be 2-3 cycle latency between register writes and counter response.

---

#### Programming Sequences

**Basic Counter Start:**
```c
// 1. Disable PIT
write_register(PIT_CONFIG, 0x00);

// 2. Program control word
write_register(PIT_CONTROL, 0x30);  // Counter 0, Mode 0, binary

// 3. Load count value
write_register(COUNTER0_DATA, 1000);

// 4. Enable PIT
write_register(PIT_CONFIG, 0x01);

// 5. Wait for OUT signal or poll status
while (!(read_register(PIT_STATUS) & 0x80)) {
    // Wait for OUT bit to go high
}
```

**Multiple Counter Configuration:**
```c
// Disable PIT
write_register(PIT_CONFIG, 0x00);

// Program Counter 0
write_register(PIT_CONTROL, 0x30);
write_register(COUNTER0_DATA, 100);

// Program Counter 1
write_register(PIT_CONTROL, 0x70);  // Counter 1
write_register(COUNTER1_DATA, 200);

// Program Counter 2
write_register(PIT_CONTROL, 0xB0);  // Counter 2
write_register(COUNTER2_DATA, 300);

// Enable all counters
write_register(PIT_CONFIG, 0x01);
```

---

**Version:** 1.0
**Last Updated:** 2025-11-08
