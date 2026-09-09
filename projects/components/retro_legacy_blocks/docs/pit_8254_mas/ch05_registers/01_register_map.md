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

# APB PIT 8254 - Register Map

## Overview

| Address | Name | Access | Description |
|---------|------|--------|-------------|
| `0x000` | PIT_CONFIG | RW | Global configuration |
| `0x004` | PIT_CONTROL | WO | Control word (8254-compatible) |
| `0x008` | PIT_STATUS | RO | Status readback (3 bytes) |
| `0x00C` | RESERVED | - | Reserved |
| `0x010` | COUNTER0_DATA | RW | Counter 0 value |
| `0x014` | COUNTER1_DATA | RW | Counter 1 value |
| `0x018` | COUNTER2_DATA | RW | Counter 2 value |

These seven registers are the only software-visible addresses in the 4 KB
window. Every other address -- 0x01C, 0x020 and up -- is dropped with
PSLVERR: the write is ignored and the read returns 0. There are no aliases.
See the top-level interface chapter for the decode policy.

---

## PIT_CONFIG (0x000) - Global Configuration

**Access:** Read/Write
**Reset Value:** `0x00000000`

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| [31:2] | RESERVED | RO | 0 | Reserved, read as 0 |
| [1] | CLOCK_SELECT | RW | 0 | Clock source select. Storage only: there is one counting clock and no divider behind this bit, so it reads back what was written and changes nothing |
| [0] | PIT_ENABLE | RW | 0 | Global PIT enable<br>0 = PIT disabled (counters paused)<br>1 = PIT enabled (counters active) |

**Programming Notes:**
- Setting `PIT_ENABLE=0` stops all counters immediately
- Counters preserve their current count values when disabled
- Recommended to disable PIT before reprogramming counters

---

## PIT_CONTROL (0x004) - Control Word

**Access:** Write-Only
**Reset Value:** N/A

| Bits | Name | Description |
|------|------|-------------|
| [7:6] | SC[1:0] | Counter Select<br>`00` = Counter 0<br>`01` = Counter 1<br>`10` = Counter 2<br>`11` = Read-back command (not implemented) |
| [5:4] | RW[1:0] | Read/Write Mode<br>`00` = Counter latch command (see the latch note below)<br>`01` = LSB only, bits [7:0]<br>`10` = MSB only, bits [15:8]<br>`11` = LSB then MSB, full 16-bit word (recommended) |
| [3:1] | M[2:0] | Counter Mode<br>`000` = Mode 0 (Interrupt on terminal count)<br>`001`-`101` = Modes 1-5 (not implemented) |
| [0] | BCD | Counting Mode<br>`0` = Binary (16-bit, 0-65535)<br>`1` = BCD (4 digits, 0-9999) |

**Counter latch (RW=00) is the 8254 command.** A control word with RW=00
freezes the selected counter's current count while the counter keeps
running; it does not touch the counter's mode, RW mode or BCD programming.
The next read of that counter's COUNTERx_DATA returns the frozen value and
releases the latch, so reads after that see the live count again. A second
latch command before the read is ignored -- the first latched value
survives. The latch is also released, without a read, when the counter is
reprogrammed (a control word that programs it) or reloaded (a data write),
so the first read after a new program returns the new program's live
count, never a stale snapshot of the old one. A data write never latches: RW=00 is the latch opcode, not a
read/write mode, so a counter still at its reset RW=00 takes a data write
as a full 16-bit load. (This replaced the write-triggered, sticky latch
of issue #52 on 2026-09-09.)

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

## PIT_STATUS (0x008) - Status Readback

**Access:** Read-Only
**Reset Value:** `0x00404040` (all counters in reset state: OUT=0, NULL_COUNT=1, RW_MODE/MODE/BCD=0 -> 0x40 per status byte)

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
| [3:1] | MODE | Counter mode (mirrors control word). WARNING: this mirrors whatever mode was WRITTEN, but the counter logic implements Mode 0 only - firmware that programs Mode 2 reads back "Mode 2" while getting Mode 0 behavior. |
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

## COUNTERx_DATA (0x010, 0x014, 0x018) - Counter Values

**Access:** Read/Write
**Reset Value:** `0x00000000`

| Bits | Name | Access | Description |
|------|------|--------|-------------|
| [31:16] | RESERVED | RO | Reserved, read as 0 |
| [15:0] | COUNT | RW | Counter value (16-bit) |

**Write Behavior:**
- Program the control word first so the RW mode is what you intend. A
  counter that has never seen a control word (RW=00 out of reset) takes a
  data write as a full 16-bit load -- it never latches
- The byte the counter loads follows the RW mode, on its natural lane:
  - `RW=11` (or reset RW=00): all 16 bits, `count = PWDATA[15:0]`
  - `RW=01` (LSB only): `count = {8'h00, PWDATA[7:0]}`
  - `RW=10` (MSB only): `count = {PWDATA[15:8], 8'h00}` -- write 0xAB00 to
    load 0xAB00
- PSTRB is honoured: the register block merges the strobed bytes into the
  stored value and the load takes that merged value, so a PSTRB=0x1 write
  loads {stored high byte, new low byte}
- The stored value that a byte-strobed write merges with is the field's
  mirror of the LIVE count, not the value software last wrote, so a partial
  load on a running counter takes the other byte from wherever the count is
  that cycle. Disable the PIT or use a full 16-bit write when the result
  must be deterministic.
- One write, one load: the load strobe fires once, aligned to the stored
  value, so the count goes old to new in a single cycle with no stale
  intermediate value and no spurious OUT or interrupt. A running counter can
  be reloaded safely
- A count of 0 means 65536 (10000 in BCD): terminal count after a full wrap
- The load clears NULL_COUNT and drives OUT low; the counter then counts
  whenever `GATE` is high and `PIT_ENABLE=1`. GATE low pauses it, GATE high
  resumes it from where it stopped
- Writes while counting replace the count and restart from the new value

**Read Behavior:**
- The value returned depends on the counter's programmed RW mode, on the
  same lane the write uses:
  - `RW=01` (LSB only): returns `{8'h00, count[7:0]}`
  - `RW=10` (MSB only): returns `{count[15:8], 8'h00}` -- the high byte in
    bits [15:8], bits [7:0] read 0
  - `RW=11` (LSB then MSB): returns the full 16-bit current count
- Returns the live count -- or, if a latch command is pending, the latched
  count; that read releases the latch (see PIT_CONTROL)
- After terminal count the counter parks at 0 with OUT high; it does not
  keep decrementing past zero the way a real 8254 does (stated deviation)
- The counter continues decrementing while being read; for an atomic
  snapshot use the latch command, or disable the PIT first

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

## Timing

**Write Timing:**
```
APB Write → field storage updates (PSTRB merged) → one aligned load strobe,
next cycle → counter holds the new value → counting while GATE high and PIT enabled
```

**Read Timing:**
```
APB Read → Counter Sample (1 cycle) → Register Read (1 cycle) → APB Response
```

**Important:** Due to APB and counter pipeline delays, there may be 2-3 cycle latency between register writes and counter response.

---

## Usage Example

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

**Version:** 1.1
**Last Updated:** 2026-09-09
