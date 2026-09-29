# LPDDR2 CA-bus command encoding — reference (locked spec)

**Authority:** JEDEC JESD209-2F, *Table 60 — Command Truth Table* (p149–150), the
command-description prose in §5.x, and DFI v2.1.1 §"CA bus for LPDDR2". Local copies:
`dfi-specs/ddr2-lpddr2/jedec/LPDDR2_JESD209-2F.pdf`,
`dfi-specs/jedec/DFI_v2_1_1.pdf`.

This is the single source of truth that BOTH the RTL command formatter
(`rtl/fub/dfi_cmd_formatter.sv`, LPDDR2 branch) AND the verification BFM
(`RTLDesignSherpa-DV` `CocoTBFramework/components/dfi/lpddr_ca.py`) encode against.
Neither side may invent its own packing — they must be bit-identical to the tables
below, and the round-trip conformance test (`dv/tests/fub/test_dfi_cmd_formatter.py`)
holds them to it.

> WHY THIS EXISTS: DDR2 puts the command on dedicated `ras_n/cas_n/we_n` + a
> straight `dfi_address` row/column. LPDDR2 has NO ras/cas/we — the command AND a
> **scrambled** address are multiplexed onto a 10-bit CA bus across two clock edges.
> The row/column bit-to-pin assignment (Table 60) is non-contiguous and JEDEC
> forbids any other ordering ("Scrambling ... in any order different than those
> described in the Command truth table is prohibited", §2.14.1). Bit-exactness is
> therefore a spec requirement, not a nicety.

---

## 1. DFI carriage: the flat 20-bit CA word

Per DFI v2.1.1, an LPDDR2 command spanning two CA cycles is carried on `dfi_address`
as a single word per DFI command cycle; `dfi_ras_n / dfi_cas_n / dfi_we_n / dfi_bank`
are held idle (`1` / `0`). The PHY splits the word into the two 10-bit DDR CA cycles.

Canonical bit layout used by pumice (CA0 = LSB of each 10-bit half):

```
 dfi_address bit:  19 18 17 16 15 14 13 12 11 10 | 9  8  7  6  5  4  3  2  1  0
 CA pin / edge:    C9 C8 C7 C6 C5 C4 C3 C2 C1 C0 | C9 C8 C7 C6 C5 C4 C3 C2 C1 C0
                   \------ FALLING edge (f) -----/ \------ RISING edge (r) ------/
```

- `dfi_address[i]`      = CA`i` on the **rising** edge (CA`i`r), for i = 0..9
- `dfi_address[10 + i]` = CA`i` on the **falling** edge (CA`i`f), for i = 0..9

Requires `DFI_ADDR_BUS_W ≥ 20` (= `DFI_ADDR_WIDTH * DFI_RATE`). At the default
geometry `DFI_ADDR_WIDTH = ROW_WIDTH = 14`, `DFI_RATE = 2` → 28 bits, satisfied.
Upper bits (`[27:20]`) are driven `0`. `dfi_cs_n` is asserted for the target rank on
the command's DFI cycle exactly as for DDR2.

---

## 2. Command decode — rising-edge {CA0, CA1, CA2, CA3}

Per Table 60, every LPDDR2 command is selected by CS_n + CA0..CA3 + CKE at the
rising clock edge (NOTE 1). CKE-based commands (power-down / self-refresh entry &
exit) are NOT pure CA decodes — they are driven via CKE/CS sequencing and are out of
scope for the CA formatter.

| Command                | CA0r | CA1r | CA2r | CA3r | notes |
|------------------------|:----:|:----:|:----:|:----:|-------|
| MRW (Mode Reg Write)   |  L   |  L   |  L   |  L   | init / MR programming |
| MRR (Mode Reg Read)    |  L   |  L   |  L   |  H   | not used by pumice (write-only MR) |
| Refresh — per bank     |  L   |  L   |  H   |  L   | 8-bank devices only (NOTE 11) |
| Refresh — all bank     |  L   |  L   |  H   |  H   | |
| Activate               |  L   |  H   |  —   |  —   | CA2r+ carry row bits |
| Write                  |  H   |  L   |  L   |  —   | CA2r = L distinguishes from Read |
| Read                   |  H   |  L   |  H   |  —   | CA2r = H |
| Precharge              |  H   |  H   |  L   |  H   | |
| BST (Burst Terminate)  |  H   |  H   |  L   |  L   | not used by pumice |
| NOP / Deselect         |  H   |  H   |  H   |  —   | also CS_n=H = deselect |

`L` = logic 0, `H` = logic 1, `—` = carries payload (not part of the opcode).

---

## 3. Full per-command CA-pin assignment (Table 60, transcribed)

Two sub-rows per command: **r** = rising edge (`dfi_address[9:0]`), **f** = falling
edge (`dfi_address[19:10]`). `X` = don't-care (drive 0). `RFU` = reserved (drive 0).

### Activate  (CA0r=L, CA1r=H)
| edge | CA0 | CA1 | CA2 | CA3 | CA4 | CA5 | CA6 | CA7 | CA8 | CA9 |
|------|-----|-----|-----|-----|-----|-----|-----|-----|-----|-----|
| r    |  L  |  H  | R8  | R9  | R10 | R11 | R12 | BA0 | BA1 | BA2 |
| f    | R0  | R1  | R2  | R3  | R4  | R5  | R6  | R7  | R13 | R14 |

### Write  (CA0r=H, CA1r=L, CA2r=L)
| edge | CA0 | CA1 | CA2 | CA3 | CA4 | CA5 | CA6 | CA7 | CA8 | CA9 |
|------|-----|-----|-----|-----|-----|-----|-----|-----|-----|-----|
| r    |  H  |  L  |  L  | RFU | RFU | C1  | C2  | BA0 | BA1 | BA2 |
| f    | AP  | C3  | C4  | C5  | C6  | C7  | C8  | C9  | C10 | C11 |

### Read  (CA0r=H, CA1r=L, CA2r=H)
| edge | CA0 | CA1 | CA2 | CA3 | CA4 | CA5 | CA6 | CA7 | CA8 | CA9 |
|------|-----|-----|-----|-----|-----|-----|-----|-----|-----|-----|
| r    |  H  |  L  |  H  | RFU | RFU | C1  | C2  | BA0 | BA1 | BA2 |
| f    | AP  | C3  | C4  | C5  | C6  | C7  | C8  | C9  | C10 | C11 |

- `AP` (CA0f) HIGH → auto-precharge to the addressed bank (NOTE 4). Read+AP = RDA,
  Write+AP = WRA.
- `C0` is implied 0 and NOT transmitted (NOTE 12); the transmitted column field is
  C1..C11.

### Precharge  (CA0r=H, CA1r=H, CA2r=L, CA3r=H)
| edge | CA0 | CA1 | CA2 | CA3 | CA4 | CA5 | CA6 | CA7 | CA8 | CA9 |
|------|-----|-----|-----|-----|-----|-----|-----|-----|-----|-----|
| r    |  H  |  H  |  L  |  H  | AB  |  X  |  X  | BA0 | BA1 | BA2 |
| f    |  X  |  X  |  X  |  X  |  X  |  X  |  X  |  X  |  X  |  X  |

- `AB` (CA4r) HIGH → all-bank precharge; bank address then don't-care (NOTE 13).

### Refresh  (CA0r=L, CA1r=L, CA2r=H)
| variant   | CA3r | payload |
|-----------|:----:|---------|
| per-bank  |  L   | bank implied by internal counter; 8-bank parts only |
| all-bank  |  H   | — |

All other CA pins `X`.

### MRW — Mode Register Write  (CA0r=L, CA1r=L, CA2r=L, CA3r=L)
| edge | CA0 | CA1 | CA2 | CA3 | CA4 | CA5 | CA6 | CA7 | CA8 | CA9 |
|------|-----|-----|-----|-----|-----|-----|-----|-----|-----|-----|
| r    |  L  |  L  |  L  |  L  | MA0 | MA1 | MA2 | MA3 | MA4 | MA5 |
| f    | MA6 | MA7 | OP0 | OP1 | OP2 | OP3 | OP4 | OP5 | OP6 | OP7 |

- `MA[7:0]` = mode-register address, `OP[7:0]` = mode-register data (opcode).
- Controller plumbing: the scheduler carries the MRW fields in the ROW request as
  `{MA[5:0], OP[7:0]}` (row[13:8]=index, row[7:0]=data), which `dfi_cmd_formatter`
  unpacks into `w_mr_ma`/`w_mr_op`. This reaches the full MR0..MR63 range (a 3-bit
  bank port could not); MA[7:6]=0. The `init_sequencer` LPDDR2 chain (Reset MR63 ->
  ZQ MR10 -> MR1/2/3) drives it.

---

## 4. pumice geometry mapping (defaults: 8 banks, ROW_WIDTH=14, COL_WIDTH=10)

Bank (3 bits): `BA0 = CA7r`, `BA1 = CA8r`, `BA2 = CA9r`.

Row (14 bits, R0..R13; R14 unused):
- `R0..R7`   → CA0f..CA7f (falling)
- `R8..R12`  → CA2r..CA6r (rising)
- `R13`      → CA8f (falling)

Column (10 bits, C0..C9; C0 implied 0, so transmit C1..C9; C10/C11 unused):
- `C1, C2`   → CA5r, CA6r (rising)
- `C3..C9`   → CA1f..CA7f (falling)

Auto-precharge: `AP = CA0f`.

> A wider row/column geometry lights up the currently-unused pins (R14 = CA9f,
> C10 = CA8f, C11 = CA9f) — the tables in §3 are the full-width truth; §4 is only
> the subset populated at the default widths.

---

## 5. Implementation notes / gotchas

1. **BL16 unsupported today.** `mode_register.bl_o` is 4-bit and clips BL16→BL8.
   LPDDR2 supports BL4/8/16; only BL4/BL8 are wired. Separate future item.
2. **Read latency.** LPDDR2 `AL = 0`; `RL` comes from MR2 (not `AL+CL` as DDR2).
   Only matters for strict-timing read alignment (`t_rddata_en`); the lenient BFM
   self-times reads off `dfi_rddata_en`.
3. **Power-down / self-refresh** entry/exit ride CKE+CS sequences, not CA opcodes
   (Table 61) — handled by `powerdown_ctrl` / the init sequencer, not this formatter.
4. **MRR** (mode-register read) is unused: pumice programs MRs but never reads them
   back over the bus.
5. **Endianness of the flat word** is fixed by §1 (CA0 = LSB of each half). Both the
   RTL and the BFM MUST agree on this; the conformance test drives the RTL and
   decodes with `lpddr_ca.decode_lpddr2_ca`, so any disagreement fails immediately.

---

## 6. Traceability

| Field | Source |
|-------|--------|
| Command decode {CA0..CA3} | Table 60 (p149); prose §5 (Activate p-CA0=L/CA1=H; Read CA0=H/CA1=L/CA2=H; Write CA0=H/CA1=L/CA2=L) |
| Row/col/bank pin assignment | Table 60 rising/falling rows |
| C0 implied 0 | Table 60 NOTE 12 |
| AP semantics | Table 60 NOTE 3, 4 |
| All-bank precharge (AB) | Table 60 NOTE 13 |
| Per-bank refresh 8-bank only | Table 60 NOTE 11 |
| DFI flat-word carriage | DFI v2.1.1, CA-bus-for-LPDDR2 |
