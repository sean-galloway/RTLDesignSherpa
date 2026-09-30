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

# Descriptor Format

## Overview

RAPIDS uses 256-bit (32-byte) descriptors to define DMA transfers. Descriptors are stored in system memory and fetched by the Descriptor Engine when a channel is kicked. The layout is the layout RAPIDS Beats uses, bit for bit. What changed is the meaning of two things: the `length` field counts BYTES, and `src_addr` / `dst_addr` are byte addresses with no alignment requirement.

A descriptor therefore describes a transfer the way software thinks of it. A packet of 37 bytes at address 0x1007 is a descriptor with `length` = 37 and `dst_addr` = 0x1007. The hardware turns that into beats, byte enables and a partial last beat; software never does the arithmetic.

## Descriptor Layout

### 256-Bit Structure

```
Bit Range    Field Name           Width  Description
────────────────────────────────────────────────────────────────────────
[255:213]    reserved             43     Reserved (write 0)
[212:210]    desc_type            3      0 = LEGACY, 1 = EXTENDED (see below)
[209:208]    opcode               2      0 = DATA, 1 = CTRL_READ, 2 = CTRL_WRITE
[207:200]    priority             8      Transfer priority (informational)
[199:196]    channel_id           4      Channel ID (informational)
[195]        error                1      Error flag (written by hardware)
[194]        last                 1      Last descriptor in chain
[193]        gen_irq              1      Generate interrupt on completion
[192]        valid                1      Descriptor valid flag
[191:160]    next_descriptor_ptr  32     Address of next descriptor (0 = last)
[159:128]    length               32     Transfer length in BYTES
[127:64]     dst_addr             64     Destination byte address
[63:0]       src_addr             64     Source byte address
```

: 256-Bit Descriptor Layout (`rapids_pkg::descriptor_t`)

The authoritative definition is `rapids_pkg::descriptor_t` in `rtl/includes/rapids_pkg.sv`. Only bits `[255:0]` are fetched and used. Every field position is the same as in RAPIDS Beats, so a descriptor builder needs one change: the value written to `length`.

## Field Descriptions

### Control Bits [195:192]

| Bit | Field | Description |
|-----|-------|-------------|
| 192 | `valid` | Must be 1; a descriptor with valid=0 puts the channel in the error state |
| 193 | `gen_irq` | Set to 1 to generate a completion interrupt |
| 194 | `last` | Set to 1 for the last descriptor in a chain |
| 195 | `error` | Error flag; written by hardware, write 0 |

: Control Bits

### Direction

There is no direction field in the descriptor. Direction is a property of the **half** that owns the channel. The SOURCE half (memory to AXIS) reads from `src_addr`. The SINK half (AXIS to memory) writes to `dst_addr`. A descriptor is delivered to one half's descriptor engine by the address it was staged at, so the same layout serves both. Each half looks only at its own address, so the two offsets never have to agree.

### Transfer Length [159:128]

- 32-bit field specifying the transfer size in BYTES.
- The length is the packet length. On the sink it is the number of bytes the AXIS packet must carry. On the source it is the number of bytes in the one AXIS packet the descriptor produces.
- A length of 0 moves nothing and carries no packet record (see Alignment and Offsets).

### Next Pointer [191:160]

- 32-bit address of the next descriptor, zero-extended to the engine's 64-bit address width.
- A value of 0 terminates the chain, as does `last` = 1.
- Autonomous chaining also requires the address to fall inside one of the two configured descriptor address ranges.

Chain traversal is unchanged from RAPIDS Beats. See the shared Descriptor Chaining chapter.

### Address Fields [127:0]

**For SINK transfers (network to memory):**

| Field | Usage |
|-------|-------|
| `dst_addr` [127:64] | Memory write destination, any byte address |
| `src_addr` [63:0] | Not used (write 0) |

**For SOURCE transfers (memory to network):**

| Field | Usage |
|-------|-------|
| `dst_addr` [127:64] | Not used (write 0) |
| `src_addr` [63:0] | Memory read source, any byte address |

: Address Field Usage

## Alignment and Offsets

Let `BYTE_LANES` be the beat size in bytes (`DATA_WIDTH / 8`, 32 for the 256-bit build) and `OFF_W` its log2 (5 for 256 bits). For a linear DATA descriptor:

```
offset      = addr[OFF_W-1:0]                    (the low bits of the byte address)
beats_total = 0                                   if length == 0
            = (offset + length + BYTE_LANES - 1) >> OFF_W   otherwise
```

`beats_total` is the number of whole memory beats the transfer touches. The sum is computed with a 33-bit intermediate, so a length near 4 GB does not overflow. Each half applies the formula to its own address: the source uses `src_addr`, the sink uses `dst_addr`.

| Length (bytes) | Offset | beats_total | Useful bytes / (beats x 32) |
|----------------|--------|-------------|-----------------------------|
| 0 | any | 0 | no transfer |
| 1 | 0 | 1 | 0.031 |
| 2 | 31 | 2 | 0.031 |
| 32 | 0 | 1 | 1.000 |
| 32 | 1 | 2 | 0.500 |
| 37 | 0 | 2 | 0.578 |
| 60 | 5 | 3 | 0.625 |
| 100 | 7 | 4 | 0.781 |
| 203 | 3 | 7 | 0.906 |

: Beat Count Examples (BYTE_LANES = 32)

The last column is the fraction of the bus the transfer uses. A transfer that is a whole number of beats and starts on a beat boundary is 1.000. Everything else pays for the beats it touches, not the bytes it carries.

### How the offset reaches the bus

- **AXI address.** `AxADDR` is always issued beat-aligned. The offset never appears in the address. Address progression inside a transfer is the aligned-down start plus a beat count times `BYTE_LANES`.
- **Sink writes.** The first beat's `WSTRB` leaves lanes `0` to `offset-1` clear, and the last beat's `WSTRB` covers only the bytes that remain. Bytes outside the packet are never written, so a sub-beat transfer does not disturb its neighbors in memory.
- **Source reads.** The read master fetches whole beats from the aligned address. The egress re-packer drops the leading `offset` bytes and packs the rest, so the AXIS packet starts at byte lane 0.
- **AXIS.** The stream is packed. Only the last beat is partial: `TSTRB` is contiguous from lane 0 and `TLAST` is on that beat. See the AXIS Interface chapter.

### 4 KB boundaries

A burst never crosses a 4 KB boundary. The engines cut a burst at the boundary, so a transfer that straddles one is issued as more than one burst. This is a protocol rule handled in hardware, not something software arranges. Example: 203 bytes at an address whose low 12 bits are 0xFC3 has offset 3 and 7 beats. The first two beats (aligned addresses 0xFC0 and 0xFE0) end at the boundary. The remaining five beats start at the next 4 KB page.

### Zero-length descriptors

A descriptor with `length` = 0 moves nothing. It issues no read or write request and it carries no packet record, whatever its addresses are. It still occupies its place in the chain, so `last`, `next_descriptor_ptr` and `gen_irq` are honored. A zero-length DATA descriptor is therefore a legal way to report a completion event or end a chain without moving data.

### Packet record

Every non-zero DATA descriptor produces one packet record, `{bytes, offset}`, for each enabled direction. The data path uses the record to place bytes on the sink or to frame the packet on the source. The record is pulsed once, when the scheduler leaves the fetch state to start the transfer.

- Each channel's record queue is `PQ_DEPTH` deep (4). A descriptor whose record does not fit waits. This is backpressure and not an error.
- The sink ingress does not accept the first beat of a packet until the channel's record exists. Issue the descriptor before the packet arrives, or send them concurrently.
- `s_axis_tready` is one signal, qualified by the `tid` of the beat on the bus. A beat for a channel with no record stalls the whole stream, including beats for other channels queued behind it. The per-channel record queues and ingress holds keep the data intact, so the effect is delay and not corruption. A stream that must not head-of-line block should have every channel's descriptor issued before the stream starts.

## Descriptor Opcodes (DATA / CTRL_READ / CTRL_WRITE)

The 2-bit opcode selects one of three behaviors. Only `DATA` moves payload, and only `DATA` is affected by the byte-granular changes.

| Opcode | Value | Behavior |
|--------|-------|----------|
| `DATA` | `2'b00` | Payload transfer; `length` in bytes, byte addresses |
| `CTRL_READ` | `2'b01` | Consumer gate: poll a memory location until `(read & mask) == expected`, then release the chain |
| `CTRL_WRITE` | `2'b10` | Producer doorbell: one 32-bit write to a memory location, then continue |

: Descriptor Opcodes

The CTRL_READ and CTRL_WRITE field layouts are unchanged from RAPIDS Beats, and they carry no packet record. See the RAPIDS Beats descriptor chapter for the field tables and the retry limit.

## Extended Descriptors (row/col-major addressing)

`desc_type` = 1 (EXTENDED) selects strided, 2-D or circular addressing instead of linear accumulation. It is enabled at build time by `USE_ROW_COL_MAJOR_ADDRESSING`, which defaults to 1. An extended descriptor is 512 bits in two 256-bit chunks. Chunk 0 is the layout above with `desc_type` = 1. Chunk 1 is fetched by a second single-beat read at `descriptor_addr + 0x20`, so the two chunks must be contiguous in memory.

```
Chunk 1 (at descriptor_addr + 0x20)
Bit Range    Field Name        Width  Description
──────────────────────────────────────────────────────────────────────
[255:192]    reserved_hi       64     Reserved (future 3rd dimension)
[191:188]    wr_reserved       4      Reserved
[187:182]    wr_wrap1_log2     6      Write outer wrap window, log2 (0 = off)
[181:176]    wr_wrap0_log2     6      Write inner wrap window, log2 (0 = off)
[175:160]    wr_inner_count    16     Write beats per contiguous run
[159:128]    wr_stride_1       32     Write outer stride, SIGNED bytes
[127:96]     wr_stride_0       32     Write inner stride, SIGNED bytes
[95:92]      rd_reserved       4      Reserved
[91:86]      rd_wrap1_log2     6      Read outer wrap window, log2 (0 = off)
[85:80]      rd_wrap0_log2     6      Read inner wrap window, log2 (0 = off)
[79:64]      rd_inner_count    16     Read beats per contiguous run
[63:32]      rd_stride_1       32     Read outer stride, SIGNED bytes
[31:0]       rd_stride_0       32     Read inner stride, SIGNED bytes
```

: Extended Descriptor Chunk 1 (`rapids_pkg::descriptor_ext_t`)

The mode selection, the address equation and the signed strides are unchanged from RAPIDS Beats. The layout is byte-compatible with STREAM's `descriptor_ext_t`.

### EXT descriptors stay beat-aligned (permanent limitation)

TYPE=EXT is not byte-granular, and it is not going to be. This is a deliberate, permanent limitation of RAPIDS. An extended descriptor must have:

- `src_addr` and `dst_addr` aligned to `BYTE_LANES` (32 bytes for the 256-bit build).
- A `length` that is a multiple of `BYTE_LANES`.

Row and column striding are counted in whole beats, so a run of `inner_count` beats is `inner_count x BYTE_LANES` bytes, and the strides step between beat-aligned rows. An EXT descriptor with an unaligned address or a length that is not a beat multiple is outside the contract and is not checked. Use a linear descriptor when the transfer starts or ends mid-beat. The byte-granular path (offsets, byte enables, partial last beat, packet records) applies to linear descriptors only.

## Descriptor Fetch

Fetch is unchanged from RAPIDS Beats. The Descriptor Engine issues a single-beat AXI4 read (`arlen` = 0) at the descriptor address, and again at `+0x20` for an EXTENDED descriptor. The parsed descriptor is handed to the scheduler, which converts `length` and the address to `beats_total`, the record and the address working registers as described above. The descriptor address and `next_descriptor_ptr` are 32-byte aligned; that is the only alignment rule that remains for linear descriptors.

## Alignment Requirements

| Field | Alignment | Notes |
|-------|-----------|-------|
| Descriptor address | 32-byte | One descriptor is 32 bytes; an EXTENDED descriptor's chunk 1 is fetched at `+0x20` |
| `next_ptr` [191:160] | 32-byte | 32-bit descriptor address, zero-extended by the engine |
| `dst_addr` [127:64], linear | none | Any byte address |
| `src_addr` [63:0], linear | none | Any byte address |
| `dst_addr` / `src_addr`, EXT | `DATA_WIDTH/8` | Permanent: EXT is beat-aligned |
| `length`, linear | none | Any byte count; 0 moves nothing |
| `length`, EXT | multiple of `DATA_WIDTH/8` | Permanent: EXT counts whole beats |

: Address and Length Alignment

## What Changed from RAPIDS Beats

| Aspect | RAPIDS Beats | RAPIDS |
|--------|--------------|--------|
| Descriptor size and bit layout | 256 bits | Same |
| `length` unit | beats | bytes |
| `length` = 0 | Reserved | Legal: moves nothing, no record, chain continues |
| `src_addr` / `dst_addr` alignment (linear) | `DATA_WIDTH/8` | None |
| Beats moved | `length` | `(offset + length + BYTE_LANES - 1) >> OFF_W` |
| Sink write strobes | All lanes | `WSTRB` marks the bytes written |
| Source packet | Full beats | One packed packet per descriptor, partial last beat |
| Per-descriptor packet record | None | `{bytes, offset}` per enabled direction |
| Sink accepts a packet | Before the descriptor | After the channel's record exists |
| CTRL_READ / CTRL_WRITE | Defined | Unchanged |
| TYPE=EXT | Beat rows | Beat rows, aligned addresses and lengths (permanent) |
| Chaining, `next_ptr`, `last`, `gen_irq` | Defined | Unchanged |

: Descriptor Differences, RAPIDS Beats to RAPIDS

## Descriptor Examples

### Sink Descriptor (Network to Memory)

A 100-byte sink transfer to `0x1_0000_0007`, chained to a descriptor at `0x2000`, raising an interrupt on completion. The destination is 7 bytes into a beat, so `offset` = 7 and `beats_total` = (7 + 100 + 31) >> 5 = 4. The first beat writes lanes 7 to 31, the last beat writes 4 bytes.

```
64-bit words, LSB word first:
[63:0]    = 0x0000_0000_0000_0000  // src_addr  (unused by the SINK half)
[127:64]  = 0x0000_0001_0000_0007  // dst_addr  = 0x1_0000_0007
[191:128] = 0x0000_2000_0000_0064  // next_ptr[191:160]=0x2000, length[159:128]=100
[255:192] = 0x0000_0000_0000_0003  // valid=1, gen_irq=1, last=0
```

### Source Descriptor (Memory to Network)

A 60-byte source transfer from `0x2_0000_0005`, terminating the chain. `offset` = 5 and `beats_total` = (5 + 60 + 31) >> 5 = 3 memory beats. The source emits one AXIS packet of two stream beats: 32 bytes, then 28 bytes with `TLAST`.

```
64-bit words, LSB word first:
[63:0]    = 0x0000_0002_0000_0005  // src_addr = 0x2_0000_0005
[127:64]  = 0x0000_0000_0000_0000  // dst_addr (unused by the SOURCE half)
[191:128] = 0x0000_0000_0000_003C  // next_ptr = 0, length = 60
[255:192] = 0x0000_0000_0000_0007  // valid=1, gen_irq=1, last=1
```

## Software Construction

### C Structure Example

```c
typedef struct __attribute__((packed, aligned(32))) {
    uint64_t src_addr;      // [63:0]     source byte address
    uint64_t dst_addr;      // [127:64]   destination byte address
    uint32_t length;        // [159:128]  transfer length in BYTES
    uint32_t next_ptr;      // [191:160]  32-bit, 0 terminates the chain
    uint32_t flags;         // [223:192]  see macros below
    uint32_t reserved[2];   // [255:224]
} rapids_descriptor_t;

// flags bit positions are relative to descriptor bit 192
#define DESC_VALID          (1u << 0)   // [192]
#define DESC_GEN_IRQ        (1u << 1)   // [193]
#define DESC_LAST           (1u << 2)   // [194]
#define DESC_ERROR          (1u << 3)   // [195] hardware-written
#define DESC_CHANNEL_ID(n)  (((n) & 0xFu) << 4)    // [199:196]
#define DESC_PRIORITY(n)    (((n) & 0xFFu) << 8)   // [207:200]
#define DESC_OPCODE(n)      (((n) & 0x3u) << 16)   // [209:208]
#define DESC_TYPE(n)        (((n) & 0x7u) << 18)   // [212:210]

#define DESC_OP_DATA        0x0
#define DESC_OP_CTRL_READ   0x1
#define DESC_OP_CTRL_WRITE  0x2

#define DESC_TYPE_LEGACY    0x0
#define DESC_TYPE_EXT       0x1

// Beats a linear DATA descriptor touches (BYTE_LANES = 32 for 256-bit)
static inline uint32_t rapids_beats_total(uint64_t addr, uint32_t length)
{
    const uint64_t lanes = 32;
    if (length == 0)
        return 0;
    return (uint32_t)(((addr & (lanes - 1)) + length + lanes - 1) / lanes);
}
```

The helper is for software that wants to size buffers or predict burst counts. The hardware does not need it.

### Descriptor Ring Setup

```c
// Descriptor ring: descriptors must be 32-byte aligned
rapids_descriptor_t *ring = aligned_alloc(32, NUM_DESC * sizeof(*ring));

for (int i = 0; i < NUM_DESC; i++) {
    memset(&ring[i], 0, sizeof(ring[i]));
    ring[i].dst_addr = dst[i];               // any byte address
    ring[i].length   = len[i];               // bytes
    ring[i].flags    = DESC_VALID | DESC_GEN_IRQ;
    if (i < NUM_DESC - 1) {
        ring[i].next_ptr = (uint32_t)(uintptr_t)&ring[i + 1];
    } else {
        ring[i].next_ptr = 0;                // terminates the chain
        ring[i].flags   |= DESC_LAST;
    }
}
```

The descriptor buffers themselves stay 32-byte aligned. The payload addresses do not have to be.
