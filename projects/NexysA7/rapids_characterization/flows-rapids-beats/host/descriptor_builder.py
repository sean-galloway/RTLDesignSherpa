# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# Module: descriptor_builder
# Purpose: Build 256-bit RAPIDS descriptors for the rapids_char_top host
#          campaign. Mirrors the descriptor layout in
#          projects/components/rapids/rtl/includes/rapids_pkg.sv and the
#          create_descriptor() helper in the cocotb harness TB
#          (dv/rapids_char_harness_tb.py) so the on-chip descriptor engine sees
#          exactly the same bytes whether kicked from sim or from the board.
#
# Descriptor layout (256 bits, 4 x 64-bit words), from rapids_pkg.sv:
#   [63:0]    src_addr             (DATA: source byte address)
#   [127:64]  dst_addr             (DATA: destination byte address)
#   [159:128] length               (transfer length in BEATS, not bytes)
#   [191:160] next_descriptor_ptr  (0 = last in chain)
#   [192]     valid
#   [193]     gen_irq              (informational)
#   [194]     last
#   [195]     error
#   [199:196] channel_id
#   [207:200] desc_priority
#   [209:208] opcode               (0=DATA, 1=CTRL_READ, 2=CTRL_WRITE)
#   [255:210] reserved
#
# Control-descriptor field reuse (SAME 256-bit word, reinterpreted by opcode):
#   CTRL_READ : poll_addr=[63:0]  expected=[95:64]  mask=[127:96]  max_try=[143:128]
#   CTRL_WRITE: wr_addr  =[63:0]  wr_data =[95:64]
#
# Author: sean galloway
# Created: 2026-07-04

"""RAPIDS 256-bit descriptor builder (host side, dependency-free)."""

from dataclasses import dataclass

# Opcodes (rapids_pkg.sv desc_opcode_t, bits [209:208]).
DESC_OP_DATA = 0
DESC_OP_CTRL_READ = 1
DESC_OP_CTRL_WRITE = 2

DESC_WIDTH_BITS = 256
DESC_WIDTH_WORDS = DESC_WIDTH_BITS // 32

_MASK64 = (1 << 64) - 1
_MASK32 = (1 << 32) - 1
_MASK16 = (1 << 16) - 1


def _u(value: int, width: int) -> int:
    """Mask a value to `width` bits (raises on negative)."""
    if value < 0:
        raise ValueError(f"descriptor field must be non-negative, got {value}")
    return value & ((1 << width) - 1)


def build_data_descriptor(src_addr: int, dst_addr: int, length_beats: int,
                          channel_id: int = 0, *, last: bool = True,
                          gen_irq: bool = False, next_ptr: int = 0,
                          priority: int = 0) -> int:
    """Build a DATA (opcode 0) descriptor.

    length_beats is in BEATS (matches rapids_pkg / the cocotb TB), not bytes.
    For a SINK transfer set src_addr=0 and dst_addr to the sink data address;
    for a SOURCE transfer set src_addr to the source data address and dst_addr=0
    (exactly as run_sink_selfcheck / run_source_selfcheck do in the TB).
    """
    desc = 0
    desc |= _u(src_addr, 64)
    desc |= _u(dst_addr, 64) << 64
    desc |= _u(length_beats, 32) << 128
    desc |= _u(next_ptr, 32) << 160
    desc |= 1 << 192                              # valid
    desc |= (1 if gen_irq else 0) << 193
    desc |= (1 if last else 0) << 194
    desc |= 0 << 195                              # error
    desc |= _u(channel_id, 4) << 196
    desc |= _u(priority, 8) << 200
    desc |= DESC_OP_DATA << 208
    return desc


def build_ctrl_read_descriptor(poll_addr: int, expected: int, mask: int,
                               max_try: int = 0, channel_id: int = 0, *,
                               last: bool = True, gen_irq: bool = False,
                               next_ptr: int = 0, priority: int = 0) -> int:
    """Build a CTRL_READ (opcode 1) consumer-gate descriptor.

    Polls poll_addr until (read & mask) == expected. max_try=0 uses the config
    default retry budget.
    """
    desc = 0
    desc |= _u(poll_addr, 64)                     # [63:0]   reuses src_addr slot
    desc |= _u(expected, 32) << 64                # [95:64]  reuses dst_addr[31:0]
    desc |= _u(mask, 32) << 96                    # [127:96] reuses dst_addr[63:32]
    desc |= _u(max_try, 16) << 128                # [143:128] reuses length[15:0]
    desc |= _u(next_ptr, 32) << 160
    desc |= 1 << 192                              # valid
    desc |= (1 if gen_irq else 0) << 193
    desc |= (1 if last else 0) << 194
    desc |= _u(channel_id, 4) << 196
    desc |= _u(priority, 8) << 200
    desc |= DESC_OP_CTRL_READ << 208
    return desc


def build_ctrl_write_descriptor(wr_addr: int, wr_data: int, channel_id: int = 0,
                                *, last: bool = True, gen_irq: bool = False,
                                next_ptr: int = 0, priority: int = 0) -> int:
    """Build a CTRL_WRITE (opcode 2) producer-doorbell descriptor.

    Writes wr_data to wr_addr, then continues the chain.
    """
    desc = 0
    desc |= _u(wr_addr, 64)                        # [63:0]  reuses src_addr slot
    desc |= _u(wr_data, 32) << 64                 # [95:64] reuses dst_addr[31:0]
    desc |= _u(next_ptr, 32) << 160
    desc |= 1 << 192                              # valid
    desc |= (1 if gen_irq else 0) << 193
    desc |= (1 if last else 0) << 194
    desc |= _u(channel_id, 4) << 196
    desc |= _u(priority, 8) << 200
    desc |= DESC_OP_CTRL_WRITE << 208
    return desc


def descriptor_to_words(desc: int) -> list:
    """Split a 256-bit descriptor into 8 little-endian 32-bit words.

    words[0] = desc[31:0] ... words[7] = desc[255:224], matching the
    DESC_WORD[0..7] assembly order the rapids_char_top DESC-LOAD region expects.
    """
    desc &= (1 << DESC_WIDTH_BITS) - 1
    return [(desc >> (32 * i)) & _MASK32 for i in range(DESC_WIDTH_WORDS)]


def words_to_descriptor(words) -> int:
    """Inverse of descriptor_to_words (handy for round-trip verification)."""
    desc = 0
    for i, w in enumerate(words):
        desc |= (_u(w, 32)) << (32 * i)
    return desc


@dataclass(frozen=True)
class DecodedDescriptor:
    """Human-readable decode of a DATA descriptor (for logging/dumps)."""
    opcode: int
    src_addr: int
    dst_addr: int
    length_beats: int
    next_ptr: int
    valid: int
    last: int
    channel_id: int


def decode_data_descriptor(desc: int) -> DecodedDescriptor:
    """Decode the DATA-view fields of a 256-bit descriptor."""
    return DecodedDescriptor(
        opcode=(desc >> 208) & 0x3,
        src_addr=desc & _MASK64,
        dst_addr=(desc >> 64) & _MASK64,
        length_beats=(desc >> 128) & _MASK32,
        next_ptr=(desc >> 160) & _MASK32,
        valid=(desc >> 192) & 0x1,
        last=(desc >> 194) & 0x1,
        channel_id=(desc >> 196) & 0xF,
    )
