# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2026 sean galloway
"""Model of the a7ddrphy 4-phase read de-interleave window — the mechanism
behind the on-board pumice read corruption (task #143).

The generated a7ddrphy is nphases=4: a read burst deserializes into an 8-slot
window = 4 DFI phases (p0..p3) x 2 x16 device-words each
    slot:  0    1   | 2    3   | 4    5   | 6    7
    phase: p0.a p0.b| p1.a p1.b| p2.a p2.b| p3.a p3.b
The pumice controller runs DFI_RATE=2 and reads only {p1,p0} = slots [0:4],
assembling the 64b DFI word as {p1, p0} = slot3<<48 | slot2<<32 | slot1<<16 | slot0.

A BL4 read delivers 4 device-words. WHERE they land in the 8-slot window is set
by the read-latency / rddata_en alignment. When that alignment is correct the 4
device-words occupy slots [0:4] and {p1,p0} is exact. The rearchitecture's added
pipeline depth shifts the alignment by `slot_offset` slots, so {p1,p0} grabs the
WRONG four slots -> shifted device-words + zeros: exactly the ILA signatures
(0x..a5a0 = one shifted device-word + zeros; phase1==phase0 = a duplicated slot).

This is the model to plug into DFISlavePHY (return {p1,p0} of this window instead
of the ideal 2-phase data) so the sim reproduces the board and the committed
device-word assertion (axi_rd_device_word_check) fires.
"""
from typing import List


def place_read_window(device_words: List[int], slot_offset: int,
                      n_slots: int = 8) -> List[int]:
    """Lay the BL4 read's device-words into the 8-slot 4-phase window at
    `slot_offset` (rest = 0, modelling stale/empty deserializer slots)."""
    win = [0] * n_slots
    for i, dw in enumerate(device_words):
        s = slot_offset + i
        if 0 <= s < n_slots:
            win[s] = dw
    return win


def read_p1p0(window: List[int], dw_bits: int = 16) -> int:
    """The controller's {p1,p0} readout = slots [0:4] assembled to a 64b word:
    slot3<<48 | slot2<<32 | slot1<<16 | slot0."""
    s = window[0:4]
    return (s[3] << (3 * dw_bits)) | (s[2] << (2 * dw_bits)) \
        | (s[1] << dw_bits) | s[0]


def beat_from_golden(golden64: int, slot_offset: int, dw_bits: int = 16) -> int:
    """End-to-end: take the correct 64b beat (4 device-words), model the 4-phase
    window at slot_offset, and return what the controller's {p1,p0} readout is.
    slot_offset==0 => bit-exact passthrough (the working case)."""
    m = (1 << dw_bits) - 1
    dws = [(golden64 >> (k * dw_bits)) & m for k in range(4)]
    return read_p1p0(place_read_window(dws, slot_offset), dw_bits)
