"""
Utility class for building STREAM descriptor packets.

Purpose: Helper to create 512-bit descriptor packets from descriptor fields.
         The scheduler expects 512-bit packets where bits [255:0] contain
         the actual descriptor data and bits [511:256] are reserved.

Author: sean galloway
Created: 2025-11-01
"""


class DescriptorPacketBuilder:
    """Build 512-bit STREAM descriptor packets."""

    @staticmethod
    def build_descriptor_packet(src_addr, dst_addr, length, next_ptr=0,
                               valid=True, gen_irq=False, last=False,
                               error=False, channel_id=0, priority=0):
        """Build a 512-bit descriptor packet.

        Args:
            src_addr (int): Source address (64-bit, must be aligned)
            dst_addr (int): Destination address (64-bit, must be aligned)
            length (int): Transfer length in BEATS (32-bit)
            next_ptr (int): Next descriptor pointer (32-bit, 0=last)
            valid (bool): Descriptor valid flag
            gen_irq (bool): Generate interrupt on completion
            last (bool): Last descriptor in chain
            error (bool): Error flag
            channel_id (int): Channel ID (4-bit, informational)
            priority (int): Descriptor priority (8-bit)

        Returns:
            int: 512-bit descriptor packet

        Descriptor Layout (512-bit packet):
            [63:0]    - src_addr
            [127:64]  - dst_addr
            [159:128] - length (in BEATS, not bytes!)
            [191:160] - next_descriptor_ptr
            [192]     - valid
            [193]     - gen_irq
            [194]     - last
            [195]     - error
            [199:196] - channel_id
            [207:200] - priority
            [255:208] - reserved (48 bits)
            [511:256] - reserved (256 bits)
        """
        # Build control byte [199:192]
        control_low = (
            (1 if valid else 0) |           # [192]
            ((1 if gen_irq else 0) << 1) |  # [193]
            ((1 if last else 0) << 2) |     # [194]
            ((1 if error else 0) << 3) |    # [195]
            ((channel_id & 0xF) << 4)       # [199:196]
        )

        # Build priority byte [207:200]
        priority_byte = priority & 0xFF

        # Assemble 256-bit descriptor (lower half of 512-bit packet)
        descriptor_256 = (
            (src_addr & 0xFFFFFFFFFFFFFFFF) |         # [63:0]
            ((dst_addr & 0xFFFFFFFFFFFFFFFF) << 64) |  # [127:64]
            ((length & 0xFFFFFFFF) << 128) |           # [159:128]
            ((next_ptr & 0xFFFFFFFF) << 160) |         # [191:160]
            (control_low << 192) |                      # [199:192]
            (priority_byte << 200)                      # [207:200]
            # [255:208] remain 0 (reserved)
        )

        # Upper 256 bits are reserved (all zeros)
        # Final 512-bit packet = descriptor_256 + 0 in upper bits
        return descriptor_256

    # ------------------------------------------------------------------
    # Extended (TASK-101 row/col) descriptor format. THE single definition:
    # both the component TB (write_ext_descriptor) and the FPGA char flow
    # (descriptor_builder.build_ext) build from this -- the flows link here,
    # never the reverse. Two 256-bit slots: chunk0 = legacy layout with
    # desc_type=EXT, chunk1 = the dma_address_gen config.
    # ------------------------------------------------------------------
    DESC_TYPE_EXT = 1   # desc_type field (bits [210:208]) value for extended

    @staticmethod
    def build_extended_words(src_addr, dst_addr, beats, rd, wr, *,
                             channel_id=0, next_ptr=0, last=True, gen_irq=True):
        """16 x 32-bit words for one EXTENDED descriptor: chunk0[0:8] at
        descriptor index idx, chunk1[8:16] at idx+1.

        rd/wr = {'s0','s1','inner','w0'(=0),'w1'(=0)}: signed byte strides s0/s1,
        index_0 extent 'inner', log2 wrap windows w0/w1 (0=off). Address model
        (mirrored by StreamCoreTB._ext_addr_set and rtl dma_address_gen):
        addr = base + i0*s0 + i1*s1, i0 in [0,inner), i1 in [0, beats/inner)."""
        ctrl = (1                                  # [192] valid
                | ((1 if gen_irq else 0) << 1)     # [193] irq
                | ((1 if last else 0) << 2)        # [194] last
                | ((channel_id & 0xF) << 4))       # [199:196] channel_id
        chunk0 = [
            src_addr & 0xFFFFFFFF, (src_addr >> 32) & 0xFFFFFFFF,
            dst_addr & 0xFFFFFFFF, (dst_addr >> 32) & 0xFFFFFFFF,
            beats & 0xFFFFFFFF,
            next_ptr & 0xFFFFFFFF,
            (ctrl | (DescriptorPacketBuilder.DESC_TYPE_EXT << 16)) & 0xFFFFFFFF,
            0,
        ]

        def _dim(inner, w0, w1):   # inner[15:0] | wrap0[21:16] | wrap1[27:22]
            return (inner & 0xFFFF) | ((w0 & 0x3F) << 16) | ((w1 & 0x3F) << 22)
        u32 = lambda v: v & 0xFFFFFFFF
        chunk1 = [
            u32(rd['s0']), u32(rd['s1']), _dim(rd['inner'], rd.get('w0', 0), rd.get('w1', 0)),
            u32(wr['s0']), u32(wr['s1']), _dim(wr['inner'], wr.get('w0', 0), wr.get('w1', 0)),
            0, 0,
        ]
        return chunk0 + chunk1

    @staticmethod
    def extract_src_addr(packet):
        """Extract source address from descriptor packet."""
        return packet & 0xFFFFFFFFFFFFFFFF

    @staticmethod
    def extract_dst_addr(packet):
        """Extract destination address from descriptor packet."""
        return (packet >> 64) & 0xFFFFFFFFFFFFFFFF

    @staticmethod
    def extract_length(packet):
        """Extract length (in beats) from descriptor packet."""
        return (packet >> 128) & 0xFFFFFFFF

    @staticmethod
    def extract_next_ptr(packet):
        """Extract next descriptor pointer from descriptor packet."""
        return (packet >> 160) & 0xFFFFFFFF

    @staticmethod
    def extract_valid(packet):
        """Extract valid flag from descriptor packet."""
        return bool((packet >> 192) & 0x1)

    @staticmethod
    def extract_gen_irq(packet):
        """Extract interrupt flag from descriptor packet."""
        return bool((packet >> 193) & 0x1)

    @staticmethod
    def extract_last(packet):
        """Extract last flag from descriptor packet."""
        return bool((packet >> 194) & 0x1)

    @staticmethod
    def extract_error(packet):
        """Extract error flag from descriptor packet."""
        return bool((packet >> 195) & 0x1)

    @staticmethod
    def extract_channel_id(packet):
        """Extract channel ID from descriptor packet."""
        return (packet >> 196) & 0xF

    @staticmethod
    def extract_priority(packet):
        """Extract priority from descriptor packet."""
        return (packet >> 200) & 0xFF

    @staticmethod
    def format_packet(packet):
        """Format descriptor packet as human-readable string."""
        return (
            f"Descriptor Packet:\n"
            f"  src_addr:  0x{DescriptorPacketBuilder.extract_src_addr(packet):016X}\n"
            f"  dst_addr:  0x{DescriptorPacketBuilder.extract_dst_addr(packet):016X}\n"
            f"  length:    {DescriptorPacketBuilder.extract_length(packet)} beats\n"
            f"  next_ptr:  0x{DescriptorPacketBuilder.extract_next_ptr(packet):08X}\n"
            f"  valid:     {DescriptorPacketBuilder.extract_valid(packet)}\n"
            f"  gen_irq:   {DescriptorPacketBuilder.extract_gen_irq(packet)}\n"
            f"  last:      {DescriptorPacketBuilder.extract_last(packet)}\n"
            f"  error:     {DescriptorPacketBuilder.extract_error(packet)}\n"
            f"  channel:   {DescriptorPacketBuilder.extract_channel_id(packet)}\n"
            f"  priority:  {DescriptorPacketBuilder.extract_priority(packet)}"
        )


# Example usage
if __name__ == "__main__":
    # Create a descriptor packet
    packet = DescriptorPacketBuilder.build_descriptor_packet(
        src_addr=0x80000000,
        dst_addr=0x90000000,
        length=64,  # 64 beats
        next_ptr=0,  # Last descriptor
        valid=True,
        last=True,
        channel_id=0
    )

    print(f"Packet value: 0x{packet:0128X}")
    print(DescriptorPacketBuilder.format_packet(packet))

    # Verify extraction
    assert DescriptorPacketBuilder.extract_src_addr(packet) == 0x80000000
    assert DescriptorPacketBuilder.extract_dst_addr(packet) == 0x90000000
    assert DescriptorPacketBuilder.extract_length(packet) == 64
    assert DescriptorPacketBuilder.extract_valid(packet) == True
    assert DescriptorPacketBuilder.extract_last(packet) == True
    print("\nAll assertions passed!")
