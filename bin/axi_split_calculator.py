#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: axi_split_calculator
# Purpose: AXI Split Logic Calculator
#
# Documentation: rtl/common/PRD.md
# Subsystem: common
#
# Author: sean galloway
# Created: 2025-10-18

"""
AXI Split Logic Calculator

Simple script to calculate AXI transaction splitting given:
- AW: Address width (bits)
- DW: Data width (bits) 
- alignment_mask: Boundary alignment mask (e.g., 0xFFF for 4KB)
- addr: Starting address
- len: Transaction length (AXI encoding: beats - 1)

Outputs:
- split_required: True/False
- next_boundary_addr: Address of next boundary
- split_len: Length of first split (AXI encoding)
- remaining_len: Length after split (AXI encoding)
"""

def calculate_axi_split(aw, dw, alignment_mask, addr, length):
    """
    Calculate AXI split logic
    
    Args:
        aw: Address width in bits
        dw: Data width in bits
        alignment_mask: Boundary mask (e.g., 0xFFF for 4KB boundaries)
        addr: Starting address
        length: Transaction length in AXI encoding (beats - 1)
    
    Returns:
        dict with split calculation results
    """
    
    # Calculate derived parameters
    bytes_per_beat = dw // 8
    addr_align_mask = bytes_per_beat - 1
    max_addr = (1 << aw) - 1
    
    # Align address to data width boundary
    aligned_addr = addr & ~addr_align_mask
    
    # Calculate transaction parameters
    total_beats = length + 1  # Convert from AXI encoding
    total_bytes = total_beats * bytes_per_beat
    transaction_end_addr = (aligned_addr + total_bytes - 1) & max_addr
    
    # Calculate next boundary address
    next_boundary_addr = ((aligned_addr | alignment_mask) + 1) & max_addr
    
    # Calculate bytes and beats to boundary (handle wraparound)
    if next_boundary_addr > aligned_addr:
        bytes_to_boundary = next_boundary_addr - aligned_addr
    else:
        # Address space wraparound case
        bytes_to_boundary = (max_addr - aligned_addr + 1) + next_boundary_addr
        
    beats_to_boundary = bytes_to_boundary // bytes_per_beat
    
    # Determine if split is required
    if next_boundary_addr > aligned_addr:
        crosses_boundary = transaction_end_addr >= next_boundary_addr
    else:
        # Wraparound case
        crosses_boundary = (transaction_end_addr >= next_boundary_addr) or (aligned_addr > transaction_end_addr)
    
    has_beats_before_boundary = beats_to_boundary > 0
    split_required = crosses_boundary and has_beats_before_boundary
    
    # Calculate split lengths
    if split_required:
        # Split length (AXI encoding: beats - 1)
        split_len = beats_to_boundary - 1
        
        # Remaining length after split
        remaining_beats = total_beats - beats_to_boundary
        remaining_len = remaining_beats - 1 if remaining_beats > 0 else 0
    else:
        split_len = length
        remaining_len = 0
    
    # Calculate boundary info
    boundary_size = alignment_mask + 1
    
    return {
        'inputs': {
            'aw': aw,
            'dw': dw,
            'alignment_mask': f"0x{alignment_mask:03X}",
            'boundary_size': boundary_size,
            'addr': f"0x{addr:08X}",
            'aligned_addr': f"0x{aligned_addr:08X}",
            'length': length,
            'total_beats': total_beats,
            'total_bytes': total_bytes,
            'bytes_per_beat': bytes_per_beat
        },
        'calculation': {
            'transaction_end_addr': f"0x{transaction_end_addr:08X}",
            'next_boundary_addr': f"0x{next_boundary_addr:08X}",
            'bytes_to_boundary': bytes_to_boundary,
            'beats_to_boundary': beats_to_boundary,
            'crosses_boundary': crosses_boundary,
            'has_beats_before_boundary': has_beats_before_boundary
        },
        'results': {
            'split_required': split_required,
            'split_len': split_len,
            'remaining_len': remaining_len,
            'split_beats': split_len + 1 if split_required else 0,
            'remaining_beats': remaining_len + 1 if split_required and remaining_len >= 0 else 0
        }
    }

def print_split_result(result):
    """Print formatted split calculation result"""
    
    print("=" * 80)
    print("AXI SPLIT CALCULATION RESULT")
    print("=" * 80)
    
    # Input parameters
    inp = result['inputs']
    print("📥 INPUTS:")
    print(f"   Address Width:     {inp['aw']} bits")
    print(f"   Data Width:        {inp['dw']} bits ({inp['bytes_per_beat']} bytes/beat)")
    print(f"   Alignment Mask:    {inp['alignment_mask']} (boundary size = {inp['boundary_size']} bytes)")
    print(f"   Start Address:     {inp['addr']} (aligned: {inp['aligned_addr']})")
    print(f"   Transaction:       len={inp['length']} ({inp['total_beats']} beats, {inp['total_bytes']} bytes)")
    print()
    
    # Calculation details
    calc = result['calculation']
    print("🔍 CALCULATION DETAILS:")
    print(f"   Transaction End:   {calc['transaction_end_addr']}")
    print(f"   Next Boundary:     {calc['next_boundary_addr']}")
    print(f"   Bytes to Boundary: {calc['bytes_to_boundary']}")
    print(f"   Beats to Boundary: {calc['beats_to_boundary']}")
    print(f"   Crosses Boundary:  {calc['crosses_boundary']}")
    print(f"   Has Beats Before:  {calc['has_beats_before_boundary']}")
    print()
    
    # Results
    res = result['results']
    print("📤 RESULTS:")
    print(f"   Split Required:    {res['split_required']}")
    
    if res['split_required']:
        print(f"   Split Length:      {res['split_len']} (AXI) = {res['split_beats']} beats")
        print(f"   Remaining Length:  {res['remaining_len']} (AXI) = {res['remaining_beats']} beats")
        print()
        print("   📊 VERIFICATION:")
        total_split_beats = res['split_beats'] + res['remaining_beats']
        conservation_ok = total_split_beats == inp['total_beats']
        status = "✅" if conservation_ok else "❌"
        print(f"   Beat Conservation: {res['split_beats']} + {res['remaining_beats']} = {total_split_beats} (expected {inp['total_beats']}) {status}")
    else:
        print(f"   No split needed - transaction fits before boundary")
    
    print("=" * 80)

def interactive_calculator():
    """Interactive AXI split calculator"""
    
    print("AXI Split Logic Calculator")
    print("Enter 'q' to quit, 'h' for help\n")
    
    # Default values
    aw = 32
    dw = 32
    alignment_mask = 0xFFF
    
    while True:
        try:
            print(f"Current defaults: AW={aw}, DW={dw}, mask=0x{alignment_mask:X}")
            
            # Get input
            user_input = input("\nEnter: addr,len OR addr,len,dw,mask OR 'set aw=32 dw=64 mask=0xFFF' OR 'q': ").strip()
            
            if user_input.lower() == 'q':
                break
            elif user_input.lower() == 'h':
                print_help()
                continue
            elif user_input.lower().startswith('set'):
                # Parse set command
                try:
                    parts = user_input.split()[1:]  # Skip 'set'
                    for part in parts:
                        key, val = part.split('=')
                        if key.lower() == 'aw':
                            aw = int(val)
                        elif key.lower() == 'dw':
                            dw = int(val)
                        elif key.lower() == 'mask':
                            alignment_mask = int(val, 0)  # Auto-detect hex/decimal
                    print(f"Updated defaults: AW={aw}, DW={dw}, mask=0x{alignment_mask:X}")
                    continue
                except:
                    print("Error parsing set command. Use: set aw=32 dw=64 mask=0xFFF")
                    continue
            
            # Parse calculation input
            parts = user_input.split(',')
            
            if len(parts) == 2:
                # addr,len - use current defaults
                addr = int(parts[0].strip(), 0)
                length = int(parts[1].strip())
                current_dw = dw
                current_mask = alignment_mask
            elif len(parts) == 4:
                # addr,len,dw,mask
                addr = int(parts[0].strip(), 0)
                length = int(parts[1].strip())
                current_dw = int(parts[2].strip())
                current_mask = int(parts[3].strip(), 0)
            else:
                print("Invalid input format. Examples:")
                print("  0x1000,15          (addr=0x1000, len=15, use defaults)")
                print("  0x1000,15,64,0xFFF (addr=0x1000, len=15, dw=64, mask=0xFFF)")
                continue
            
            # Calculate and display result
            result = calculate_axi_split(aw, current_dw, current_mask, addr, length)
            print_split_result(result)
            
        except KeyboardInterrupt:
            print("\nGoodbye!")
            break
        except Exception as e:
            print(f"Error: {e}")
            print("Try 'h' for help")

def print_help():
    """Print help information"""
    print("\n" + "=" * 60)
    print("AXI SPLIT CALCULATOR HELP")
    print("=" * 60)
    print("USAGE:")
    print("  addr,len                    - Calculate with current defaults")
    print("  addr,len,dw,mask           - Calculate with specific parameters")
    print("  set aw=32 dw=64 mask=0xFFF - Update defaults")
    print("  h                          - Show this help")
    print("  q                          - Quit")
    print()
    print("EXAMPLES:")
    print("  0x1000,15                  - addr=0x1000, len=15 (16 beats)")
    print("  0x1FFC,3,32,0xFFF         - addr=0x1FFC, len=3, dw=32, 4KB boundary")
    print("  0x100FC,1,512,0xFF        - addr=0x100FC, len=1, dw=512, 256B boundary")
    print()
    print("PARAMETERS:")
    print("  addr  - Starting address (hex: 0x1000 or decimal: 4096)")
    print("  len   - AXI length encoding (beats - 1)")
    print("  dw    - Data width in bits (32, 64, 128, 256, 512)")
    print("  mask  - Alignment mask (0xFF=256B, 0xFFF=4KB, 0x3FF=1KB)")
    print("=" * 60 + "\n")

def run_examples():
    """Run some example calculations"""
    
    examples = [
        # (aw, dw, mask, addr, len, description)
        (32, 32, 0xFFF, 0x1000, 15, "32-bit data, 4KB boundary, no split"),
        (32, 32, 0xFFF, 0x1FFC, 3, "32-bit data, 4KB boundary, crosses boundary"),
        (32, 64, 0xFFF, 0x1FF8, 1, "64-bit data, 4KB boundary, crosses boundary"),
        (32, 512, 0xFF, 0x100C0, 1, "512-bit data, 256B boundary, crosses boundary"),
        (32, 512, 0xFF, 0x100FC, 1, "512-bit data, 256B boundary, 1 beat before"),
    ]
    
    print("AXI SPLIT CALCULATOR - EXAMPLE CALCULATIONS")
    print("=" * 80)
    
    for i, (aw, dw, mask, addr, length, desc) in enumerate(examples, 1):
        print(f"\nEXAMPLE {i}: {desc}")
        result = calculate_axi_split(aw, dw, mask, addr, length)
        print_split_result(result)
        input("Press Enter for next example...")

if __name__ == "__main__":
    import sys
    
    if len(sys.argv) > 1 and sys.argv[1] == "examples":
        run_examples()
    elif len(sys.argv) == 6:
        # Command line mode: aw dw mask addr len
        aw = int(sys.argv[1])
        dw = int(sys.argv[2]) 
        mask = int(sys.argv[3], 0)
        addr = int(sys.argv[4], 0)
        length = int(sys.argv[5])
        
        result = calculate_axi_split(aw, dw, mask, addr, length)
        print_split_result(result)
    else:
        interactive_calculator()
