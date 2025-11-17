# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2024-2025 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: PIC8259Helper
# Purpose: Human-readable PIC 8259 register programming helper
#
# Author: sean galloway
# Created: 2025-11-15

"""
PIC 8259 Register Programming Helper

Provides human-readable methods for configuring PIC 8259 registers using the
RegisterMap class with auto-generated register definitions.

Example Usage:
    pic = PIC8259Helper('pic_8259_regmap.py', apb_data_width=32, 
                        apb_addr_width=16, start_address=0x0, log=logger)
    
    # Initialize PIC in edge-triggered mode with vector base 0x20
    pic.initialize(vector_base=0x20, edge_triggered=True, 
                   single_mode=True, icw4_needed=True, auto_eoi=True)
    
    # Unmask specific IRQs
    pic.unmask_irqs([0, 1, 2])  # Enable IRQ0, IRQ1, IRQ2
    
    # Send EOI for IRQ5
    pic.send_eoi(5)
    
    # Generate APB cycles
    apb_transactions = pic.generate_apb_cycles()
"""

from typing import List, Optional
from CocoTBFramework.tbclasses.apb.register_map import RegisterMap
from CocoTBFramework.components.apb.apb_packet import APBPacket


# EOI Command Types
EOI_NON_SPECIFIC = 0b001       # Clear highest priority ISR bit
EOI_SPECIFIC = 0b011            # Clear specific ISR bit
EOI_ROTATE_NON_SPECIFIC = 0b101  # Rotate + clear highest ISR
EOI_ROTATE_SPECIFIC = 0b111     # Rotate + clear specific ISR
EOI_ROTATE_AUTO_CLEAR = 0b000   # Clear auto-rotate mode
EOI_ROTATE_AUTO_SET = 0b100     # Set auto-rotate mode
EOI_SET_PRIORITY = 0b110        # Set lowest priority

class PIC8259Helper:
    """
    PIC 8259 Register Programming Helper
    
    Provides intuitive methods for programming PIC 8259 registers without
    needing to know the low-level register/field names or 8259 initialization sequences.
    """
    
    def __init__(self, regmap_file: str, apb_data_width: int, 
                 apb_addr_width: int, start_address: int, log):
        """
        Initialize PIC helper with register map.
        
        Args:
            regmap_file: Path to generated register map file (e.g., 'pic_8259_regmap.py')
            apb_data_width: APB bus data width (typically 32)
            apb_addr_width: APB bus address width
            start_address: Base address of PIC in memory map
            log: Logger instance
        """
        self.reg_map = RegisterMap(regmap_file, apb_data_width, 
                                   apb_addr_width, start_address, log)
        self.log = log
        self.num_irqs = 8  # PIC 8259 has 8 IRQ inputs
        
    def enable_pic(self, enable: bool = True):
        """
        Enable or disable the PIC globally.
        
        Args:
            enable: True to enable, False to disable PIC
        """
        self.reg_map.write('PIC_CONFIG', 'pic_enable', 1 if enable else 0)
        self.log.info(f"PIC {'enabled' if enable else 'disabled'}")
        
    def initialize(self, vector_base: int = 0x20, 
                  edge_triggered: bool = True,
                  single_mode: bool = True, 
                  icw4_needed: bool = True,
                  auto_eoi: bool = False,
                  cascade_config: int = 0x00,
                  buffered_mode: int = 0b00,
                  special_fully_nested: bool = False):
        """
        Initialize PIC with ICW sequence (ICW1-4).
        
        This performs the complete initialization sequence required by the 8259A.
        
        Args:
            vector_base: Interrupt vector base address (bits [7:3], default 0x20 for IRQ 32-39)
            edge_triggered: True for edge-triggered, False for level-triggered
            single_mode: True for single PIC, False for cascade mode
            icw4_needed: True if ICW4 will be written (usually True for 8086 mode)
            auto_eoi: True for automatic EOI, False for normal EOI
            cascade_config: Cascade configuration byte (ICW3)
                           Master: bitmap of cascade IRQ inputs
                           Slave: slave ID (0-7)
            buffered_mode: Buffered mode select (00=non-buffered, 10=buffered slave, 11=buffered master)
            special_fully_nested: True to enable special fully nested mode
        """
        self.log.info("Starting PIC initialization sequence...")
        
        # Set init mode in config register
        self.reg_map.write('PIC_CONFIG', 'init_mode', 1)
        self.reg_map.write('PIC_CONFIG', 'auto_reset_init', 1)  # Auto-clear after ICW4
        
        # ICW1: Initialization control
        self.reg_map.write('PIC_ICW1', 'ic4', 1 if icw4_needed else 0)
        self.reg_map.write('PIC_ICW1', 'sngl', 1 if single_mode else 0)
        self.reg_map.write('PIC_ICW1', 'adi', 0)  # Call address interval (8085 mode)
        self.reg_map.write('PIC_ICW1', 'ltim', 0 if edge_triggered else 1)
        self.reg_map.write('PIC_ICW1', 'icw1_marker', 1)  # Always 1 for ICW1
        
        self.log.info(f"ICW1: edge_trig={edge_triggered}, single={single_mode}, ic4={icw4_needed}")
        
        # ICW2: Interrupt vector base
        self.reg_map.write('PIC_ICW2', 'vector_base', vector_base)
        self.log.info(f"ICW2: vector_base=0x{vector_base:02X}")
        
        # ICW3: Cascade configuration (if not single mode)
        if not single_mode:
            self.reg_map.write('PIC_ICW3', 'cascade', cascade_config)
            self.log.info(f"ICW3: cascade=0x{cascade_config:02X}")
        
        # ICW4: Special modes (if needed)
        if icw4_needed:
            self.reg_map.write('PIC_ICW4', 'upm', 1)  # 8086/8088 mode
            self.reg_map.write('PIC_ICW4', 'aeoi', 1 if auto_eoi else 0)
            self.reg_map.write('PIC_ICW4', 'buf_mode', buffered_mode)
            self.reg_map.write('PIC_ICW4', 'sfnm', 1 if special_fully_nested else 0)
            self.log.info(f"ICW4: auto_eoi={auto_eoi}, buf_mode={buffered_mode:02b}, sfnm={special_fully_nested}")
        
        self.log.info("PIC initialization sequence complete")
        
    def mask_all_irqs(self):
        """
        Mask (disable) all IRQ inputs.
        
        This is useful during initialization or when disabling all interrupts.
        """
        self.reg_map.write('PIC_OCW1', 'imr', 0xFF)
        self.log.info("All IRQs masked")
        
    def unmask_all_irqs(self):
        """
        Unmask (enable) all IRQ inputs.
        
        Use with caution - typically you want to selectively enable IRQs.
        """
        self.reg_map.write('PIC_OCW1', 'imr', 0x00)
        self.log.info("All IRQs unmasked")
        
    def mask_irqs(self, irq_list: List[int]):
        """
        Mask (disable) specific IRQ inputs.
        
        Args:
            irq_list: List of IRQ numbers to mask (0-7)
        """
        for irq in irq_list:
            if not 0 <= irq < self.num_irqs:
                raise ValueError(f"IRQ must be 0-{self.num_irqs-1}")
                
        # Read current IMR (this needs to be tracked internally in real usage)
        # For now, we'll assume we're setting individual bits
        mask_value = 0
        for irq in irq_list:
            mask_value |= (1 << irq)
            
        # In practice, you'd want to read-modify-write
        # For this helper, we'll provide the mask value
        self.reg_map.write('PIC_OCW1', 'imr', mask_value)
        self.log.info(f"IRQs masked: {irq_list}, mask=0x{mask_value:02X}")
        
    def unmask_irqs(self, irq_list: List[int]):
        """
        Unmask (enable) specific IRQ inputs.
        
        Args:
            irq_list: List of IRQ numbers to unmask (0-7)
        """
        for irq in irq_list:
            if not 0 <= irq < self.num_irqs:
                raise ValueError(f"IRQ must be 0-{self.num_irqs-1}")
        
        # Calculate mask: 0 = enabled, 1 = masked
        # Enable only the specified IRQs
        mask_value = 0xFF
        for irq in irq_list:
            mask_value &= ~(1 << irq)
            
        self.reg_map.write('PIC_OCW1', 'imr', mask_value)
        self.log.info(f"IRQs unmasked: {irq_list}, mask=0x{mask_value:02X}")
        
    def set_interrupt_mask(self, mask: int):
        """
        Set interrupt mask register directly.
        
        Args:
            mask: 8-bit mask value (bit=1: masked/disabled, bit=0: unmasked/enabled)
        """
        if not 0 <= mask <= 0xFF:
            raise ValueError("Mask must be 0-255")
            
        self.reg_map.write('PIC_OCW1', 'imr', mask)
        self.log.info(f"IMR set to 0x{mask:02X}")
        
    def send_eoi(self, irq: Optional[int] = None, specific: bool = False):
        """
        Send End-of-Interrupt command.
        
        Args:
            irq: IRQ number for specific EOI (0-7), None for non-specific
            specific: If True, use specific EOI; if False, use non-specific
        """
        if specific and irq is None:
            raise ValueError("Specific EOI requires IRQ number")
            
        if irq is not None and not 0 <= irq < self.num_irqs:
            raise ValueError(f"IRQ must be 0-{self.num_irqs-1}")
        
        if specific and irq is not None:
            # Specific EOI for given IRQ
            self.reg_map.write('PIC_OCW2', 'irq_level', irq)
            self.reg_map.write('PIC_OCW2', 'eoi_cmd', EOI_SPECIFIC)
            self.log.info(f"Specific EOI sent for IRQ{irq}")
        else:
            # Non-specific EOI (clears highest priority ISR bit)
            self.reg_map.write('PIC_OCW2', 'irq_level', 0)
            self.reg_map.write('PIC_OCW2', 'eoi_cmd', EOI_NON_SPECIFIC)
            self.log.info("Non-specific EOI sent")
            
    def send_rotate_eoi(self, irq: Optional[int] = None, specific: bool = False):
        """
        Send EOI with priority rotation.
        
        After EOI, the serviced IRQ becomes lowest priority.
        
        Args:
            irq: IRQ number for specific rotate EOI (0-7), None for non-specific
            specific: If True, use specific rotate EOI; if False, use non-specific
        """
        if specific and irq is None:
            raise ValueError("Specific rotate EOI requires IRQ number")
            
        if irq is not None and not 0 <= irq < self.num_irqs:
            raise ValueError(f"IRQ must be 0-{self.num_irqs-1}")
        
        if specific and irq is not None:
            # Specific rotate EOI
            self.reg_map.write('PIC_OCW2', 'irq_level', irq)
            self.reg_map.write('PIC_OCW2', 'eoi_cmd', EOI_ROTATE_SPECIFIC)
            self.log.info(f"Specific rotate EOI sent for IRQ{irq}")
        else:
            # Non-specific rotate EOI
            self.reg_map.write('PIC_OCW2', 'irq_level', 0)
            self.reg_map.write('PIC_OCW2', 'eoi_cmd', EOI_ROTATE_NON_SPECIFIC)
            self.log.info("Non-specific rotate EOI sent")
            
    def set_priority(self, lowest_priority_irq: int):
        """
        Set priority rotation base (lowest priority IRQ).
        
        In rotating priority mode, this determines which IRQ has lowest priority.
        Priority increases from this IRQ upward (wrapping around).
        
        Args:
            lowest_priority_irq: IRQ number to be lowest priority (0-7)
        """
        if not 0 <= lowest_priority_irq < self.num_irqs:
            raise ValueError(f"IRQ must be 0-{self.num_irqs-1}")
            
        self.reg_map.write('PIC_OCW2', 'irq_level', lowest_priority_irq)
        self.reg_map.write('PIC_OCW2', 'eoi_cmd', EOI_SET_PRIORITY)
        self.log.info(f"Priority base set: IRQ{lowest_priority_irq} is lowest priority")
        
    def enable_auto_rotate_eoi(self, enable: bool = True):
        """
        Enable or disable automatic priority rotation on EOI.
        
        When enabled, priority rotates automatically after each EOI.
        
        Args:
            enable: True to enable auto-rotate, False to disable
        """
        if enable:
            self.reg_map.write('PIC_OCW2', 'irq_level', 0)
            self.reg_map.write('PIC_OCW2', 'eoi_cmd', EOI_ROTATE_AUTO_SET)
            self.log.info("Auto-rotate EOI enabled")
        else:
            self.reg_map.write('PIC_OCW2', 'irq_level', 0)
            self.reg_map.write('PIC_OCW2', 'eoi_cmd', EOI_ROTATE_AUTO_CLEAR)
            self.log.info("Auto-rotate EOI disabled")
            
    def enable_special_mask_mode(self, enable: bool = True):
        """
        Enable or disable special mask mode.
        
        In special mask mode, masked IRQs can still be serviced if no higher
        priority unmasked interrupts are pending.
        
        Args:
            enable: True to enable special mask mode, False to disable
        """
        self.reg_map.write('PIC_OCW3', 'smm_cmd', 0b11 if enable else 0b10)
        self.reg_map.write('PIC_OCW3', 'ocw3_marker', 0b01)  # Identify as OCW3
        self.log.info(f"Special mask mode {'enabled' if enable else 'disabled'}")
        
    def generate_apb_cycles(self) -> List[APBPacket]:
        """
        Generate APB bus cycles for all pending register writes.
        
        Returns:
            List of APBPacket objects ready for bus transaction
        """
        return self.reg_map.generate_apb_cycles()
        
    def initialize_defaults(self):
        """
        Initialize PIC with sensible defaults:
        - Disable PIC globally
        - Edge-triggered mode
        - Single PIC mode (no cascade)
        - 8086 mode with auto-EOI disabled
        - Vector base 0x20 (IRQ 32-39)
        - All IRQs masked
        """
        # Disable PIC
        self.enable_pic(False)
        
        # Initialize with standard PC settings
        self.initialize(
            vector_base=0x20,      # Standard PC IRQ vector base
            edge_triggered=True,    # Edge-triggered
            single_mode=True,       # Single PIC
            icw4_needed=True,       # Need ICW4 for 8086 mode
            auto_eoi=False,         # Normal EOI
            cascade_config=0x00,
            buffered_mode=0b00,     # Non-buffered
            special_fully_nested=False
        )
        
        # Mask all IRQs
        self.mask_all_irqs()
        
        # Enable PIC
        self.enable_pic(True)
        
        self.log.info("PIC initialized to defaults (all IRQs masked)")
        
    def configure_pc_master_pic(self, cascade_irq: int = 2):
        """
        Configure as master PIC in PC-compatible cascade configuration.
        
        Standard PC configuration:
        - Master PIC: IRQ0-7 (vectors 0x20-0x27)
        - Slave PIC cascaded on IRQ2
        
        Args:
            cascade_irq: IRQ line where slave is connected (typically 2)
        """
        cascade_mask = 1 << cascade_irq
        
        self.initialize(
            vector_base=0x20,
            edge_triggered=True,
            single_mode=False,      # Cascade mode
            icw4_needed=True,
            auto_eoi=False,
            cascade_config=cascade_mask,  # Cascade on IRQ2
            buffered_mode=0b11,     # Buffered master
            special_fully_nested=False
        )
        
        self.log.info(f"Configured as master PIC (cascade on IRQ{cascade_irq})")
        
    def configure_pc_slave_pic(self, slave_id: int = 2):
        """
        Configure as slave PIC in PC-compatible cascade configuration.
        
        Standard PC configuration:
        - Slave PIC: IRQ8-15 (vectors 0x28-0x2F)
        - Connected to master IRQ2
        
        Args:
            slave_id: Cascade input number on master (typically 2)
        """
        self.initialize(
            vector_base=0x28,       # Slave vectors 0x28-0x2F
            edge_triggered=True,
            single_mode=False,      # Cascade mode
            icw4_needed=True,
            auto_eoi=False,
            cascade_config=slave_id,  # Slave ID = 2
            buffered_mode=0b10,     # Buffered slave
            special_fully_nested=False
        )
        
        self.log.info(f"Configured as slave PIC (slave ID={slave_id})")
