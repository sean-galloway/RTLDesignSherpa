from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.field_config import FieldConfig

class AXIErrorMonitorSlave:
    """
    Combined monitor/slave for a single AXI error monitoring interface.
    Works with both AXI and AXI-Lite protocols using the unified base error monitor.
    """
    def __init__(self, dut, clock, axi_addr_width=32, axi_id_width=8,
                    title_prefix="Error", randomizer=None, log=None, is_axil=False):
        """
        Initialize the AXI error monitor/slave component.

        Args:
            dut: Device under test
            clock: Clock signal
            axi_addr_width: Width of AXI address bus
            axi_id_width: Width of AXI ID field (for AXI) or 1 (for AXI-Lite)
            title_prefix: Prefix for component names
            randomizer: Randomizer for timing constraints
            log: Logger instance
            is_axil: Flag to indicate if this is for AXI-Lite (no ID field)
        """
        # Store the randomizer for later access
        self.randomizer = randomizer
        self.is_axil = is_axil
        
        # Create field configuration for error reporting interface
        self.field_config = FieldConfig()
        
        # Error type is the same for both AXI and AXI-Lite
        self.field_config.add_field_dict('error_type', {
            'bits': 4,
            'default': 0,
            'format': 'bin',
            'display_width': 4,
            'active_bits': (3, 0),
            'description': 'Error type: [0]=AR/AW timeout, [1]=R/W timeout, [2]=B timeout, [3]=Response error'
        })
        
        # Add ID field only for AXI (not AXI-Lite)
        if not is_axil:
            self.field_config.add_field_dict('error_id', {
                'bits': axi_id_width,
                'default': 0,
                'format': 'hex',
                'display_width': 2,
                'active_bits': (axi_id_width-1, 0),
                'description': 'Transaction ID associated with the error'
            })

        # Address field is common for both AXI and AXI-Lite
        self.field_config.add_field_dict('error_addr', {
            'bits': axi_addr_width,
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (axi_addr_width-1, 0),
            'description': 'Address associated with the error (if applicable)'
        })

        # Define common signal map
        signal_map = {
            'm2s_valid': 'fub_error_valid',
            's2m_ready': 'fub_error_ready'
        }

        # Define signal map based on protocol type
        if is_axil:
            optional_signal_map = {
                'm2s_pkt_error_type': 'fub_error_type',
                'm2s_pkt_error_addr': 'fub_error_addr'
            }
        else:
            optional_signal_map = {
                'm2s_pkt_error_type': 'fub_error_type',
                'm2s_pkt_error_id':   'fub_error_id',
                'm2s_pkt_error_addr': 'fub_error_addr'
            }

        # Create slave for error monitoring
        self.error_slave = GAXISlave(
            dut, f'{title_prefix}ErrSlave', '', clock,
            field_config=self.field_config,
            randomizer=randomizer,
            log=log,
            signal_map=signal_map,
            optional_signal_map=optional_signal_map,
            multi_sig=True
        )

        # Create monitor for error reporting
        self.error_monitor = GAXIMonitor(
            dut, f'{title_prefix}ErrMonitor', '', clock,
            field_config=self.field_config,
            is_slave=True,
            log=log,
            signal_map=signal_map,
            optional_signal_map=optional_signal_map,
            multi_sig=True
        )

    def set_randomizer(self, randomizer):
        """
        Update the randomizer used for timing control.

        Args:
            randomizer: New FlexRandomizer instance
        """
        self.randomizer = randomizer
        self.error_slave.set_randomizer(randomizer)

    async def reset_bus(self):
        """Reset the slave interface"""
        await self.error_slave.reset_bus()

    def add_error_callback(self, callback):
        """Add callback for error monitoring"""
        self.error_monitor.add_callback(callback)

    def clear_queue(self):
        """Clear the monitor queue"""
        self.error_monitor.clear_queue()
        
    def get_error_info(self, error_packet):
        """
        Extract error information from a packet based on protocol type.
        
        Args:
            error_packet: Error packet received from the monitor
            
        Returns:
            Dictionary containing error information
        """
        error_info = {
            'error_type': error_packet.error_type,
            'error_addr': error_packet.error_addr
        }
        
        # Add ID only for AXI (not for AXI-Lite)
        if not self.is_axil:
            error_info['error_id'] = error_packet.error_id
        
        return error_info