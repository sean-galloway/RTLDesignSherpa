from CocoTBFramework.components.gaxi.gaxi_slave import GAXISlave
from CocoTBFramework.components.gaxi.gaxi_monitor import GAXIMonitor
from CocoTBFramework.components.field_config import FieldConfig

class AXISplitMonitorSlave:
    """
    Combined monitor/slave for a single AXI split monitoring interface.
    Works with the updated splitter design that provides consistent behavior
    between read and write protocols.
    """
    def __init__(self, dut, clock, axi_addr_width=32, axi_id_width=8,
                    title_prefix="Split", randomizer=None, log=None):
        """
        Initialize the AXI split monitor/slave component.

        Args:
            dut: Device under test
            clock: Clock signal
            axi_addr_width: Width of AXI address bus
            axi_id_width: Width of AXI ID field
            title_prefix: Prefix for component names
            randomizer: Randomizer for timing constraints
            log: Logger instance
        """
        # Store the randomizer for later access
        self.randomizer = randomizer

        # Create field configuration for split reporting interface
        # This remains largely the same as the updated splitters maintain
        # the same interface for reporting split transactions
        self.field_config = FieldConfig()
        
        self.field_config.add_field_dict('split_addr', {
            'bits': axi_addr_width,
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (axi_addr_width-1, 0),
            'description': 'Original address of the split transaction'
        })
        
        self.field_config.add_field_dict('split_id', {
            'bits': axi_id_width,
            'default': 0,
            'format': 'hex',
            'display_width': 2,
            'active_bits': (axi_id_width-1, 0),
            'description': 'Transaction ID associated with the split transaction'
        })
        
        self.field_config.add_field_dict('split_cnt', {
            'bits': 8,
            'default': 0,
            'format': 'dec',
            'display_width': 3,
            'active_bits': (7, 0),
            'description': 'Number of splits for the transaction'
        })

        # Signal maps remain unchanged as the interface is consistent
        # between the old and new implementations
        signal_map = {
            'm2s_valid': 'fub_split_valid',
            's2m_ready': 'fub_split_ready'
        }
        
        optional_signal_map = {
            'm2s_pkt_split_addr': 'fub_split_addr',
            'm2s_pkt_split_id':   'fub_split_id',
            'm2s_pkt_split_cnt':  'fub_split_cnt'
        }

        # Create slave for split tracking
        self.split_slave = GAXISlave(
            dut, f'{title_prefix}SplitSlave', '', clock,
            field_config=self.field_config,
            randomizer=randomizer,
            log=log,
            signal_map=signal_map,
            optional_signal_map=optional_signal_map,
            multi_sig=True
        )

        # Create monitor for split reporting
        self.split_monitor = GAXIMonitor(
            dut, f'{title_prefix}SplitMonitor', '', clock,
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
        self.split_slave.set_randomizer(randomizer)

    async def reset_bus(self):
        """Reset the slave interface"""
        await self.split_slave.reset_bus()

    def add_split_callback(self, callback):
        """Add callback for split monitoring"""
        self.split_monitor.add_callback(callback)

    def clear_queue(self):
        """Clear the monitor queue"""
        self.split_monitor.clear_queue()
    
    def get_split_info(self, split_packet):
        """
        Extract split information from a packet.
        
        Args:
            split_packet: Split packet received from the monitor
            
        Returns:
            Dictionary containing split information
        """
        return {
            'split_addr': split_packet.split_addr,
            'split_id': split_packet.split_id,
            'split_cnt': split_packet.split_cnt,
        }