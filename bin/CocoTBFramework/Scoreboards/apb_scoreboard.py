"""APB Scoreboard for verifying APB transactions"""
from CocoTBFramework.Componentsapb import APBCycle
from .scoreboard_base import BaseScoreboard


class APBScoreboard(BaseScoreboard):
    """Scoreboard for APB transactions"""
    
    def __init__(self, name, addr_width=32, data_width=32, log=None):
        super().__init__(name, log)
        self.addr_width = addr_width
        self.data_width = data_width
        self.strb_width = data_width // 8
        
    def _compare_transactions(self, expected, actual):
        """Compare APB cycles based on direction, address, and data"""
        if not isinstance(expected, APBCycle) or not isinstance(actual, APBCycle):
            if self.log:
                self.log.error(f"{self.name} - Invalid transaction types")
                self.log.error(f"  Expected type: {type(expected)}")
                self.log.error(f"  Actual type: {type(actual)}")
            return False
            
        # Basic comparison already implemented in APBCycle.__eq__
        return expected == actual
    
    def _log_mismatch(self, expected, actual):
        """Enhanced mismatch logging for APB cycles"""
        if self.log:
            self.log.error(f"{self.name} - APB Cycle mismatch:")
            self.log.error(f"  Expected: {expected.formatted(self.addr_width, self.data_width, self.strb_width)}")
            self.log.error(f"  Actual:   {actual.formatted(self.addr_width, self.data_width, self.strb_width)}")
            
            # Detailed comparison of fields
            if expected.direction != actual.direction:
                self.log.error(f"  Direction mismatch: expected={expected.direction}, actual={actual.direction}")
            
            if expected.paddr != actual.paddr:
                self.log.error(f"  Address mismatch: expected=0x{expected.paddr:X}, actual=0x{actual.paddr:X}")
                
            if expected.direction == 'WRITE':
                if expected.pwdata != actual.pwdata:
                    self.log.error(f"  Write data mismatch: expected=0x{expected.pwdata:X}, actual=0x{actual.pwdata:X}")
                if expected.pstrb != actual.pstrb:
                    self.log.error(f"  Strobe mismatch: expected=0x{expected.pstrb:X}, actual=0x{actual.pstrb:X}")
            else:
                if expected.prdata != actual.prdata:
                    self.log.error(f"  Read data mismatch: expected=0x{expected.prdata:X}, actual=0x{actual.prdata:X}")
            
            if expected.pprot != actual.pprot:
                self.log.error(f"  Protection mismatch: expected=0x{expected.pprot:X}, actual=0x{actual.pprot:X}")
            
            if expected.pslverr != actual.pslverr:
                self.log.error(f"  Slave error mismatch: expected={expected.pslverr}, actual={actual.pslverr}")


class APBtoGAXITransformer(ProtocolTransformer):
    """Transformer from APB to GAXI transactions"""
    
    def __init__(self, gaxi_field_config, packet_class, log=None):
        super().__init__("APB", "GAXI", log)
        self.gaxi_field_config = gaxi_field_config
        self.packet_class = packet_class
        
    def transform(self, apb_cycle):
        """Transform APB cycle to one or more GAXI transactions"""
        if not isinstance(apb_cycle, APBCycle):
            if self.log:
                self.log.error("Invalid transaction type for APB to GAXI transformation")
            return []
            
        # For simplicity, we'll transform 1:1 
        # In a real implementation, you might want to handle more complex transformations
        
        gaxi_packet = self.packet_class(self.gaxi_field_config)
        
        # Map fields from APB to GAXI
        if 'addr' in gaxi_packet.fields:
            gaxi_packet.fields['addr'] = apb_cycle.paddr
            
        if 'data' in gaxi_packet.fields:
            if apb_cycle.direction == 'WRITE':
                gaxi_packet.fields['data'] = apb_cycle.pwdata
            else:
                gaxi_packet.fields['data'] = apb_cycle.prdata
                
        if 'strb' in gaxi_packet.fields and apb_cycle.direction == 'WRITE':
            gaxi_packet.fields['strb'] = apb_cycle.pstrb
            
        # Return as a single transaction for now
        # In more complex cases, you might return multiple transactions
        return [gaxi_packet]
