"""
AXI4 Field Definitions and Signal Mappings

This module provides:
1. Field configurations for all AXI4 channels
2. Signal mappings for connecting to AXI4 interfaces
3. Default timing constraints for AXI4 components
"""

# AXI4 Field Configurations
# Each channel has a specific field layout according to the AXI4 specification

# Write Address Channel (AW)
AXI4_AW_FIELD_CONFIG = {
    'awid': {
        'bits': 8,
        'default': 0,
        'format': 'hex',
        'display_width': 2,
        'active_bits': (7, 0),
        'description': 'Write Address ID'
    },
    'awaddr': {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Write Address'
    },
    'awlen': {
        'bits': 8,
        'default': 0,
        'format': 'dec',
        'display_width': 2,
        'active_bits': (7, 0),
        'description': 'Burst Length'
    },
    'awsize': {
        'bits': 3,
        'default': 0,
        'format': 'dec',
        'display_width': 1,
        'active_bits': (2, 0),
        'description': 'Burst Size'
    },
    'awburst': {
        'bits': 2,
        'default': 1,  # INCR
        'format': 'dec',
        'display_width': 1,
        'active_bits': (1, 0),
        'description': 'Burst Type'
    },
    'awlock': {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'Lock Type'
    },
    'awcache': {
        'bits': 4,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (3, 0),
        'description': 'Cache Type'
    },
    'awprot': {
        'bits': 3,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (2, 0),
        'description': 'Protection Type'
    },
    'awqos': {
        'bits': 4,
        'default': 0,
        'format': 'dec',
        'display_width': 1,
        'active_bits': (3, 0),
        'description': 'Quality of Service'
    },
    'awregion': {
        'bits': 4,
        'default': 0,
        'format': 'dec',
        'display_width': 1,
        'active_bits': (3, 0),
        'description': 'Region Identifier'
    },
    'awuser': {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'User Signal'
    }
}

# Write Data Channel (W)
AXI4_W_FIELD_CONFIG = {
    'wdata': {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Write Data'
    },
    'wstrb': {
        'bits': 4,
        'default': 0xF,
        'format': 'bin',
        'display_width': 4,
        'active_bits': (3, 0),
        'description': 'Write Strobe'
    },
    'wlast': {
        'bits': 1,
        'default': 1,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'Write Last'
    },
    'wuser': {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'User Signal'
    }
}

# Write Response Channel (B)
AXI4_B_FIELD_CONFIG = {
    'bid': {
        'bits': 8,
        'default': 0,
        'format': 'hex',
        'display_width': 2,
        'active_bits': (7, 0),
        'description': 'Response ID'
    },
    'bresp': {
        'bits': 2,
        'default': 0,
        'format': 'dec',
        'display_width': 1,
        'active_bits': (1, 0),
        'description': 'Write Response'
    },
    'buser': {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'User Signal'
    }
}

# Read Address Channel (AR)
AXI4_AR_FIELD_CONFIG = {
    'arid': {
        'bits': 8,
        'default': 0,
        'format': 'hex',
        'display_width': 2,
        'active_bits': (7, 0),
        'description': 'Read Address ID'
    },
    'araddr': {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Read Address'
    },
    'arlen': {
        'bits': 8,
        'default': 0,
        'format': 'dec',
        'display_width': 2,
        'active_bits': (7, 0),
        'description': 'Burst Length'
    },
    'arsize': {
        'bits': 3,
        'default': 0,
        'format': 'dec',
        'display_width': 1,
        'active_bits': (2, 0),
        'description': 'Burst Size'
    },
    'arburst': {
        'bits': 2,
        'default': 1,  # INCR
        'format': 'dec',
        'display_width': 1,
        'active_bits': (1, 0),
        'description': 'Burst Type'
    },
    'arlock': {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'Lock Type'
    },
    'arcache': {
        'bits': 4,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (3, 0),
        'description': 'Cache Type'
    },
    'arprot': {
        'bits': 3,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (2, 0),
        'description': 'Protection Type'
    },
    'arqos': {
        'bits': 4,
        'default': 0,
        'format': 'dec',
        'display_width': 1,
        'active_bits': (3, 0),
        'description': 'Quality of Service'
    },
    'arregion': {
        'bits': 4,
        'default': 0,
        'format': 'dec',
        'display_width': 1,
        'active_bits': (3, 0),
        'description': 'Region Identifier'
    },
    'aruser': {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'User Signal'
    }
}

# Read Data Channel (R)
AXI4_R_FIELD_CONFIG = {
    'rid': {
        'bits': 8,
        'default': 0,
        'format': 'hex',
        'display_width': 2,
        'active_bits': (7, 0),
        'description': 'Read Data ID'
    },
    'rdata': {
        'bits': 32,
        'default': 0,
        'format': 'hex',
        'display_width': 8,
        'active_bits': (31, 0),
        'description': 'Read Data'
    },
    'rresp': {
        'bits': 2,
        'default': 0,
        'format': 'dec',
        'display_width': 1,
        'active_bits': (1, 0),
        'description': 'Read Response'
    },
    'rlast': {
        'bits': 1,
        'default': 1,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'Read Last'
    },
    'ruser': {
        'bits': 1,
        'default': 0,
        'format': 'bin',
        'display_width': 1,
        'active_bits': (0, 0),
        'description': 'User Signal'
    }
}

# Default timing constraints for AXI4 components
AXI4_MASTER_DEFAULT_CONSTRAINTS = {
    'valid_delay': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1])
}

AXI4_SLAVE_DEFAULT_CONSTRAINTS = {
    'ready_delay': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1])
}

# AXI4 Signal Mapping Functions

def get_master_aw_signal_map(prefix=""):
    """Get signal map for AW channel (master)"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}m_axi_awvalid',
        's2m_ready': f'{prefix}m_axi_awready'
    }

    # Optional signals for the AW packet fields
    optional_signal_map = {
        'm2s_pkt_awid': f'{prefix}m_axi_awid',
        'm2s_pkt_awaddr': f'{prefix}m_axi_awaddr',
        'm2s_pkt_awlen': f'{prefix}m_axi_awlen',
        'm2s_pkt_awsize': f'{prefix}m_axi_awsize',
        'm2s_pkt_awburst': f'{prefix}m_axi_awburst',
        'm2s_pkt_awlock': f'{prefix}m_axi_awlock',
        'm2s_pkt_awcache': f'{prefix}m_axi_awcache',
        'm2s_pkt_awprot': f'{prefix}m_axi_awprot',
        'm2s_pkt_awqos': f'{prefix}m_axi_awqos',
        'm2s_pkt_awregion': f'{prefix}m_axi_awregion',
        'm2s_pkt_awuser': f'{prefix}m_axi_awuser'
    }

    return signal_map, optional_signal_map

def get_master_w_signal_map(prefix=""):
    """Get signal map for W channel (master)"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}m_axi_wvalid',
        's2m_ready': f'{prefix}m_axi_wready'
    }

    # Optional signals for the W packet fields
    optional_signal_map = {
        'm2s_pkt_wdata': f'{prefix}m_axi_wdata',
        'm2s_pkt_wstrb': f'{prefix}m_axi_wstrb',
        'm2s_pkt_wlast': f'{prefix}m_axi_wlast',
        'm2s_pkt_wuser': f'{prefix}m_axi_wuser'
    }

    return signal_map, optional_signal_map

def get_master_b_signal_map(prefix=""):
    """Get signal map for B channel (master)"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}m_axi_bvalid',
        's2m_ready': f'{prefix}m_axi_bready'
    }

    # Optional signals for the B packet fields
    optional_signal_map = {
        'm2s_pkt_bid': f'{prefix}m_axi_bid',
        'm2s_pkt_bresp': f'{prefix}m_axi_bresp',
        'm2s_pkt_buser': f'{prefix}m_axi_buser'
    }

    return signal_map, optional_signal_map

def get_master_ar_signal_map(prefix=""):
    """Get signal map for AR channel (master)"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}m_axi_arvalid',
        's2m_ready': f'{prefix}m_axi_arready'
    }

    # Optional signals for the AR packet fields
    optional_signal_map = {
        'm2s_pkt_arid': f'{prefix}m_axi_arid',
        'm2s_pkt_araddr': f'{prefix}m_axi_araddr',
        'm2s_pkt_arlen': f'{prefix}m_axi_arlen',
        'm2s_pkt_arsize': f'{prefix}m_axi_arsize',
        'm2s_pkt_arburst': f'{prefix}m_axi_arburst',
        'm2s_pkt_arlock': f'{prefix}m_axi_arlock',
        'm2s_pkt_arcache': f'{prefix}m_axi_arcache',
        'm2s_pkt_arprot': f'{prefix}m_axi_arprot',
        'm2s_pkt_arqos': f'{prefix}m_axi_arqos',
        'm2s_pkt_arregion': f'{prefix}m_axi_arregion',
        'm2s_pkt_aruser': f'{prefix}m_axi_aruser'
    }

    return signal_map, optional_signal_map

def get_master_r_signal_map(prefix=""):
    """Get signal map for R channel (master)"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}m_axi_rvalid',
        's2m_ready': f'{prefix}m_axi_rready'
    }

    # Optional signals for the R packet fields
    optional_signal_map = {
        'm2s_pkt_rid': f'{prefix}m_axi_rid',
        'm2s_pkt_rdata': f'{prefix}m_axi_rdata',
        'm2s_pkt_rresp': f'{prefix}m_axi_rresp',
        'm2s_pkt_rlast': f'{prefix}m_axi_rlast',
        'm2s_pkt_ruser': f'{prefix}m_axi_ruser'
    }

    return signal_map, optional_signal_map

def get_slave_aw_signal_map(prefix=""):
    """Get signal map for AW channel (slave)"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}s_axi_awvalid',
        's2m_ready': f'{prefix}s_axi_awready'
    }

    # Optional signals for the AW packet fields
    optional_signal_map = {
        'm2s_pkt_awid': f'{prefix}s_axi_awid',
        'm2s_pkt_awaddr': f'{prefix}s_axi_awaddr',
        'm2s_pkt_awlen': f'{prefix}s_axi_awlen',
        'm2s_pkt_awsize': f'{prefix}s_axi_awsize',
        'm2s_pkt_awburst': f'{prefix}s_axi_awburst',
        'm2s_pkt_awlock': f'{prefix}s_axi_awlock',
        'm2s_pkt_awcache': f'{prefix}s_axi_awcache',
        'm2s_pkt_awprot': f'{prefix}s_axi_awprot',
        'm2s_pkt_awqos': f'{prefix}s_axi_awqos',
        'm2s_pkt_awregion': f'{prefix}s_axi_awregion',
        'm2s_pkt_awuser': f'{prefix}s_axi_awuser'
    }

    return signal_map, optional_signal_map

def get_slave_w_signal_map(prefix=""):
    """Get signal map for W channel (slave)"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}s_axi_wvalid',
        's2m_ready': f'{prefix}s_axi_wready'
    }

    # Optional signals for the W packet fields
    optional_signal_map = {
        'm2s_pkt_wdata': f'{prefix}s_axi_wdata',
        'm2s_pkt_wstrb': f'{prefix}s_axi_wstrb',
        'm2s_pkt_wlast': f'{prefix}s_axi_wlast',
        'm2s_pkt_wuser': f'{prefix}s_axi_wuser'
    }

    return signal_map, optional_signal_map

def get_slave_b_signal_map(prefix=""):
    """Get signal map for B channel (slave)"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}s_axi_bvalid',
        's2m_ready': f'{prefix}s_axi_bready'
    }

    # Optional signals for the B packet fields
    optional_signal_map = {
        'm2s_pkt_bid': f'{prefix}s_axi_bid',
        'm2s_pkt_bresp': f'{prefix}s_axi_bresp',
        'm2s_pkt_buser': f'{prefix}s_axi_buser'
    }

    return signal_map, optional_signal_map

def get_slave_ar_signal_map(prefix=""):
    """Get signal map for AR channel (slave)"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}s_axi_arvalid',
        's2m_ready': f'{prefix}s_axi_arready'
    }

    # Optional signals for the AR packet fields
    optional_signal_map = {
        'm2s_pkt_arid': f'{prefix}s_axi_arid',
        'm2s_pkt_araddr': f'{prefix}s_axi_araddr',
        'm2s_pkt_arlen': f'{prefix}s_axi_arlen',
        'm2s_pkt_arsize': f'{prefix}s_axi_arsize',
        'm2s_pkt_arburst': f'{prefix}s_axi_arburst',
        'm2s_pkt_arlock': f'{prefix}s_axi_arlock',
        'm2s_pkt_arcache': f'{prefix}s_axi_arcache',
        'm2s_pkt_arprot': f'{prefix}s_axi_arprot',
        'm2s_pkt_arqos': f'{prefix}s_axi_arqos',
        'm2s_pkt_arregion': f'{prefix}s_axi_arregion',
        'm2s_pkt_aruser': f'{prefix}s_axi_aruser'
    }

    return signal_map, optional_signal_map

def get_slave_r_signal_map(prefix=""):
    """Get signal map for R channel (slave)"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}s_axi_rvalid',
        's2m_ready': f'{prefix}s_axi_rready'
    }

    # Optional signals for the R packet fields
    optional_signal_map = {
        'm2s_pkt_rid': f'{prefix}s_axi_rid',
        'm2s_pkt_rdata': f'{prefix}s_axi_rdata',
        'm2s_pkt_rresp': f'{prefix}s_axi_rresp',
        'm2s_pkt_rlast': f'{prefix}s_axi_rlast',
        'm2s_pkt_ruser': f'{prefix}s_axi_ruser'
    }

    return signal_map, optional_signal_map


def adjust_field_configs(field_configs, id_width, addr_width, data_width, user_width):
    """
    Adjust field configurations for specified widths.

    Args:
        field_configs: Dictionary of field configurations for each channel (AW, W, B, AR, R)
        id_width: Width of ID fields
        addr_width: Width of address fields
        data_width: Width of data fields
        user_width: Width of user fields

    Returns:
        Dictionary of adjusted field configurations
    """
    adjusted_configs = {
        channel: {k: v.copy() for k, v in config.items()}
        for channel, config in field_configs.items()
    }
    # Strobe width calculation
    strb_width = data_width // 8

    # Adjust ID fields
    for field_name in ['awid', 'bid']:
        if field_name in adjusted_configs.get('AW', {}):
            adjusted_configs['AW'][field_name]['bits'] = id_width
            adjusted_configs['AW'][field_name]['active_bits'] = (id_width-1, 0)
        if field_name in adjusted_configs.get('B', {}):
            adjusted_configs['B'][field_name]['bits'] = id_width
            adjusted_configs['B'][field_name]['active_bits'] = (id_width-1, 0)

    for field_name in ['arid', 'rid']:
        if field_name in adjusted_configs.get('AR', {}):
            adjusted_configs['AR'][field_name]['bits'] = id_width
            adjusted_configs['AR'][field_name]['active_bits'] = (id_width-1, 0)
        if field_name in adjusted_configs.get('R', {}):
            adjusted_configs['R'][field_name]['bits'] = id_width
            adjusted_configs['R'][field_name]['active_bits'] = (id_width-1, 0)

    # Adjust address fields
    for field_name in ['awaddr', 'araddr']:
        if field_name in adjusted_configs.get('AW', {}):
            adjusted_configs['AW'][field_name]['bits'] = addr_width
            adjusted_configs['AW'][field_name]['active_bits'] = (addr_width-1, 0)
        if field_name in adjusted_configs.get('AR', {}):
            adjusted_configs['AR'][field_name]['bits'] = addr_width
            adjusted_configs['AR'][field_name]['active_bits'] = (addr_width-1, 0)

    # Adjust data fields
    if 'wdata' in adjusted_configs.get('W', {}):
        adjusted_configs['W']['wdata']['bits'] = data_width
        adjusted_configs['W']['wdata']['active_bits'] = (data_width-1, 0)

    if 'rdata' in adjusted_configs.get('R', {}):
        adjusted_configs['R']['rdata']['bits'] = data_width
        adjusted_configs['R']['rdata']['active_bits'] = (data_width-1, 0)

    # Adjust strobe field
    if 'wstrb' in adjusted_configs.get('W', {}):
        adjusted_configs['W']['wstrb']['bits'] = strb_width
        adjusted_configs['W']['wstrb']['active_bits'] = (strb_width-1, 0)

    # Adjust user fields
    user_fields = {
        'AW': ['awuser'],
        'W': ['wuser'],
        'B': ['buser'],
        'AR': ['aruser'],
        'R': ['ruser']
    }

    for channel, fields in user_fields.items():
        for field_name in fields:
            if field_name in adjusted_configs.get(channel, {}):
                adjusted_configs[channel][field_name]['bits'] = user_width
                adjusted_configs[channel][field_name]['active_bits'] = (user_width-1, 0)

    return adjusted_configs


def create_all_signal_maps(prefix="", is_slave=False):
    """
    Create signal maps for all AXI4 channels.

    Args:
        prefix: Signal prefix
        is_slave: Whether to create slave-side signal maps (default: False for master-side)

    Returns:
        Dictionary of signal maps for all channels
    """
    if is_slave:
        return {
            'AW': get_slave_aw_signal_map(prefix),
            'W': get_slave_w_signal_map(prefix),
            'B': get_slave_b_signal_map(prefix),
            'AR': get_slave_ar_signal_map(prefix),
            'R': get_slave_r_signal_map(prefix),
        }
    else:
        return {
            'AW': get_master_aw_signal_map(prefix),
            'W': get_master_w_signal_map(prefix),
            'B': get_master_b_signal_map(prefix),
            'AR': get_master_ar_signal_map(prefix),
            'R': get_master_r_signal_map(prefix),
        }
