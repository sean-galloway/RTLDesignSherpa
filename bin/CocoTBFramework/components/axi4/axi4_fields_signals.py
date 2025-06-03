"""
AXI4 Field Definitions and Signal Mappings

This module provides:
1. Field configurations for all AXI4 channels
2. Signal mappings for connecting to AXI4 interfaces
3. Default timing constraints for AXI4 components
"""

from CocoTBFramework.components.field_config import FieldConfig, FieldDefinition

# AXI4 Field Configurations
# Create FieldConfig objects for each channel according to the AXI4 specification

def create_axi4_aw_field_config():
    """Create the Write Address (AW) channel field configuration"""
    config = FieldConfig()
    config.add_field(FieldDefinition(
        name="awid",
        bits=8,
        default=0,
        format="hex",
        display_width=2,
        active_bits=(7, 0),
        description="Write Address ID"
    ))
    config.add_field(FieldDefinition(
        name="awaddr",
        bits=32,
        default=0,
        format="hex",
        display_width=8,
        active_bits=(31, 0),
        description="Write Address"
    ))
    config.add_field(FieldDefinition(
        name="awlen",
        bits=8,
        default=0,
        format="dec",
        display_width=2,
        active_bits=(7, 0),
        description="Burst Length"
    ))
    config.add_field(FieldDefinition(
        name="awsize",
        bits=3,
        default=0,
        format="dec",
        display_width=1,
        active_bits=(2, 0),
        description="Burst Size"
    ))
    config.add_field(FieldDefinition(
        name="awburst",
        bits=2,
        default=1,  # INCR
        format="dec",
        display_width=1,
        active_bits=(1, 0),
        description="Burst Type"
    ))
    config.add_field(FieldDefinition(
        name="awlock",
        bits=1,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(0, 0),
        description="Lock Type"
    ))
    config.add_field(FieldDefinition(
        name="awcache",
        bits=4,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(3, 0),
        description="Cache Type"
    ))
    config.add_field(FieldDefinition(
        name="awprot",
        bits=3,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(2, 0),
        description="Protection Type"
    ))
    config.add_field(FieldDefinition(
        name="awqos",
        bits=4,
        default=0,
        format="dec",
        display_width=1,
        active_bits=(3, 0),
        description="Quality of Service"
    ))
    config.add_field(FieldDefinition(
        name="awregion",
        bits=4,
        default=0,
        format="dec",
        display_width=1,
        active_bits=(3, 0),
        description="Region Identifier"
    ))
    config.add_field(FieldDefinition(
        name="awuser",
        bits=1,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(0, 0),
        description="User Signal"
    ))
    return config

def create_axi4_w_field_config():
    """Create the Write Data (W) channel field configuration"""
    config = FieldConfig()
    config.add_field(FieldDefinition(
        name="wdata",
        bits=32,
        default=0,
        format="hex",
        display_width=8,
        active_bits=(31, 0),
        description="Write Data"
    ))
    config.add_field(FieldDefinition(
        name="wstrb",
        bits=4,
        default=0xF,
        format="bin",
        display_width=4,
        active_bits=(3, 0),
        description="Write Strobe"
    ))
    config.add_field(FieldDefinition(
        name="wlast",
        bits=1,
        default=1,
        format="bin",
        display_width=1,
        active_bits=(0, 0),
        description="Write Last"
    ))
    config.add_field(FieldDefinition(
        name="wuser",
        bits=1,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(0, 0),
        description="User Signal"
    ))
    return config

def create_axi4_b_field_config():
    """Create the Write Response (B) channel field configuration"""
    config = FieldConfig()
    config.add_field(FieldDefinition(
        name="bid",
        bits=8,
        default=0,
        format="hex",
        display_width=2,
        active_bits=(7, 0),
        description="Response ID"
    ))
    config.add_field(FieldDefinition(
        name="bresp",
        bits=2,
        default=0,
        format="dec",
        display_width=1,
        active_bits=(1, 0),
        description="Write Response"
    ))
    config.add_field(FieldDefinition(
        name="buser",
        bits=1,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(0, 0),
        description="User Signal"
    ))
    return config

def create_axi4_ar_field_config():
    """Create the Read Address (AR) channel field configuration"""
    config = FieldConfig()
    config.add_field(FieldDefinition(
        name="arid",
        bits=8,
        default=0,
        format="hex",
        display_width=2,
        active_bits=(7, 0),
        description="Read Address ID"
    ))
    config.add_field(FieldDefinition(
        name="araddr",
        bits=32,
        default=0,
        format="hex",
        display_width=8,
        active_bits=(31, 0),
        description="Read Address"
    ))
    config.add_field(FieldDefinition(
        name="arlen",
        bits=8,
        default=0,
        format="dec",
        display_width=2,
        active_bits=(7, 0),
        description="Burst Length"
    ))
    config.add_field(FieldDefinition(
        name="arsize",
        bits=3,
        default=0,
        format="dec",
        display_width=1,
        active_bits=(2, 0),
        description="Burst Size"
    ))
    config.add_field(FieldDefinition(
        name="arburst",
        bits=2,
        default=1,  # INCR
        format="dec",
        display_width=1,
        active_bits=(1, 0),
        description="Burst Type"
    ))
    config.add_field(FieldDefinition(
        name="arlock",
        bits=1,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(0, 0),
        description="Lock Type"
    ))
    config.add_field(FieldDefinition(
        name="arcache",
        bits=4,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(3, 0),
        description="Cache Type"
    ))
    config.add_field(FieldDefinition(
        name="arprot",
        bits=3,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(2, 0),
        description="Protection Type"
    ))
    config.add_field(FieldDefinition(
        name="arqos",
        bits=4,
        default=0,
        format="dec",
        display_width=1,
        active_bits=(3, 0),
        description="Quality of Service"
    ))
    config.add_field(FieldDefinition(
        name="arregion",
        bits=4,
        default=0,
        format="dec",
        display_width=1,
        active_bits=(3, 0),
        description="Region Identifier"
    ))
    config.add_field(FieldDefinition(
        name="aruser",
        bits=1,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(0, 0),
        description="User Signal"
    ))
    return config

def create_axi4_r_field_config():
    """Create the Read Data (R) channel field configuration"""
    config = FieldConfig()
    config.add_field(FieldDefinition(
        name="rid",
        bits=8,
        default=0,
        format="hex",
        display_width=2,
        active_bits=(7, 0),
        description="Read Data ID"
    ))
    config.add_field(FieldDefinition(
        name="rdata",
        bits=32,
        default=0,
        format="hex",
        display_width=8,
        active_bits=(31, 0),
        description="Read Data"
    ))
    config.add_field(FieldDefinition(
        name="rresp",
        bits=2,
        default=0,
        format="dec",
        display_width=1,
        active_bits=(1, 0),
        description="Read Response"
    ))
    config.add_field(FieldDefinition(
        name="rlast",
        bits=1,
        default=1,
        format="bin",
        display_width=1,
        active_bits=(0, 0),
        description="Read Last"
    ))
    config.add_field(FieldDefinition(
        name="ruser",
        bits=1,
        default=0,
        format="bin",
        display_width=1,
        active_bits=(0, 0),
        description="User Signal"
    ))
    return config

# Create the field configs
AXI4_AW_FIELD_CONFIG = create_axi4_aw_field_config()
AXI4_W_FIELD_CONFIG = create_axi4_w_field_config()
AXI4_B_FIELD_CONFIG = create_axi4_b_field_config()
AXI4_AR_FIELD_CONFIG = create_axi4_ar_field_config()
AXI4_R_FIELD_CONFIG = create_axi4_r_field_config()

# Maintain dictionary representation for backward compatibility
AXI4_AW_FIELD_CONFIG_DICT = AXI4_AW_FIELD_CONFIG.to_dict()
AXI4_W_FIELD_CONFIG_DICT = AXI4_W_FIELD_CONFIG.to_dict()
AXI4_B_FIELD_CONFIG_DICT = AXI4_B_FIELD_CONFIG.to_dict()
AXI4_AR_FIELD_CONFIG_DICT = AXI4_AR_FIELD_CONFIG.to_dict()
AXI4_R_FIELD_CONFIG_DICT = AXI4_R_FIELD_CONFIG.to_dict()

# Default timing constraints for AXI4 components
AXI4_MASTER_DEFAULT_CONSTRAINTS = {
    'valid_delay': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1])
}

AXI4_SLAVE_DEFAULT_CONSTRAINTS = {
    'ready_delay': ([[0, 0], [1, 5], [6, 10]], [5, 3, 1])
}

# AXI4 Signal Mapping Functions

def get_aw_signal_map(prefix="", divider="_", suffix=""):
    """Get signal map for AW channel"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}_aw{divider}valid{suffix}',
        's2m_ready': f'{prefix}_aw{divider}ready{suffix}'
    }

    # Optional signals for the AW packet fields
    optional_signal_map = {
        'm2s_pkt_awid': f'{prefix}_aw{divider}id{suffix}',
        'm2s_pkt_awaddr': f'{prefix}_aw{divider}addr{suffix}',
        'm2s_pkt_awlen': f'{prefix}_aw{divider}len{suffix}',
        'm2s_pkt_awsize': f'{prefix}_aw{divider}size{suffix}',
        'm2s_pkt_awburst': f'{prefix}_aw{divider}burst{suffix}',
        'm2s_pkt_awlock': f'{prefix}_aw{divider}lock{suffix}',
        'm2s_pkt_awcache': f'{prefix}_aw{divider}cache{suffix}',
        'm2s_pkt_awprot': f'{prefix}_aw{divider}prot{suffix}',
        'm2s_pkt_awqos': f'{prefix}_aw{divider}qos{suffix}',
        'm2s_pkt_awregion': f'{prefix}_aw{divider}region{suffix}',
        'm2s_pkt_awuser': f'{prefix}_aw{divider}user{suffix}'
    }

    return signal_map, optional_signal_map

def get_w_signal_map(prefix="", divider="_", suffix=""):
    """Get signal map for W channel"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}_w{divider}valid{suffix}',
        's2m_ready': f'{prefix}_w{divider}ready{suffix}'
    }

    # Optional signals for the W packet fields
    optional_signal_map = {
        'm2s_pkt_wdata': f'{prefix}_w{divider}data{suffix}',
        'm2s_pkt_wstrb': f'{prefix}_w{divider}strb{suffix}',
        'm2s_pkt_wlast': f'{prefix}_w{divider}last{suffix}',
        'm2s_pkt_wuser': f'{prefix}_w{divider}user{suffix}'
    }

    return signal_map, optional_signal_map

def get_b_signal_map(prefix="", divider="_", suffix=""):
    """Get signal map for B channel"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}_b{divider}valid{suffix}',
        's2m_ready': f'{prefix}_b{divider}ready{suffix}'
    }

    # Optional signals for the B packet fields
    optional_signal_map = {
        'm2s_pkt_bid': f'{prefix}_b{divider}id{suffix}',
        'm2s_pkt_bresp': f'{prefix}_b{divider}resp{suffix}',
        'm2s_pkt_buser': f'{prefix}_b{divider}user{suffix}'
    }

    return signal_map, optional_signal_map

def get_ar_signal_map(prefix="", divider="_", suffix=""):
    """Get signal map for AR channel"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}_ar{divider}valid{suffix}',
        's2m_ready': f'{prefix}_ar{divider}ready{suffix}'
    }

    # Optional signals for the AR packet fields
    optional_signal_map = {
        'm2s_pkt_arid': f'{prefix}_ar{divider}id{suffix}',
        'm2s_pkt_araddr': f'{prefix}_ar{divider}addr{suffix}',
        'm2s_pkt_arlen': f'{prefix}_ar{divider}len{suffix}',
        'm2s_pkt_arsize': f'{prefix}_ar{divider}size{suffix}',
        'm2s_pkt_arburst': f'{prefix}_ar{divider}burst{suffix}',
        'm2s_pkt_arlock': f'{prefix}_ar{divider}lock{suffix}',
        'm2s_pkt_arcache': f'{prefix}_ar{divider}cache{suffix}',
        'm2s_pkt_arprot': f'{prefix}_ar{divider}prot{suffix}',
        'm2s_pkt_arqos': f'{prefix}_ar{divider}qos{suffix}',
        'm2s_pkt_arregion': f'{prefix}_ar{divider}region{suffix}',
        'm2s_pkt_aruser': f'{prefix}_ar{divider}user{suffix}'
    }

    return signal_map, optional_signal_map

def get_r_signal_map(prefix="", divider="_", suffix=""):
    """Get signal map for R channel"""
    # Base signal map for valid/ready
    signal_map = {
        'm2s_valid': f'{prefix}_r{divider}valid{suffix}',
        's2m_ready': f'{prefix}_r{divider}ready{suffix}'
    }

    # Optional signals for the R packet fields
    optional_signal_map = {
        'm2s_pkt_rid': f'{prefix}_r{divider}id{suffix}',
        'm2s_pkt_rdata': f'{prefix}_r{divider}data{suffix}',
        'm2s_pkt_rresp': f'{prefix}_r{divider}resp{suffix}',
        'm2s_pkt_rlast': f'{prefix}_r{divider}last{suffix}',
        'm2s_pkt_ruser': f'{prefix}_r{divider}user{suffix}'
    }

    return signal_map, optional_signal_map

def create_all_signal_maps(prefix="", divider="_", suffix=""):
    """
    Create signal maps for all AXI4 channels.

    Args:
        prefix: Signal prefix (e.g., 'm_axi' or 's_axi')
        divider: Divider between channel and signal name
        suffix: Signal suffix

    Returns:
        Dictionary of signal maps for all channels
    """
    return {
        'AW': get_aw_signal_map(prefix, divider, suffix),
        'W': get_w_signal_map(prefix, divider, suffix),
        'B': get_b_signal_map(prefix, divider, suffix),
        'AR': get_ar_signal_map(prefix, divider, suffix),
        'R': get_r_signal_map(prefix, divider, suffix),
    }

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
    adjusted_configs = {}
    # Strobe width calculation
    strb_width = data_width // 8

    # Create deep copies of the field configs to avoid modifying the originals
    for channel, config in field_configs.items():
        adjusted_configs[channel] = config

    # Adjust ID fields in AW and B channels
    if 'AW' in adjusted_configs:
        if adjusted_configs['AW'].has_field('awid'):
            adjusted_configs['AW'].update_field_width('awid', id_width)

    if 'B' in adjusted_configs:
        if adjusted_configs['B'].has_field('bid'):
            adjusted_configs['B'].update_field_width('bid', id_width)

    # Adjust ID fields in AR and R channels
    if 'AR' in adjusted_configs:
        if adjusted_configs['AR'].has_field('arid'):
            adjusted_configs['AR'].update_field_width('arid', id_width)

    if 'R' in adjusted_configs:
        if adjusted_configs['R'].has_field('rid'):
            adjusted_configs['R'].update_field_width('rid', id_width)

    # Adjust address fields
    if 'AW' in adjusted_configs:
        if adjusted_configs['AW'].has_field('awaddr'):
            adjusted_configs['AW'].update_field_width('awaddr', addr_width)

    if 'AR' in adjusted_configs:
        if adjusted_configs['AR'].has_field('araddr'):
            adjusted_configs['AR'].update_field_width('araddr', addr_width)

    # Adjust data fields
    if 'W' in adjusted_configs:
        if adjusted_configs['W'].has_field('wdata'):
            adjusted_configs['W'].update_field_width('wdata', data_width)
        if adjusted_configs['W'].has_field('wstrb'):
            adjusted_configs['W'].update_field_width('wstrb', strb_width)

    if 'R' in adjusted_configs:
        if adjusted_configs['R'].has_field('rdata'):
            adjusted_configs['R'].update_field_width('rdata', data_width)

    # Adjust user fields
    user_fields = {
        'AW': ['awuser'],
        'W': ['wuser'],
        'B': ['buser'],
        'AR': ['aruser'],
        'R': ['ruser']
    }

    for channel, fields in user_fields.items():
        if channel in adjusted_configs:
            for field_name in fields:
                if adjusted_configs[channel].has_field(field_name):
                    adjusted_configs[channel].update_field_width(field_name, user_width)

    return adjusted_configs
