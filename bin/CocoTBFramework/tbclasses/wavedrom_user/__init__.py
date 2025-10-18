# wavedrom_user package

# APB protocol support
from .apb import (
    APBPresets,
    APBDebug,
    APBConstraints,
    setup_apb_constraints_with_boundaries,
    get_apb_boundary_pattern,
    get_apb_field_config
)

# GAXI protocol support
from .gaxi import (
    GAXIPresets,
    GAXIWaveDromTemplate,
    get_gaxi_field_config,
    create_gaxi_wavejson_generator,
    create_gaxi_handshake_constraint,
    create_gaxi_back2back_constraint,
    create_gaxi_stall_constraint,
    create_gaxi_idle_constraint,
    setup_gaxi_constraints_with_boundaries,
    get_gaxi_boundary_pattern,
    create_gaxi_signals_list
)

__all__ = [
    # APB
    'APBPresets',
    'APBDebug',
    'APBConstraints',
    'setup_apb_constraints_with_boundaries',
    'get_apb_boundary_pattern',
    'get_apb_field_config',
    # GAXI
    'GAXIPresets',
    'GAXIWaveDromTemplate',
    'get_gaxi_field_config',
    'create_gaxi_wavejson_generator',
    'create_gaxi_handshake_constraint',
    'create_gaxi_back2back_constraint',
    'create_gaxi_stall_constraint',
    'create_gaxi_idle_constraint',
    'setup_gaxi_constraints_with_boundaries',
    'get_gaxi_boundary_pattern',
    'create_gaxi_signals_list'
]
