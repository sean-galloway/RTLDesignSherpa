import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import pytest
from delta_mesh import DeltaMeshConfig, validate_mesh, header_width


def test_torus_requires_two_cells():
    with pytest.raises(ValueError, match="torus.*>= 2"):
        validate_mesh(DeltaMeshConfig(cells_x=1, torus_x=True))


def test_user_width_below_header_rejected():
    with pytest.raises(ValueError, match="user-width"):
        validate_mesh(DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1, user_width=8))


def test_header_width_formula():
    assert header_width(DeltaMeshConfig(cells_x=4, cells_y=4, cells_z=1)) == 6 * 2 + 32
