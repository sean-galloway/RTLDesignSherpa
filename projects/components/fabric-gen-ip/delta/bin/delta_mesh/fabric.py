# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# RTL Design Sherpa - Industry-Standard RTL Design and Verification
# https://github.com/sean-galloway/RTLDesignSherpa
#
# Module: delta_mesh.fabric
# Purpose: Emitter for delta_mesh_fabric_<X>x<Y>x<Z> -- the mesh fabric top
#          that instantiates the delta_mesh_cell grid and exposes the
#          boundary cells' local ports (rapids attach points).
#
# Documentation: docs/superpowers/specs/2026-10-13-delta-mesh-design.md
# Subsystem: delta
#
# Author: sean galloway
# Created: 2026-10-14

"""
Delta mesh fabric-top generator using the unified verilog framework.

Task 3 scope: grid instantiation of the Task 2 cell over an XxYxZ mesh with
per-instance POS parameters, the boundary cells' local ports exposed as
unpacked boundary-local arrays (s_local_*/m_local_* plus the credit
sidebands), and every absent boundary-neighbor port tied off. Torus wrap
links are rejected here (NotImplementedError) until Task 9 lands them.

The generated fabric is pure structural: nested SystemVerilog generate
loops over genvars gx/gy/gz. The boundary-index map is computed by the
elaboration-time constant functions is_boundary()/boundary_index() in the
emitted RTL, matching boundary_cells() below (single source of truth).
"""

import os

from rtl_generators.verilog.module import Module

from .cell import NUM_PORTS, PORT_IDS
from .config import DeltaMeshConfig

# Boundary test and boundary-index map (single source of truth, mirrored in
# the emitted constant functions and consumed by the DV TB):
#
#   A cell is a boundary cell when
#       x in {0, X-1} or y in {0, Y-1} or z in {0, Z-1}
#   i.e. any coordinate sits on a mesh face. With Z == 1 both z faces are
#   boundary, so every cell of a 2-D mesh qualifies.
#
#   Boundary indices enumerate boundary cells in x-major, then y, then z
#   order -- ascending linear cell index (z*Y + y)*X + x, boundary cells
#   only. The generated RTL computes the same map in the elaboration-time
#   constant functions is_boundary()/boundary_index() below; keep the two
#   in lockstep.


def is_boundary(x: int, y: int, z: int, cfg: DeltaMeshConfig) -> bool:
    """True when cell (x,y,z) sits on at least one mesh face."""
    return (x in (0, cfg.cells_x - 1)
            or y in (0, cfg.cells_y - 1)
            or z in (0, cfg.cells_z - 1))


def boundary_cells(cfg: DeltaMeshConfig) -> list[tuple[int, int, int]]:
    """Boundary cell coordinates in boundary-index order (x, then y, then z)."""
    return [(x, y, z)
            for z in range(cfg.cells_z)
            for y in range(cfg.cells_y)
            for x in range(cfg.cells_x)
            if is_boundary(x, y, z, cfg)]


def validate_fabric(cfg: DeltaMeshConfig) -> None:
    """Reject configurations the Task 3 fabric emitter does not cover."""
    if cfg.torus_x or cfg.torus_y or cfg.torus_z:
        raise NotImplementedError(
            "torus mesh fabric is not yet supported: wrap links land in "
            "Task 9 -- re-run without --torus-x/--torus-y/--torus-z")


class DeltaMeshFabric(Module):
    """delta_mesh_fabric_<X>x<Y>x<Z> emitter: grid of cells, boundary locals out."""

    def __init__(self, config: DeltaMeshConfig):
        validate_fabric(config)
        self.cfg = config
        self.module_str = (f'delta_mesh_fabric_{config.cells_x}'
                           f'x{config.cells_y}x{config.cells_z}')

        Module.__init__(self, module_name=self.module_str)

        coord_w = max(1, (max(config.cells_x, config.cells_y, config.cells_z)
                          - 1).bit_length())
        self.coord_w = coord_w
        self.num_boundary = len(boundary_cells(config))

        param_str = f'''
            parameter int DATA_WIDTH = {config.data_width},
            parameter int USER_WIDTH = {config.user_width},
            parameter int COORD_W = {coord_w},
            parameter int NUM_VC = 2,
            parameter string FIFO_IMPL = "{config.fifo_impl}",
            parameter int ENABLE_COUNTERS = {1 if config.add_counters else 0},
            parameter int NUM_BOUNDARY = {self.num_boundary}
        '''
        self.params.add_param_string(param_str)

        port_str = '''
            input  logic aclk,
            input  logic aresetn,

            input  logic [DATA_WIDTH-1:0] s_local_tdata  [NUM_BOUNDARY],
            input  logic                  s_local_tvalid [NUM_BOUNDARY],
            output logic                  s_local_tready [NUM_BOUNDARY],
            input  logic                  s_local_tlast  [NUM_BOUNDARY],
            input  logic [USER_WIDTH-1:0] s_local_tuser  [NUM_BOUNDARY],

            output logic [DATA_WIDTH-1:0] m_local_tdata  [NUM_BOUNDARY],
            output logic                  m_local_tvalid [NUM_BOUNDARY],
            input  logic                  m_local_tready [NUM_BOUNDARY],
            output logic                  m_local_tlast  [NUM_BOUNDARY],
            output logic [USER_WIDTH-1:0] m_local_tuser  [NUM_BOUNDARY],

            input  logic [NUM_VC-1:0]     s_local_credit [NUM_BOUNDARY],
            output logic [NUM_VC-1:0]     m_local_credit [NUM_BOUNDARY]
        '''
        self.ports.add_port_string(port_str)

    # ------------------------------------------------------------------
    # Section emitters
    # ------------------------------------------------------------------
    def generate_header_comment(self):
        cfg = self.cfg
        self.comment("==============================================================================")
        self.comment(f"Module: {self.module_str}")
        self.comment("Project: Delta - AXI-Stream Crossbar Generator (mesh topology)")
        self.comment("==============================================================================")
        self.comment(f"Description: Mesh fabric top for a {cfg.cells_x}x{cfg.cells_y}x"
                     f"{cfg.cells_z} grid of delta_mesh_cell instances")
        self.comment("")
        self.comment("Delta: Where data flows split and merge like river deltas")
        self.comment("")
        self.comment("Generated by: delta_generator.py --topology mesh (framework version)")
        self.comment("Configuration:")
        self.comment(f"  - Topology: mesh ({cfg.cells_x}x{cfg.cells_y}x{cfg.cells_z})")
        self.comment(f"  - Data Width: {cfg.data_width} bits")
        self.comment(f"  - User Width: {cfg.user_width} bits (head-flit header in TUSER)")
        self.comment(f"  - Coordinate Width: {self.coord_w} bits")
        self.comment(f"  - Boundary Cells: {self.num_boundary} of "
                     f"{cfg.cells_x * cfg.cells_y * cfg.cells_z}")
        self.comment("")
        self.comment("Boundary locals (rapids attach points):")
        self.comment("  - A cell is a boundary cell when x in {0, X-1} or")
        self.comment("    y in {0, Y-1} or z in {0, Z-1} (any face of the mesh).")
        self.comment("    With Z == 1 both z faces are boundary, so every cell")
        self.comment("    of a 2-D mesh qualifies.")
        self.comment("  - Boundary index ordering is x-major, then y, then z:")
        self.comment("    ascending linear cell index (z*Y + y)*X + x over")
        self.comment("    boundary cells only (see boundary_index() below).")
        self.comment("  - Ports s_local_* / m_local_* (plus s_local_credit /")
        self.comment("    m_local_credit) are unpacked arrays over boundary")
        self.comment("    cells, one entry per boundary cell in that order.")
        self.comment("")
        self.comment("Tie-off policy (no torus this task -- wrap links land in")
        self.comment("Task 9; --torus-* is rejected at generation time):")
        self.comment("  - An absent boundary-neighbor port ties its s-side to")
        self.comment("    '0 (tvalid low) and s_credit to all-ones, and its")
        self.comment("    m-side tready to 1'b0: never ready, so a misroute")
        self.comment("    toward a nonexistent neighbor stalls visibly instead")
        self.comment("    of dropping flits. In-range DOR never selects one.")
        self.comment("  - An interior cell's local port (possible only when")
        self.comment("    X, Y, Z all >= 3) is tied off the same way.")
        self.comment("")
        self.comment("==============================================================================")
        self.instruction("")

    def generate_localparams(self):
        cfg = self.cfg
        self.comment("==========================================================================")
        self.comment("Local parameters")
        self.comment("==========================================================================")
        self.instruction(f"localparam int X_DIM = {cfg.cells_x};")
        self.instruction(f"localparam int Y_DIM = {cfg.cells_y};")
        self.instruction(f"localparam int Z_DIM = {cfg.cells_z};")
        self.instruction(f"localparam int NUM_PORTS = {NUM_PORTS};")
        self.instruction("")
        self.comment("Mesh port ids (pinned, same as delta_mesh_cell)")
        for name, value in PORT_IDS:
            self.instruction(f"localparam int {name} = {value};")
        self.instruction("")
        self.comment("Boundary predicate and boundary-index map, matching")
        self.comment("bin/delta_mesh/fabric.py (single source of truth). The")
        self.comment("index enumerates boundary cells in x-major, then y, then")
        self.comment("z order -- ascending linear index (z*Y + y)*X + x over")
        self.comment("boundary cells only. Constant functions: elaboration-")
        self.comment("time evaluated per generate-loop iteration.")
        self.instruction("function automatic logic is_boundary(int x, int y, int z);")
        self.instruction("    return (x == 0) || (x == X_DIM-1) ||")
        self.instruction("           (y == 0) || (y == Y_DIM-1) ||")
        self.instruction("           (z == 0) || (z == Z_DIM-1);")
        self.instruction("endfunction")
        self.instruction("")
        self.instruction("function automatic int linear_idx(int x, int y, int z);")
        self.instruction("    return (z*Y_DIM + y)*X_DIM + x;")
        self.instruction("endfunction")
        self.instruction("")
        self.instruction("function automatic int boundary_index(int x, int y, int z);")
        self.instruction("    int idx = 0;")
        self.instruction("    for (int zz = 0; zz < Z_DIM; zz++) begin")
        self.instruction("        for (int yy = 0; yy < Y_DIM; yy++) begin")
        self.instruction("            for (int xx = 0; xx < X_DIM; xx++) begin")
        self.instruction("                if (linear_idx(xx, yy, zz) < linear_idx(x, y, z))")
        self.instruction("                    if (is_boundary(xx, yy, zz))")
        self.instruction("                        idx++;")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("    return idx;")
        self.instruction("endfunction")
        self.instruction("")

    def generate_wire_declarations(self):
        self.comment("==========================================================================")
        self.comment("Inter-cell wiring (unpacked [X][Y][Z][port])")
        self.comment("==========================================================================")
        self.comment("Whole-signal granularity makes verilator report UNOPTFLAT")
        self.comment("(m -> s -> mux -> m looks circular across cells). The true")
        self.comment("per-element graph is acyclic: every cell's output grants")
        self.comment("are registered, in-range DOR routes never cycle, and the")
        self.comment("tready steering chain terminates at a flopped grant or a")
        self.comment("tied-off boundary. Suppressed at the declaration site; a")
        self.comment("genuine wiring loop from a future task would hang")
        self.comment("simulation instead -- the all-pairs suites catch that.")
        self.instruction("/* verilator lint_off UNOPTFLAT */")
        self.instruction("logic [DATA_WIDTH-1:0] cell_s_tdata  [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("logic                  cell_s_tvalid [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("logic                  cell_s_tready [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("logic                  cell_s_tlast  [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("logic [USER_WIDTH-1:0] cell_s_tuser  [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("logic [NUM_VC-1:0]     cell_s_credit [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.comment("Cell m-side outputs: elements whose neighbor/local sink is")
        self.comment("absent are deliberately left unread (tied-off side).")
        self.instruction("/* verilator lint_off UNUSEDSIGNAL */")
        self.instruction("logic [DATA_WIDTH-1:0] cell_m_tdata  [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("logic                  cell_m_tvalid [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("logic                  cell_m_tready [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("logic                  cell_m_tlast  [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("logic [USER_WIDTH-1:0] cell_m_tuser  [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("logic [NUM_VC-1:0]     cell_m_credit [X_DIM][Y_DIM][Z_DIM][NUM_PORTS];")
        self.instruction("/* verilator lint_on UNUSEDSIGNAL */")
        self.instruction("/* verilator lint_on UNOPTFLAT */")
        self.instruction("")

    # ------------------------------------------------------------------
    # Per-cell hookup emitters (coordinates are genvar expressions)
    # ------------------------------------------------------------------
    def _emit_port_tieoff(self, x, y, z, port):
        """Tie off every side of an absent neighbor/local port `port`."""
        p = f"[{x}][{y}][{z}][{port}]"
        self.instruction(f"                    assign cell_s_tdata{p}  = '0;")
        self.instruction(f"                    assign cell_s_tvalid{p} = 1'b0;")
        self.instruction(f"                    assign cell_s_tlast{p}  = 1'b0;")
        self.instruction(f"                    assign cell_s_tuser{p}  = '0;")
        self.instruction(f"                    assign cell_s_credit{p} = {{NUM_VC{{1'b1}}}};")
        self.instruction(f"                    assign cell_m_tready{p} = 1'b0;")

    def _emit_port_connection(self, x, y, z, port, nx, ny, nz, nport):
        """Connect port `port` of cell (x,y,z) to port `nport` of its neighbor."""
        p = f"[{x}][{y}][{z}][{port}]"
        q = f"[{nx}][{ny}][{nz}][{nport}]"
        # RHS wrapped: a full 4-D-array cross-connection assign exceeds the
        # 100-column house limit on one line.
        self.instruction(f"                    assign cell_s_tdata{p}  =")
        self.instruction(f"                        cell_m_tdata{q};")
        self.instruction(f"                    assign cell_s_tvalid{p} =")
        self.instruction(f"                        cell_m_tvalid{q};")
        self.instruction(f"                    assign cell_s_tlast{p}  =")
        self.instruction(f"                        cell_m_tlast{q};")
        self.instruction(f"                    assign cell_s_tuser{p}  =")
        self.instruction(f"                        cell_m_tuser{q};")
        self.instruction(f"                    assign cell_s_credit{p} =")
        self.instruction(f"                        cell_m_credit{q};")
        self.instruction(f"                    assign cell_m_tready{p} =")
        self.instruction(f"                        cell_s_tready{q};")

    def _emit_local_connection(self):
        """Wire a boundary cell's local port to its boundary-local slot."""
        self.instruction("                    localparam int BIDX = boundary_index(gx, gy, gz);")
        p = "[gx][gy][gz][P_LOCAL]"
        self.instruction(f"                    assign cell_s_tdata{p}  = s_local_tdata[BIDX];")
        self.instruction(f"                    assign cell_s_tvalid{p} = s_local_tvalid[BIDX];")
        self.instruction(f"                    assign cell_s_tlast{p}  = s_local_tlast[BIDX];")
        self.instruction(f"                    assign cell_s_tuser{p}  = s_local_tuser[BIDX];")
        self.instruction(f"                    assign cell_s_credit{p} = s_local_credit[BIDX];")
        self.instruction(f"                    assign cell_m_tready{p} = m_local_tready[BIDX];")
        self.instruction("")
        self.instruction(f"                    assign s_local_tready[BIDX] = cell_s_tready{p};")
        self.instruction(f"                    assign m_local_tdata[BIDX]  = cell_m_tdata{p};")
        self.instruction(f"                    assign m_local_tvalid[BIDX] = cell_m_tvalid{p};")
        self.instruction(f"                    assign m_local_tlast[BIDX]  = cell_m_tlast{p};")
        self.instruction(f"                    assign m_local_tuser[BIDX]  = cell_m_tuser{p};")
        self.instruction(f"                    assign m_local_credit[BIDX] = cell_m_credit{p};")

    def _emit_neighbor_hookups(self):
        """Emit the six if-generate neighbor hookups (genvar-relative)."""
        # (port, neighbor port, genvar, exists-condition)
        neighbors = (
            ("P_X_NEG", "P_X_POS", ("gx-1", "gy", "gz"), "gx > 0"),
            ("P_X_POS", "P_X_NEG", ("gx+1", "gy", "gz"), "gx < X_DIM-1"),
            ("P_Y_NEG", "P_Y_POS", ("gx", "gy-1", "gz"), "gy > 0"),
            ("P_Y_POS", "P_Y_NEG", ("gx", "gy+1", "gz"), "gy < Y_DIM-1"),
            ("P_Z_NEG", "P_Z_POS", ("gx", "gy", "gz-1"), "gz > 0"),
            ("P_Z_POS", "P_Z_NEG", ("gx", "gy", "gz+1"), "gz < Z_DIM-1"),
        )
        for port, nport, (nx, ny, nz), cond in neighbors:
            tag = port.replace("P_", "").lower()
            self.instruction(f"                if ({cond}) begin : gen_{tag}_conn")
            self._emit_port_connection("gx", "gy", "gz", port, nx, ny, nz, nport)
            self.instruction("                end else begin : "
                             f"gen_{tag}_tieoff")
            self._emit_port_tieoff("gx", "gy", "gz", port)
            self.instruction("                end")

    def generate_grid(self):
        self.comment("==========================================================================")
        self.comment("Cell grid -- nested generate loops over x, y, z")
        self.comment("==========================================================================")
        self.comment("Each delta_mesh_cell instance gets its grid coordinate as")
        self.comment("POS_X/POS_Y/POS_Z; neighbor ports hook to the adjacent")
        self.comment("cell or tie off at the mesh boundary. Boundary cells'")
        self.comment("local ports drive the s_local_*/m_local_* port arrays via")
        self.comment("the boundary-index map (x-major, then y, then z).")
        self.comment("==========================================================================")
        self.instruction("generate")
        self.instruction("    for (genvar gz = 0; gz < Z_DIM; gz++) begin : gen_z")
        self.instruction("        for (genvar gy = 0; gy < Y_DIM; gy++) begin : gen_y")
        self.instruction("            for (genvar gx = 0; gx < X_DIM; gx++) begin : gen_x")
        self.instruction("")
        self._emit_neighbor_hookups()
        self.instruction("")
        self.instruction("                if (is_boundary(gx, gy, gz)) begin : gen_local_conn")
        self._emit_local_connection()
        self.instruction("                end else begin : gen_local_tieoff")
        self._emit_port_tieoff("gx", "gy", "gz", "P_LOCAL")
        self.instruction("                end")
        self.instruction("")
        self.instruction("                delta_mesh_cell #(")
        self.instruction("                    .DATA_WIDTH(DATA_WIDTH),")
        self.instruction("                    .USER_WIDTH(USER_WIDTH),")
        self.instruction("                    .COORD_W(COORD_W),")
        self.instruction("                    .POS_X(gx),")
        self.instruction("                    .POS_Y(gy),")
        self.instruction("                    .POS_Z(gz),")
        self.instruction("                    .NUM_VC(NUM_VC),")
        self.instruction("                    .FIFO_IMPL(FIFO_IMPL),")
        self.instruction("                    .ENABLE_COUNTERS(ENABLE_COUNTERS)")
        self.instruction("                ) u_cell (")
        self.instruction("                    .aclk(aclk),")
        self.instruction("                    .aresetn(aresetn),")
        self.instruction("                    .s_axis_tdata (cell_s_tdata [gx][gy][gz]),")
        self.instruction("                    .s_axis_tvalid(cell_s_tvalid[gx][gy][gz]),")
        self.instruction("                    .s_axis_tready(cell_s_tready[gx][gy][gz]),")
        self.instruction("                    .s_axis_tlast (cell_s_tlast [gx][gy][gz]),")
        self.instruction("                    .s_axis_tuser (cell_s_tuser [gx][gy][gz]),")
        self.instruction("                    .m_axis_tdata (cell_m_tdata [gx][gy][gz]),")
        self.instruction("                    .m_axis_tvalid(cell_m_tvalid[gx][gy][gz]),")
        self.instruction("                    .m_axis_tready(cell_m_tready[gx][gy][gz]),")
        self.instruction("                    .m_axis_tlast (cell_m_tlast [gx][gy][gz]),")
        self.instruction("                    .m_axis_tuser (cell_m_tuser [gx][gy][gz]),")
        self.instruction("                    .s_credit(cell_s_credit[gx][gy][gz]),")
        self.instruction("                    .m_credit(cell_m_credit[gx][gy][gz])")
        self.instruction("                );")
        self.instruction("            end")
        self.instruction("        end")
        self.instruction("    end")
        self.instruction("endgenerate")
        self.instruction("")

    # ------------------------------------------------------------------
    # Top level
    # ------------------------------------------------------------------
    def verilog(self, file_path):
        self.generate_header_comment()
        self.generate_localparams()
        self.generate_wire_declarations()
        self.generate_grid()

        self.start()
        self.end()
        # House style: no trailing whitespace (the framework's comment("")
        # emits "// "; verible no-trailing-spaces flags it)
        self.start_instructions = [s.rstrip() for s in self.start_instructions]
        self.instructions = [s.rstrip() for s in self.instructions]
        self.end_instructions = [s.rstrip() for s in self.end_instructions]
        self.write(file_path, f'{self.module_name}.sv')


def write_fabric(config: DeltaMeshConfig, output_dir: str) -> str:
    """Emit delta_mesh_fabric_<X>x<Y>x<Z>.sv into output_dir; return its path."""
    validate_fabric(config)
    generator = DeltaMeshFabric(config)
    generator.verilog(output_dir)
    return os.path.join(output_dir, f'{generator.module_name}.sv')
