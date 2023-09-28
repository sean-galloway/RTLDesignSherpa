import math
from rtl_generators.verilog.module import Module
from .black import Black
from .gray import Gray


def create_matrix_2d(row, col, default_val='x'):
    return [[default_val] * col for _ in range(row)]

class GroupPGLogic(Module):
    module_str = 'math_adder_brent_kung_grouppg'
    param_str = 'parameter int N=8'
    port_str = '''
    input  logic [N:0] i_p,
    input  logic [N:0] i_g,
    output logic [N:0] ow_gg,
    output logic [N:0] ow_pp
    '''


    def __init__(self, buswidth):
        super().__init__(module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        self.buswidth = buswidth
        self.bitwidth = buswidth+1
        self.params.set_param_value('N', self.buswidth)
        self.block_matrix = self.generate_block_matrix()
        self.row, self.col = len(self.block_matrix), len(self.block_matrix[0])
        self.module_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'


    def generate_block_matrix(self):
        height = int(2*math.log2(self.bitwidth) - 1)
        bmatrix = create_matrix_2d(height, self.bitwidth, default_val=('|', None))

        # Upside
        pow2 = 1
        for ix in range(math.ceil(height/2)):
            pow2 *= 2
            prev_route = pow2/2
            for jx in range(self.bitwidth-1, -1, -1):
                if ((jx+1) % pow2) == 0:
                    if jx == math.pow(2, ix+1)-1:
                        bmatrix[ix][jx] = ('Gray', jx-prev_route)
                    else:
                        bmatrix[ix][jx] = ('Black', jx-prev_route)
                elif ((jx+1) % pow2) == (pow2/2):
                    bmatrix[ix][jx] = ('Buffer', None)
                else:
                    continue

        # Downside
        downside_start_index = math.ceil(height/2)
        pow2 /= 2
        for ix in range(downside_start_index, downside_start_index+math.floor(height/2)):
            for jx in range(self.bitwidth-1, -1, -1):
                if (jx + 1) % pow2 != pow2 / 2:
                    continue

                if (jx+1+pow2/2) / pow2 != 1:
                    bmatrix[ix][jx] = ('Gray', jx-pow2/2)
            pow2 /= 2

        return bmatrix

    def height(self):
        return int(2*math.log2(self.bitwidth) - 1)

    def p_i_j(self, i, row):
        return self.naming_wired(row, i, 'P_{}_{}')

    def g_i_j(self, i, row):
        return self.naming_wired(row, i, 'G_{}_{}')

    def naming_wired(self, row, i, arg2):
        height = self.height()
        j = 0
        if row < math.ceil(height / 2) and row <= math.log2(self.bitwidth):
            j = i - math.pow(2, row + 1) + 1
        if row >= math.ceil(height / 2):
            j = i - math.pow(2, height - 1 - row)
        return arg2.format(int(i), j)


    def input_i_j(self, r, c):
        height = self.height()

        i = c
        if r < math.ceil(height/2):
            j = c if r == 0 else c - math.pow(2, r) + 1
        else:
            j = c if r == height-1 else c - math.pow(2, height-r-1) + 1
        return int(i), int(j)

    def output_i_j(self, r, c):
        height = self.height()

        i = c
        j = c - math.pow(2, r+1) + 1 if r < math.ceil(height/2) else 0
        return int(i), int(j)

    def black_block(self, r, c, block_in):
        # Inputs
        # print('---------------- Black Block ----------------')
        height = self.height()
        in1_i, in1_j = self.input_i_j(r, c)
        in2_i, in2_j = self.input_i_j(r, block_in)

        if in1_i == in1_j:
            gik = f'i_g[{in1_i}]'
            pik = f'i_p[{in1_i}]'
        else:
            gik = f'G_{in1_i}_{in1_j}'
            pik = f'P_{in1_i}_{in1_j}'
        if in2_i == in2_j:
            g_km1 = f'i_g[{in2_i}]'
            p_km1 = f'i_p[{in2_i}]'
        elif in2_j in ['0', 0]:
            g_km1 = f'ow_gg[{in2_i}]'
            p_km1 = f'ow_pp[{in2_i}]'
        else:
            g_km1 = f'G_{in2_i}_{in2_j}'
            p_km1 = f'P_{in2_i}_{in2_j}'
        _g_i_k = Module.in_connector('i_g', gik)
        _p_i_k = Module.in_connector('i_p', pik)
        _g_km1_j = Module.in_connector('i_g_km1', g_km1)
        _p_km1_j = Module.in_connector('i_p_km1', p_km1)

        # Outputs
        out_i, out_j = self.output_i_j(r, c)
        if out_j == '0':
            gij = f'ow_gg[{out_i}]'
            pij = f'ow_pp[{out_i}]'
        else:
            gij = f'G_{out_i}_{out_j}'
            pij = f'P_{out_i}_{out_j}'
        _g_i_j = Module.out_connector('ow_g', gij)
        _p_i_j = Module.out_connector('ow_p', pij)

        inputs = [_g_i_k, _p_i_k, _g_km1_j, _p_km1_j]
        outputs = [_g_i_j, _p_i_j]

        i, j = c, self.p_i_j(c, r).split('_')[-1]
        if in1_i == in1_j or in2_i == in2_j:
            wires = [output['connector'] for output in outputs]
        elif out_j == 0:
            wires = [input['connector'] for input in inputs]
        else:
            wires = [input['connector'] for input in inputs] + [output['connector'] for output in outputs]
        j = int(j.split('.')[0])
        b = Black()
        b_str = b.instantiate(instance_name=f'black_block_{i}_{j}', inputs=inputs, outputs=outputs)
        return wires, b_str

    def gray_block(self, r, c, block_in):
        # print('---------------- Gray Block ----------------')
        height = self.height()
        # Inputs
        in1_i, in1_j = self.input_i_j(r, c)
        in2_i, in2_j = self.input_i_j(r, block_in)
        if r >= math.ceil(height/2):
            in2_j = 0

        if in1_i == in1_j:
            gik = f'i_g[{in1_i}]'
            pik = f'i_p[{in1_i}]'
        else:
            gik = f'G_{in1_i}_{in1_j}'
            pik = f'P_{in1_i}_{in1_j}'
        if in2_i == in2_j:
            g_km1 = f'i_g[{in2_i}]'
        elif in2_j in ['0', 0]:
            g_km1 = f'ow_gg[{in2_i}]'
        else:
            f'G_{in2_i}_{in2_j}'
        _g_i_k = Module.in_connector('i_g', gik)
        _p_i_k = Module.in_connector('i_p', pik)
        _g_km1_j = Module.in_connector('i_g_km1', g_km1)

        # Outputs
        out_i, out_j = self.output_i_j(r, c)
        gij = f'ow_gg[{out_i}]' if out_j == 0 else f'G_{out_i}_{out_j}'
        _g_i_j = Module.out_connector('ow_g', gij)

        inputs = [_g_i_k, _p_i_k, _g_km1_j]
        outputs = [_g_i_j]

        i, j = c, self.p_i_j(c, r).split('_')[-1]
        if r == 0:
            wires = [output['connector'] for output in outputs]
        elif r == height-1:
            wires = [input['connector'] for input in inputs]
        else:
            wires = [input['connector'] for input in inputs] + [output['connector'] for output in outputs]
        j = int(j.split('.')[0])
        g = Gray()
        g_str = g.instantiate(instance_name=f'gray_block_{i}_{j}', inputs=inputs, outputs=outputs)
        return wires, g_str


    def verilog(self, file_path):  # sourcery skip: low-code-quality
        all_wires = []
        for r in range(self.row):
            for c in range(self.col):
                block_type, block_in = self.block_matrix[r][c]

                if block_type in ['Black', 'Gray']:
                    new_wires, new_block = None, None
                    new_wires, new_block = (
                        self.black_block(r, c, block_in)
                        if block_type == 'Black'
                        else self.gray_block(r, c, block_in)
                    )
                    for wire in new_wires:
                        if wire not in all_wires:
                            all_wires.append(wire)

                    self.instruction(new_block)

                elif block_type in ['Buffer', '|']:
                    continue
                else:
                    exit()

        for wire in all_wires:
            wire_min = wire.split('[')[0]
            if wire_min in ('i_g', 'i_p', 'ow_gg', 'ow_pp'):
                continue
            i, j = wire.split('_')[-2], wire.split('_')[-1]
            self.wire(wire, '')

        self.instruction('assign ow_gg[0] = i_g[0];')
        self.instruction('assign ow_pp[0] = i_p[0];')

        self.start()

        self.end()

        self.write(file_path, f'{self.module_name}.sv')

