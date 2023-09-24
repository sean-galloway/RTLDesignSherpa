from rtl_generators.verilog.module import Module


class PartialProducts(Module):
    module_str = 'math_multiplier_partial_products'
    param_str = 'parameter N=8'
    port_str = '''
    input  [N-1:0] i_multiplier,
    input  [N-1:0] i_multiplicand,
    output [N-1:0][N-1:0] ow_pp
    '''

    def __init__(self, buswidth):
        self.buswidth = buswidth
        super().__init__(module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        # self.module_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'


    def verilog(self, file_path):
        # sourcery skip: extract-duplicate-method
        self.start()

        # Instructions
        self.instruction('// Loop over bits')
        self.instruction('genvar i, j;')
        self.instruction('generate')
        self.instruction('    for (i = 0; i < N; i=i+1) begin : gen_loop_i ')
        self.instruction('        for (j = 0; j < N; j=j+1) begin : gen_loop_j ')
        self.instruction('            assign ow_pp[i][j] = i_multiplier[i] & i_multiplicand[j];')
        self.instruction('        end')
        self.instruction('    end')
        self.instruction('endgenerate')
        self.instruction('')
        # for i in range(self.buswidth):
        #     for j in range(self.buswidth):
        #         self.instruction(f'    assign ow_pp[{i:2}][{j:2}] = i_multiplier[{i:2}] & i_multiplicand[{j:2}];')

        self.end()

        self.write(file_path, f'{self.module_name}.sv')

