from rtl_generators.verilog.module import Module


class BitwisePGLogic(Module):
    module_str = 'math_adder_brent_kung_bitwisepg'
    param_str = 'parameter int N=8'
    port_str = '''
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_c,
    output logic [N:0]   ow_g,
    output logic [N:0]   ow_p
    '''

    def __init__(self, buswidth):
        self.buswidth = buswidth
        super().__init__(module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)


    def verilog(self, file_path):
        # sourcery skip: extract-duplicate-method
        self.start()

        # Instructions
        self.instruction('// Loop over bits')
        self.instruction('genvar k;')
        self.instruction('generate')
        self.instruction('    for (k = 0; k < N; k=k+1) begin : gen_loop ')
        self.instruction('        math_adder_brent_kung_pg PG_Bit(.i_a(i_a[k]),.i_b(i_b[k]),.ow_p(ow_p[k+1]),.ow_g(ow_g[k+1]));')
        self.instruction('    end')
        self.instruction('endgenerate')
        self.instruction('')
        self.instruction("assign ow_p[0] = 'b0;")
        self.instruction("assign ow_g[0] = i_c;")

        self.end()

        self.write(file_path, f'{self.module_name}.sv')

