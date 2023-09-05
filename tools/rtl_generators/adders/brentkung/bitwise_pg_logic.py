from .pg import PG as PG
import verilog as verilog


class BitwisePGLogic:
    module_name = 'math_adder_brent_kung_bitwisepg'

    def __init__(self, bitwidth):
        self.bitwidth = bitwidth
        self.buswidth = bitwidth
        self.unique = True


    def verilog(self, file_path, file_name):
        # sourcery skip: extract-duplicate-method
        m = verilog.Module(BitwisePGLogic.module_name, buswidth=self.buswidth, unique=False)

        m.input('i_a', '[N-1:0]')
        m.input('i_b', '[N-1:0]')
        m.input('i_c', '')
        m.output('ow_g', '[N:0]')
        m.output('ow_p', '[N:0]')
        m.instruction('// Loop over bits')
        m.instruction('genvar k;')
        m.instruction('generate')
        m.instruction('    for (k = 0; k < N; k=k+1) begin : gen_loop ')
        m.instruction('        math_adder_brent_kung_pg PG_Bit(.i_a(i_a[k]),.i_b(i_b[k]),.ow_p(ow_p[k+1]),.ow_g(ow_g[k+1]));')
        m.instruction('    end')
        m.instruction('endgenerate')
        m.instruction('')
        m.instruction("assign ow_p[0] = 'b0;")
        m.instruction("assign ow_g[0] = i_c;")

        m.start()

        m.end()

        m.write(file_path, file_name)

    def instantiation(self, module_name, param, instance_name, inputs, outputs):
        """
            inputs: dict{ port: ? , connector: ?}
            outputs: dict{ port: ? , connector: ?}
        """
        param = '#(.N(N))'
        return verilog.Module.instantiate(module_name=module_name,
                                          param=param,
                                          instance_name=instance_name,
                                          inputs=inputs,
                                          outputs=outputs)
