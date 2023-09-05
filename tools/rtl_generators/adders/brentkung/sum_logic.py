import verilog as verilog


class SumLogic:
    module_name = 'math_adder_brent_kung_sum'

    def __init__(self, bitwidth):
        self.bitwidth = bitwidth
        self.buswidth = bitwidth
        self.unique = True


    def inputs(self):
        Ps = 'w_p'
        Gs = 'w_gg'
        return Ps, Gs


    def outputs(self):
        Ss = 'ow_sum'
        c_out = 'ow_carry'
        return c_out, Ss


    def verilog(self, file_path, file_name):
        # sourcery skip: extract-duplicate-method
        m = verilog.Module(SumLogic.module_name, self.bitwidth, False)

        m.input('i_p', '[N:0]')
        m.input('i_gg', '[N:0]')
        m.output('ow_sum', '[N-1:0]')
        m.output('ow_carry', '')
        m.instruction('// Loop over bits')
        m.instruction('genvar k;')
        m.instruction('generate')
        m.instruction('    for (k = 0; k < N; k=k+1) begin : gen_loop ')
        m.instruction('        assign ow_sum[k] = i_gg[k] ^ i_p[k+1];')
        m.instruction('    end')
        m.instruction('endgenerate')
        m.instruction('')
        m.instruction('assign ow_carry = i_gg[N];')

        m.start()

        m.end()

        m.write(file_path, file_name)

    def instantiation(self, module_name, param, instance_name, inputs, outputs):
        """
            inputs: dict{ port: ? , connector: ?}
            outputs: dict{ port: ? , connector: ?}
        """
        return verilog.Module.instantiate(module_name=module_name,
                                          param=param,
                                          instance_name=instance_name,
                                          inputs=inputs,
                                          outputs=outputs)
