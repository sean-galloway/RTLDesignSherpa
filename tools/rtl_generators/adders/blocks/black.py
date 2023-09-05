import verilog.module as module


class BlackBlock:
    module_name = 'math_adder_brent_kung_black'

    def __init__(self):
        self.unique = True

    def inputs(self):
        return ['i_g', 'i_p', 'i_g_km1', 'i_p_km1']

    def outputs(self):
        return ['ow_g', 'ow_p']

    def verilog(self, file_path, file_name):
        m = module.Module(BlackBlock.module_name)

        # Inputs
        for input in self.inputs():
            m.input(input, '')
        # Outputs
        for output in self.outputs():
            m.output(output, '')

        # Start
        m.start()

        # Assignments
        m.stmt_assign('ow_g', 'i_g | ( i_p & i_g_km1 )')
        m.stmt_assign('ow_p', 'i_p & i_p_km1')

        # End
        m.end()

        # Write File
        m.write(file_path, file_name)

    @staticmethod
    def instantiation(instance_name, inputs, outputs):
        """
            inputs: [dict{ port: ? , connector: ?}]
            outputs: [dict{ port: ? , connector: ?}]
        """
        return module.Module.instantiate(module_name=BlackBlock.module_name,
                                         param='',
                                         instance_name=instance_name,
                                         inputs=inputs,
                                         outputs=outputs)
