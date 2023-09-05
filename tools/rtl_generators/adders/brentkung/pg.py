import verilog as verilog


class PG:
    module_name = 'math_adder_brent_kung_pg'

    def __init__(self):
        self.unique = True

    def verilog(self, file_path, file_name):
        m = verilog.Module(PG.module_name)


        m.input('i_a', '')
        m.input('i_b', '')
        m.output('ow_g', '')
        m.output('ow_p', '')

        # Assignments
        m.stmt_assign('ow_g', 'i_a & i_b')
        m.stmt_assign('ow_p', 'i_a ^ i_b')

        # Start
        m.start()
        # End
        m.end()

        # Write File
        m.write(file_path, file_name)

    def instantiation(self, instance_name, inputs, outputs):
        """
            inputs: [dict{ port: ? , connector: ?}]
            outputs: [dict{ port: ? , connector: ?}]
        """
        return verilog.Module.instantiate(module_name=PG.module_name,
                                          instance_name=instance_name,
                                          inputs=inputs,
                                          outputs=outputs)
