
from rtl_generators.verilog.module import Module


class PG(Module):
    module_str = 'math_adder_brent_kung_pg'
    port_str = '''
    input  logic  i_a,
    input  logic  i_b,
    output logic  ow_g,
    output logic  ow_p
    '''

    def __init__(self):
        super().__init__(module_name=self.module_str)
        self.ports.add_port_string(self.port_str)

    def verilog(self, file_path):
        # Start
        self.start()

        # Assignments
        self.stmt_assign('ow_g', 'i_a & i_b')
        self.stmt_assign('ow_p', 'i_a ^ i_b')


        # End
        self.end()

        # Write File
        self.write(file_path, f'{self.module_name}.sv')

