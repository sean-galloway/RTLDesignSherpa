
from rtl_generators.verilog.module import Module

class Black(Module):
    module_str = 'math_adder_brent_kung_black'
    port_str = '''
    input  logic  i_g,
    input  logic  i_p,
    input  logic  i_g_km1,
    input  logic  i_p_km1,
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
        self.stmt_assign('ow_g', 'i_g | ( i_p & i_g_km1 )')
        self.stmt_assign('ow_p', 'i_p & i_p_km1')

        # End
        self.end()

        # Write File
        self.write(file_path, f'{self.module_name}.sv')
