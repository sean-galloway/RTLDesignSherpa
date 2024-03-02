from rtl_generators.verilog.module import Module

from .partial_products import PartialProducts
from .wallace_reduction import WallaceReduction


class WallaceTree(Module):
    module_str = 'math_multiplier_wallace_tree'
    param_str = 'parameter N=8'
    port_str = '''
    input  logic  [N-1:0]    i_multiplier,
    input  logic  [N-1:0]    i_multiplicand,
    output logic  [2*N-1:0]  ow_product
    '''

    def __init__(self, type, buswidth):
        self.buswidth = buswidth
        self.type = type
        super().__init__(module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        self.params.set_param_value('N', self.buswidth)
        if type == 'csa':
            self.module_name = f'{self.module_name}_csa_{str(self.buswidth).zfill(3)}'
        else:
            self.module_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'

    def pp_logic_inputs(self):
        i_multiplier = {"port": "i_multiplier", "connector": "i_multiplier", "type":"[N-1:0]"}
        i_multiplicand = {"port": "i_multiplicand", "connector": "i_multiplicand", "type":"[N-1:0]"}
        return [i_multiplier, i_multiplicand]
    
    def pp_logic_outputs(self):
        ow_pp = {"port": "ow_pp", "connector": "ow_pp", "type":"[N-1:0][N-1:0]"}
        return [ow_pp]

    def wallace_reduction_inputs(self):
        ow_pp = {"port": "i_pp", "connector": "ow_pp", "type":"[N-1:0][N-1:0]"}
        return [ow_pp]

    def wallace_reduction_outputs(self):
        ow_product = {"port": "ow_product", "connector": "ow_product", "type":"[2*N-1:0]"}
        return [ow_product]


    def add_new_wires(self, top_ports, prev_wires, new_wires):
        prev_ports = [item['connector'] for item in prev_wires] # these are the names only for quick searches
        for w in new_wires:
            conname = w['connector']
            if conname in top_ports or conname in prev_ports:
                continue
            prev_wires.append(w)
            prev_ports.append(conname)
        return prev_wires

    def add_module(self, m, instance_name, inputs, outputs, top_ports, wires):
        instance = m.instantiate(instance_name=instance_name, inputs=inputs, outputs=outputs)

        self.instruction(instance)

        wires = self.add_new_wires(top_ports, wires, inputs)
        wires = self.add_new_wires(top_ports, wires, outputs)

        return wires

    def verilog(self, file_path):
        # sourcery skip: extract-duplicate-method

        top_ports = ["i_multiplier", "i_multiplicand", 'ow_product']
        wires = []

        mod = PartialProducts(buswidth=self.buswidth)
        mod.params.set_param_value('N', 'N')
        wires = self.add_module(m=mod,
                                    instance_name="PartialProducts_inst",
                                    inputs=self.pp_logic_inputs(),
                                    outputs=self.pp_logic_outputs(),
                                    top_ports=top_ports,
                                    wires=wires)

        mod = WallaceReduction(type=self.type, buswidth=self.buswidth)
        mod.params.set_param_value('N', 'N')
        wires = self.add_module(m=mod,
                                    instance_name="WallaceReduction_inst",
                                    inputs=self.wallace_reduction_inputs(),
                                    outputs=self.wallace_reduction_outputs(),
                                    top_ports=top_ports,
                                    wires=wires)

        self.instruction('')
        self.instruction('// synopsys translate_off')
        self.instruction('initial begin')
        self.instruction('    $dumpfile("waves.vcd");')
        self.instruction(f'    $dumpvars(0, {self.module_name});')
        self.instruction('end')
        self.instruction('// synopsys translate_on')
        self.instruction('')

        # Wires
        for wire in wires:
            wire_name = wire['connector']
            wire_type = wire['type']
            self.wire(wire_name, wire_type)

        self.start()

        self.end()

        self.write(file_path, f'{self.module_name}.sv')
