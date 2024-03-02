from rtl_generators.verilog.module import Module

from .bitwise_pg_logic import BitwisePGLogic as BitwisePGLogic
from .group_pg_logic import GroupPGLogic as GroupPGLogic
from .sum_logic import SumLogic as SumLogic


class BrentKungAdder(Module):
    module_str = 'math_adder_brent_kung'
    param_str = 'parameter int N=8'
    port_str = '''
    input  logic [N-1:0] i_a,
    input  logic [N-1:0] i_b,
    input  logic         i_c,
    output logic [N-1:0] ow_sum,
    output logic         ow_carry
    '''

    def __init__(self, buswidth):
        super().__init__(module_name=self.module_str)
        self.ports.add_port_string(self.port_str)
        self.params.add_param_string(self.param_str)
        self.buswidth = buswidth
        self.module_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'
        self.params.set_param_value('N', self.buswidth)



    def bitwise_pg_logic_inputs(self):
        i_a = {"port": "i_a", "connector": "i_a", "type":"[N-1:0]"}
        i_b = {"port": "i_b", "connector": "i_b", "type":"[N-1:0]"}
        i_c = {"port": "i_c", "connector": "i_c", "type":""}
                
        return [i_a, i_b, i_c]


    def bitwise_pg_logic_outputs(self):
        ow_g = {"port": "ow_g", "connector": "ow_g", "type":"[N:0]"}
        ow_p = {"port": "ow_p", "connector": "ow_p", "type":"[N:0]"}
        return [ow_g, ow_p]


    def group_pg_logic_inputs(self):
        i_p = {"port": "i_p", "connector": "ow_p", "type":"[N-1:0]"}
        i_g = {"port": "i_g", "connector": "ow_g", "type":"[N-1:0]"}
        return [i_g, i_p]


    def group_pg_logic_outputs(self):
        ow_gg = {"port": "ow_gg", "connector": "ow_gg", "type":"[N:0]"}
        return [ow_gg]

    def sum_logic_inputs(self):
        i_p = {"port": "i_p", "connector": "ow_p", "type":"[N:0]"}
        i_gg = {"port": "i_gg", "connector": "ow_gg", "type":"[N:0]"}
        return [i_p, i_gg]

    def sum_logic_outputs(self):
        ow_sum = {"port": "ow_sum", "connector": "ow_sum", "type":"[N-1:0]"}
        ow_carry = {"port": "ow_carry", "connector": "ow_carry", "type":""}
        return [ow_sum, ow_carry]

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

        top_ports = ['i_a', 'i_b', 'i_c', 'ow_sum', 'ow_carry']
        wires = []

        mod = BitwisePGLogic(buswidth=self.buswidth)
        mod.params.set_param_value('N', 'N')
        wires = self.add_module(m=mod,
                                    instance_name="BitwisePGLogic_inst",
                                    inputs=self.bitwise_pg_logic_inputs(),
                                    outputs=self.bitwise_pg_logic_outputs(),
                                    top_ports=top_ports,
                                    wires=wires)

        mod = GroupPGLogic(buswidth=self.buswidth)
        mod.params.set_param_value('N', 'N')
        wires = self.add_module(m=mod,
                                    instance_name="GroupPGLogic_inst",
                                    inputs=self.group_pg_logic_inputs(),
                                    outputs=self.group_pg_logic_outputs(),
                                    top_ports=top_ports,
                                    wires=wires)

        mod = SumLogic(buswidth=self.buswidth)
        mod.params.set_param_value('N', 'N')
        wires = self.add_module(m=mod,
                                    instance_name="SumLogic_inst",
                                    inputs=self.sum_logic_inputs(),
                                    outputs=self.sum_logic_outputs(),
                                    top_ports=top_ports,
                                    wires=wires)

        self.instruction('// synopsys translate_off')
        self.instruction('initial begin')
        self.instruction('    $dumpfile("waves.vcd");')
        self.instruction(f'    $dumpvars(0, {self.module_name});')
        self.instruction('end')
        self.instruction('// synopsys translate_on')
        self.instruction('')

        # Wires
        # ports = [verilog.Module(BrentKungAdder).inputs, verilog.Module(BrentKungAdder).outputs]
        for wire in wires:
            wire_name = wire['connector']
            wire_type = wire['type']
            self.wire(wire_name, wire_type)

        self.start()

        self.end()

        self.write(file_path, f'{self.module_name}.sv')
