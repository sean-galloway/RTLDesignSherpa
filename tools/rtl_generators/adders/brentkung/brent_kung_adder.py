import verilog as verilog

from .bitwise_pg_logic import BitwisePGLogic as BitwisePGLogic
from .group_pg_logic import GroupPGLogic as GroupPGLogic
from .sum_logic import SumLogic as SumLogic


class BrentKungAdder:
    module_name = 'math_adder_brent_kung'

    def __init__(self, bitwidth):
        self.bitwidth = bitwidth
        self.buswidth = bitwidth
        self.unique = False


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

    def add_module(self, m, module, module_name, param, instance_name, inputs, outputs, top_ports, wires):
        instance = module.instantiation(module_name=module_name, param=param, instance_name=instance_name, inputs=inputs, outputs=outputs)

        m.instruction(instance)

        wires = self.add_new_wires(top_ports, wires, inputs)
        wires = self.add_new_wires(top_ports, wires, outputs)

        return m, wires

    def verilog(self, file_path, file_name):
        # sourcery skip: extract-duplicate-method
        mod_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'
        m = verilog.Module(mod_name, buswidth=self.buswidth, unique=False)
        # Inputs
        m.input('i_a', '[N-1:0]')
        m.input('i_b', '[N-1:0]')
        m.input('i_c', '')
        # Outputs
        m.output('ow_sum', '[N-1:0]')
        m.output('ow_carry', '')
        top_ports = ['i_a', 'i_b', 'i_c', 'ow_sum', 'ow_carry']
        wires = []


        mod_name = BitwisePGLogic.module_name
        m, wires = self.add_module(m=m,
                                   module=BitwisePGLogic(self.bitwidth),
                                   module_name=mod_name,
                                   param='#(.N(N))',
                                   instance_name="BitwisePGLogic_inst",
                                   inputs=self.bitwise_pg_logic_inputs(),
                                   outputs=self.bitwise_pg_logic_outputs(),
                                   top_ports=top_ports,
                                   wires=wires)


        mod_name = f'{GroupPGLogic.module_name}_{str(self.buswidth).zfill(3)}'
        m, wires = self.add_module(m=m,
                                   module=GroupPGLogic(self.bitwidth),
                                   module_name=mod_name,
                                   param='#(.N(N))',
                                   instance_name="GroupPGLogic_inst",
                                   inputs=self.group_pg_logic_inputs(),
                                   outputs=self.group_pg_logic_outputs(),
                                   top_ports=top_ports,
                                   wires=wires)


        mod_name = SumLogic.module_name
        m, wires = self.add_module(m=m,
                                   module=SumLogic(self.bitwidth),
                                   module_name=mod_name,
                                   param='#(.N(N))',
                                   instance_name="SumLogic_inst",
                                   inputs=self.sum_logic_inputs(),
                                   outputs=self.sum_logic_outputs(),
                                   top_ports=top_ports,
                                   wires=wires)

        mod_name = f'{self.module_name}_{str(self.buswidth).zfill(3)}'
        m.instruction('// synopsys translate_off')
        m.instruction('initial begin')
        m.instruction('    $dumpfile("dump.vcd");')
        m.instruction(f'    $dumpvars(0, {mod_name});')
        m.instruction('end')
        m.instruction('// synopsys translate_on')
        m.instruction('')

        # Wires
        # ports = [verilog.Module(BrentKungAdder).inputs, verilog.Module(BrentKungAdder).outputs]
        for wire in wires:
            wire_name = wire['connector']
            wire_type = wire['type']
            m.wire(wire_name, wire_type)

        m.start()

        m.end()

        m.write(file_path, file_name)

    def instantiation(self, mod_name, instance_name, inputs, outputs):
        """
            inputs: dict{ port: ? , connector: ?}
            outputs: dict{ port: ? , connector: ?}
        """
        return verilog.Module.instantiate(module_name=mod_name,
                                          param='#(.N(N))',
                                          instance_name=instance_name,
                                          inputs=inputs,
                                          outputs=outputs)
