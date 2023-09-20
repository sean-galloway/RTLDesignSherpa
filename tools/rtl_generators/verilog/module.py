import re
from signal import Signal, Param

class Module(object):
    def __init__(self, module_name, buswidth=None, unique= True):
        self.start_instructions = []
        self.instructions = []
        self.end_instructions = []
        self.module_name = module_name
        self.param_list = Param()
        self.ports = Signal()
        self.wires = Signal()
        self.unique = unique


    def add_port_string(self, ports: str):
        self.ports(ports)
    

    def add_wire_string(self, wires: str):
        self.wires(wires)


    def start(self):
        param = f'#(parameter N={self.buswidth})' if self.unique is False else ''
        mod_name = self.module_name

        module = f'module {mod_name} {param}(\n'
        module += self.ports.create_port_string()

        module += ');\n'
        self.start_instructions.append(module)

        wires = self.wires.create_wire_string()
        self.start_instructions.append(wires)


    def end(self):
        self.end_instructions.append('endmodule')


    def stmt_assign(self, lhs, rhs):
        self.instructions.append(f'assign {lhs} = {rhs} ;')


    def instruction(self, instruction):
        self.instructions.append(instruction)


    def comment(self, c):
        self.instructions.append(f'// {c}')


    def write(self, file_path, filename):
        all_instructions = self.start_instructions + self.instructions + self.end_instructions
        with open(f'{file_path}/{filename}', 'w') as f:
            for insts in all_instructions:
                f.write(f'{insts}\n')


    def __str__(self):
        return '\n'.join(self.instructions)


    @staticmethod
    def instantiate(module_name, param, instance_name, inputs, outputs):
        """
            inputs: [dict{ port: ? , connector: ?}]
            outputs: [dict{ port: ? , connector: ?}]
        """
        # Ports
        ports = inputs + outputs
        ports = ['.{port}({connector})'.format(
            port=port['port'], connector=port['connector']) for port in ports]
        ports = ','.join(ports)

        return f'{module_name} {param} {instance_name}({ports});'


    @staticmethod
    def in_connector(port, connector):
        return {
            'port': port,
            'connector': connector
        }


    @staticmethod
    def out_connector(port, connector):
        return {
            'port': port,
            'connector': connector
        }
