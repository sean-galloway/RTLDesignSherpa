
from .signal import Signal
from .param import Param

class Module(object):
    def __init__(self, module_name='', instance_name=''):
        self.start_instructions = []
        self.instructions = []
        self.end_instructions = []
        self.module_name = module_name
        self.instance_name = instance_name
        self.params = Param()
        self.ports = Signal()
        self.wires = []


    def add_port_string(self, ports: str):
        self.ports(ports)
    

    def wire(self, name, _type):
        self.wires.append({'name':name, 'type':_type})


    def start(self):
        mod_name = self.module_name

        if len(self.params.paramrec_list) > 0:
            params = self.params.create_param_string()
            param_str = f'#({params})' 
            module = f'`timescale 1ns / 1ps\n\nmodule {mod_name} {param_str}(\n'
        else:
            module = f'`timescale 1ns / 1ps\n\nmodule {mod_name}(\n'

        module += self.ports.create_port_string()

        module += ');\n'
        self.start_instructions.append(module)

        for wire in self.wires:
            self.start_instructions.append(f"logic {wire['type']} {wire['name']};")


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


    def instantiate(self, instance_name, inputs, outputs):
        """
            inputs: [dict{ port: ? , connector: ?}]
            outputs: [dict{ port: ? , connector: ?}]
        """
        # Ports
        ports = inputs + outputs
        ports = ['.{port}({connector})'.format(
            port=port['port'], connector=port['connector']) for port in ports]
        ports = ','.join(ports)
        param = self.params.create_param_instance()
        return (
            f'{self.module_name} #({param}) {instance_name}({ports});'
            if len(self.params.paramrec_list) > 0
            else f'{self.module_name} {instance_name}({ports});'
        )


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
