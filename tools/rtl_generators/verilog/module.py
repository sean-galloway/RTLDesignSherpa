import re

class Module:
    def __init__(self, module_name, buswidth=None, unique= True):
        self.start_instructions = []
        self.instructions = []
        self.end_instructions = []
        self.module_name = module_name
        self.buswidth = buswidth
        self.inputs = []
        self.outputs = []
        self.wires = []
        self.unique = unique

    @staticmethod
    def get_left_right_ports(type):
        lt = rt = -1
        pattern1 = r'\[\s*(\d+)\s*]'
        pattern2 = r'\[\s*(\d+)\s*:\s+(\d+)\s+]'
        if match := re.findall(pattern1, type):
            lt = match(0)
            rt = match(0)
        elif match := re.findall(pattern2, type):
            lt = match(0)
            rt = match(1)
        return lt, rt

    def input(self, name, _type):
        lt_new, rt_new = Module.get_left_right_ports(_type)
        found = False
        for rec in self.inputs:
            if name == rec['name']:
                found = True
                lt, rt = Module.get_left_right_ports(rec['type]'])
                if lt_new > lt:
                    lt = lt_new
                if rt_new < rt:
                    rt = rt_new
                rec['type'] = f'[{lt}:{rt}]'
        if not found:
            self.inputs.append({
                'name': name,
                'type': _type,
            })

    def output(self, name, _type):
        lt_new, rt_new = Module.get_left_right_ports(_type)
        found = False
        for rec in self.outputs:
            if name == rec['name']:
                found = True
                lt, rt = Module.get_left_right_ports(rec['type]'])
                if lt_new > lt:
                    lt = lt_new
                if rt_new < rt:
                    rt = rt_new
                rec['type'] = f'[{lt}:{rt}]'
        if not found:
            self.outputs.append({
                'name': name,
                'type': _type,
            })

    def wire(self, name, _type):
        self.wires.append({
            'name': name,
            'type': _type
        })

    def start(self):
        param = f'#(parameter N={self.buswidth})' if self.unique is False else ''
        mod_name = self.module_name

        # print(f'{self.module_name=} {self.unique=} {mod_name=} {len(self.inputs)=} {len(self.outputs)=}')
        longest_type = 0
        for sig_list in [self.inputs, self.outputs]:  # Iterate through the lists
            for sig in sig_list:  # Iterate through the dictionaries in the list
                if len(sig['type']) > longest_type:
                    longest_type = len(sig['type'])

        for sig_list in [self.inputs, self.outputs]:
            for sig in sig_list:
                if len(sig['type']) < longest_type:
                    sig['type'] += ' ' * (longest_type - len(sig['type']))

        module = f'module {mod_name} {param}(\n'
        for input in self.inputs:
            module += f'    input  logic {input["type"]} {input["name"]},\n'
        last = len(self.outputs)
        for idx, output in enumerate(self.outputs):
            comma = ','
            if idx == last -1:
                comma = ''
            module += f'    output logic {output["type"]} {output["name"]}{comma}\n'

        module += ');\n'
        self.start_instructions.append(module)

        # for input in self.inputs:
        #     self.start_instructions.append(f"{input['type']} {input['name']};")

        # for output in self.outputs:
        #     self.start_instructions.append(f"{output['type']} {output['name']};")

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
