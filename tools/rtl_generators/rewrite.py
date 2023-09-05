import argparse
import re

###############################################################################
# REMatcher is a utility class to make regex's work similar to Perl
# NOTE: if there are any changes needed in this function contact Sean.
###############################################################################
class REMatcher(object):
    ''' This is a utility function to help out with matching regex's and
        grabbing the matches out in a way that is similar to how perl
        does it.
    '''
    def __init__(self, matchstring: str) -> None:
        self.matchstring = matchstring

    def match(self, regexp: str) -> bool:
        self.rematch = re.match(regexp, self.matchstring,
                                re.IGNORECASE |
                                re.MULTILINE |
                                re.DOTALL
                                )
        return bool(self.rematch)

    def group(self, i: int) -> str:
        return "Error 999" if self.rematch is None else self.rematch.group(i)


def replace_port(prefix, match):
    port_name = match.group(1)
    port_index = int(port_name.split("_")[1])
    return f"{port_name}({prefix}[{port_index - 1}])"

def rewrite_verilog_code(input_file_name, output_file_name, N):
    with open(input_file_name, 'r') as input_file:
        verilog_code = input_file.readlines()
    spaces = ' '*(5+len(str(N)))
    code = f'module math_adder_brent_kung_{str(N).zfill(3)} (\n'
    code += f'    input  logic [{N-1}:0] i_a,\n'
    code += f'    input  logic [{N-1}:0] i_b,\n'
    code += f'    input  logic {spaces}i_c,\n'
    code += f'    output logic [{N-1}:0] ow_sum,\n'
    code += f'    output logic {spaces}ow_carry\n'
    code +=  ');\n\n'
    code += f'logic [{N}:0] w_p, w_g, w_pp, w_gg;\n\n'

    for line in verilog_code:
        m = REMatcher(line)
        if m.match('module.*'):
            continue
        if m.match(r".*wire.*"):
            continue
        if m.match(r'.*math_adder.*'):
            # Found a line to replace signals on
            line = re.sub(r'(A_\d+)\(\1\)', lambda m: replace_port('i_a', m), line)
            line = re.sub(r'(B_\d+)\(\1\)', lambda m: replace_port('i_b', m), line)
            line = re.sub(r'(S_\d+)\(\1\)', lambda m: replace_port('ow_sum', m), line)
            line = re.sub(r'\.C_0\(C_0\)', r'.C_0(i_c)', line)
            line = re.sub(r'\.C_out\(C_out\)', r'.C_out(ow_carry)', line)
            code += line

    code += f"endmodule : math_adder_brent_kung_{str(N).zfill(3)}"


    with open(output_file_name, 'w') as output_file:
        output_file.write(code)

def main():
    parser = argparse.ArgumentParser(description='Rewrite Verilog code with new port names and sizes.')
    parser.add_argument('--input', required=True, help='Path to the original Verilog code file')
    parser.add_argument('--output', required=True, help='Path to save the modified Verilog code file')
    parser.add_argument('--N', type=int, required=True, help='Value of N')

    args = parser.parse_args()

    input_filename = args.input
    output_filename = args.output
    N = args.N

    rewrite_verilog_code(input_filename, output_filename, N)
    print(f"Modified Verilog code written to '{output_filename}'.")

if __name__ == '__main__':
    main()
