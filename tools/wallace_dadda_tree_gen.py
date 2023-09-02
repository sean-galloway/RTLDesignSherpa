import sys
import argparse
import math

def generate_partial_products(N, f):
    # Generate partial products
    f.write("// Partial products generation\n")

    # Define bit groups here, then populate it as we generate the partial products
    bit_groups = {i: [] for i in range(2 * N)}

    # Determine the max number of digits needed
    max_digits = len(str(N - 1))
    
    for i in range(N):
        for j in range(N):
            formatted_i = str(i).zfill(max_digits)
            formatted_j = str(j).zfill(max_digits)

            f.write(f"wire w_pp_{formatted_i}_{formatted_j} = i_multiplier[{i:2}] & i_multiplicand[{j:2}];\n")
            bit_groups[i + j].append(f"w_pp_{formatted_i}_{formatted_j}")

    f.write("\n")
    return bit_groups


def generate_booth_radix_4_partial_products(N, f):
    # Generate partial products using Booth Radix-4
    f.write("// Partial products generation using Booth Radix-4\n")

    num_digits_i = int(math.log10(N)) + 1
    num_digits_j = int(math.log10(N//2)) + 1

    bit_groups = {i: [] for i in range(2 * N)}

    for j in range(0, N, 2):
        formatted_j = str(j // 2).zfill(num_digits_j)

        f.write(f"wire [N-1:0] w_booth_encoded_{formatted_j};\n")
        f.write(f"math_booth_encoding #(.N(N)) booth_instance_{formatted_j} (")
        f.write(f".i_sel(i_multiplier[{j+1}:{j}]), ")
        f.write(".i_multiplicand(i_multiplicand), ")
        f.write(f".ow_result(w_booth_encoded_{formatted_j}));\n")

        for k in range(N):
            bit_groups[j + k].append(f"w_booth_encoded_{formatted_j}[{k}]")

    f.write("\n")
    return bit_groups


def generate_dadda_numbers(N):
    dadda_numbers = [2]
    next_number = 2
    multiply_by = 1.5  # Start by multiplying by 1.5

    while True:
        next_number = math.ceil(next_number * multiply_by)
        if next_number > N:
            break
        dadda_numbers.append(next_number)
        multiply_by = 4 / 3 if multiply_by == 1.5 else 1.5
    return dadda_numbers[::-1]

def num_stages_needed(dadda_numbers):
    return len(dadda_numbers)

def max_height(dadda_numbers, stage):
    return dadda_numbers[stage]

def dadda_reduction(bit_groups, N, f):
    unique_id = 0
    dadda_numbers = generate_dadda_numbers(N-1)
    num_stages = num_stages_needed(dadda_numbers)
    
    for stage in range(num_stages):
        max_h = max_height(dadda_numbers, stage)
        f.write(f"// Stage: {stage}, Max Height: {max_h}\n")

        for bit_idx in list(bit_groups.keys()):
            while len(bit_groups[bit_idx]) > max_h:
                sum_name = f"w_sum_{unique_id}"
                carry_name = f"w_carry_{unique_id}"

                if len(bit_groups[bit_idx]) == max_h + 1:
                    # Implement a half-adder
                    a, b = bit_groups[bit_idx][:2]
                    f.write(f"wire {sum_name}, {carry_name};\n")
                    f.write(f"math_adder_half HA_{unique_id}(.i_a({a}), .i_b({b}), .ow_sum({sum_name}), .ow_carry({carry_name}));\n")
                    
                    bit_groups[bit_idx] = bit_groups[bit_idx][2:]
                    
                else:
                    # Implement a full-adder (or a 3-to-2 CSA)
                    a, b, c = bit_groups[bit_idx][:3]
                    f.write(f"wire {sum_name}, {carry_name};\n")
                    f.write(f"math_adder_carry_save CSA_{unique_id}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_carry({carry_name}));\n")
                    
                    bit_groups[bit_idx] = bit_groups[bit_idx][3:]

                bit_groups[bit_idx].append(sum_name)
                bit_groups[bit_idx + 1].append(carry_name)
                unique_id += 1
                
    f.write("\n")


def wallace_reduction(bit_groups, N, f, multiplier_type):
    f.write("// Partial products reduction using Wallace tree\n")

    max_digits_idx = len(str(2 * N - 1))
    max_digits_len = len(str(max(len(group) for group in bit_groups.values())))

    for bit_idx in range(2 * N - 1):
        while len(bit_groups[bit_idx]) > 2:
            a, b, c = bit_groups[bit_idx][:3]
            formatted_idx = str(bit_idx).zfill(max_digits_idx)
            formatted_len = str(len(bit_groups[bit_idx])).zfill(max_digits_len)

            sum_name = f"w_sum_{formatted_idx}_{formatted_len}"
            carry_name = f"w_carry_{formatted_idx}_{formatted_len}"

            f.write(f"wire {sum_name}, {carry_name};\n")

            if multiplier_type == "wfa":
                f.write(f"math_adder_full FA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_carry({carry_name}));\n")
            else:
                f.write(f"math_adder_carry_save CSA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_carry({carry_name}));\n")

            bit_groups[bit_idx] = bit_groups[bit_idx][3:]
            bit_groups[bit_idx].append(sum_name)
            bit_groups[bit_idx + 1].append(carry_name)

        while len(bit_groups[bit_idx]) == 2:
            a, b = bit_groups[bit_idx][:2]
            formatted_idx = str(bit_idx).zfill(max_digits_idx)
            formatted_len = str(len(bit_groups[bit_idx])).zfill(max_digits_len)

            sum_name = f"w_sum_{formatted_idx}_{formatted_len}"
            carry_name = f"w_carry_{formatted_idx}_{formatted_len}"

            f.write(f"wire {sum_name}, {carry_name};\n")
            f.write(f"math_adder_half HA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .ow_sum({sum_name}), .ow_carry({carry_name}));\n")

            bit_groups[bit_idx] = bit_groups[bit_idx][2:]
            bit_groups[bit_idx].append(sum_name)
            bit_groups[bit_idx + 1].append(carry_name)

    f.write("\n")


def generate_final_addition(bit_groups, N, f):
    # This function will generate the final addition stage.
    max_digits_bit = len(str(2*N - 1))
    print(f'{bit_groups=}')

    # Prepare output for bit by bit addition
    f.write("// Final addition stage\n")
    previous_carry = None
    carry_last = ''
    for bit in range(2*N):
        formatted_bit = str(bit).zfill(max_digits_bit)

        sum_name = f"ow_sum_{formatted_bit}"
        carry_name = f"ow_carry_{formatted_bit}"
        variables = bit_groups.get(bit, [])
        f.write(f"wire {sum_name}, {carry_name};\n")

        # if no variables are present for this bit, just output a 0
        if bit == 2*N-1 and not variables:
            f.write(f"assign {sum_name} = {carry_last};\n")
            f.write(f"assign {carry_name} = 1'b0;\n")
            carry_last = carry_name
            continue
        if not variables:
            f.write(f"assign {sum_name} = 1'b0;\n")
            f.write(f"assign {carry_name} = 1'b0;\n")
            carry_last = carry_name
            continue

        if len(variables) == 1:
            f.write(f"assign {sum_name} = {variables[0]};\n")
            f.write(f"assign {carry_name} = 1'b0;\n")
        else:
            # Wire the sum and carry
            
            ic_value = previous_carry or "1'b0"
            fa_line = f"math_adder_full FA_{formatted_bit}(.i_a({variables[0]}), .i_b({variables[1]}), .i_c({ic_value}), .ow_sum({sum_name}), .ow_carry({carry_name}));\n"
            f.write(fa_line)
            
        carry_last = carry_name

        previous_carry = carry_name

    f.write("\n")


def generate_final_assignments(N, f):
    f.write("// Final product assignment\n")

    # Calculate the maximum number of digits required
    max_digits = len(str(2 * N - 1))

    for i in range(2 * N):
        formatted_idx = str(i).zfill(max_digits)
        f.write(f"assign ow_product[{str(i).rjust(max_digits)}] = ow_sum_{formatted_idx};\n")

    f.write("\n")


def generate_tree(N, multiplier_type, use_booth):
    N_idx = str(N).zfill(3)
    booth = "_booth" if use_booth else ''
    if multiplier_type == 'wcsa':
        name = f"math_multiplier{booth}_wallace_tree_csa_{N_idx}"
        title = 'Booth Radix-4 Wallace Tree CSA'
    elif multiplier_type == 'wfa':
        name = f"math_multiplier{booth}_wallace_tree_{N_idx}"
        title = 'Booth Radix-4 Wallace Tree FA'
    else:
        name = f"math_multiplier{booth}_dadda_tree_{N_idx}"
        title = 'Booth Radix-4 Dadda Tree CSA'

    filename =f'{name}.sv'
    with open(filename, 'w') as f:
        _generate_tree_helper(f, multiplier_type, N, name, use_booth)
    print(f"{title} multiplier for N={N_idx} using {multiplier_type} generated and saved as '{filename}'.")


def _generate_tree_helper(f, multiplier_type, N, name, use_booth):
    f.write(f"`timescale 1ns / 1ps\n\n")
    f.write(f"module {name} (\n")
    f.write(f"    input  [{N - 1}:0] i_multiplier,\n")
    f.write(f"    input  [{N - 1}:0] i_multiplicand,\n")
    f.write(f"    output [{2 * N - 1}:0] ow_product\n")
    f.write(f");\n\n")

    # Select Booth or simple partial products
    if not use_booth:
        print('Not Booth')
        bit_groups = generate_partial_products(N, f)
    else:
        bit_groups = generate_booth_radix_4_partial_products(N, f)

    if multiplier_type == "dad":
        dadda_reduction(bit_groups, N, f)
    else:
        wallace_reduction(bit_groups, N, f, multiplier_type)

    generate_final_addition(bit_groups, N, f)
    generate_final_assignments(N, f)

    f.write(f'''
    // Debug purposes
    // synopsys translate_off
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, {name});
    end
    // synopsys translate_on
        ''')

    f.write(f"\nendmodule : {name}\n")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate Wallace/Dadda Tree Multiplier for given N")
    parser.add_argument("-n", required=True, type=int, help="Specify the size N for the Multiplier")
    parser.add_argument("-t", required=True, choices=["wfa", "wcsa", "dad"], help="Specify the type: wfa for Wallace Full Adder, wcsa for Wallace Carry Save Adder, or dad for Dadda Multiplier")
    parser.add_argument("-b", "--booth", action="store_true", help="Use Booth Radix-4 encoding for partial products if specified")

    args = parser.parse_args()

    if not args.n:
        print("Usage: python generate_wallace_tree.py -n <N> -t <type> [--booth]")
        sys.exit(1)

    N = args.n
    multiplier_type = args.t
    use_booth = bool(args.booth)
    generate_tree(N, multiplier_type, use_booth)