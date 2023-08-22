import sys
import argparse


def generate_partial_products(N, f):
    # Generate partial products
    f.write("// Partial products generation\n")

    # Define bit groups here, then populate it as we generate the partial products
    bit_groups = {i: [] for i in range(2 * N)}

    # Determine the max number of digits needed
    max_digits = len(str(N - 1))
    
    for i in range(N):
        for j in range(N):
            # Ensure numbers are formatted with the required leading zeros
            formatted_i = str(i).zfill(max_digits)
            formatted_j = str(j).zfill(max_digits)

            f.write(f"wire w_pp_{formatted_i}_{formatted_j} = i_multiplier[{i:2}] & i_multiplicand[{j:2}];\n")
            bit_groups[i + j].append(f"w_pp_{formatted_i}_{formatted_j}")

    f.write("\n")
    return bit_groups


def reduce_partial_products(bit_groups, N, f):
    f.write("// Partial products reduction using Wallace tree\n")

    # Calculate the maximum number of digits needed based on 2*N and the maximum number of partial products.
    max_digits_idx = len(str(2 * N - 1))
    max_digits_len = len(str(max(len(group) for group in bit_groups.values())))

    for bit_idx in range(2 * N - 1):
        while len(bit_groups[bit_idx]) > 2:
            # If there are three or more bits, use a full adder
            a, b, c = bit_groups[bit_idx][:3]
            formatted_idx = str(bit_idx).zfill(max_digits_idx)
            formatted_len = str(len(bit_groups[bit_idx])).zfill(max_digits_len)

            sum_name = f"w_sum_{formatted_idx}_{formatted_len}"
            carry_name = f"w_carry_{formatted_idx}_{formatted_len}"

            f.write(f"wire {sum_name}, {carry_name};\n")
            f.write(f"math_adder_full FA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_c({carry_name}));\n")

            # Remove the used bits and append the new sum and carry
            bit_groups[bit_idx] = bit_groups[bit_idx][3:]
            bit_groups[bit_idx].append(sum_name)
            bit_groups[bit_idx + 1].append(carry_name)
            
        while len(bit_groups[bit_idx]) == 2:
            # If there are two bits, use a half adder
            a, b = bit_groups[bit_idx][:2]
            formatted_idx = str(bit_idx).zfill(max_digits_idx)
            formatted_len = str(len(bit_groups[bit_idx])).zfill(max_digits_len)

            sum_name = f"w_sum_{formatted_idx}_{formatted_len}"
            carry_name = f"w_carry_{formatted_idx}_{formatted_len}"

            f.write(f"wire {sum_name}, {carry_name};\n")
            f.write(f"math_adder_half HA_{formatted_idx}_{formatted_len}(.i_a({a}), .i_b({b}), .ow_sum({sum_name}), .ow_c({carry_name}));\n")

            # Remove the used bits and append the new sum and carry
            bit_groups[bit_idx] = bit_groups[bit_idx][2:]
            bit_groups[bit_idx].append(sum_name)
            bit_groups[bit_idx + 1].append(carry_name)

    f.write("\n")


def generate_final_assignments(bit_groups, N, f):
    f.write("// Final product assignment\n")
    
    # Calculate maximum width based on the largest index.
    max_width = len(str(2 * N - 1))
    
    for i in range(2 * N):
        idx_str = str(i).rjust(max_width)  # Format index with spaces on the left
        if bit_groups[i]:
            f.write(f"assign ow_product[{idx_str}] = {bit_groups[i][0]};\n")
        else:
            f.write(f"assign ow_product[{idx_str}] = 0;\n")
    f.write("\n")


def generate_wallace_tree(N):
    filename = f"math_multiplier_wallace_tree_{N}.sv"

    with open(filename, 'w') as f:
        f.write(f"`timescale 1ns / 1ps\n\n")
        # Module header
        f.write(f"module math_multiplier_wallace_tree_{N} (\n")
        f.write(f"    input  [{N - 1}:0] i_multiplier,\n")
        f.write(f"    input  [{N - 1}:0] i_multiplicand,\n")
        f.write(f"    output [{2 * N - 1}:0] ow_product\n")
        f.write(f");\n\n")

        # Get initial bit groups directly from the generate_partial_products function
        bit_groups = generate_partial_products(N, f)
        reduce_partial_products(bit_groups, N, f)

        # Generating final assignments
        generate_final_assignments(bit_groups, N, f)

        # Debug
        f.write(f'''
    // Debug purposes
    // synopsys translate_off
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, math_multiplier_wallace_tree_{N});
    end
    // synopsys translate_off
                ''')
        # End of module
        f.write(f"\nendmodule : math_multiplier_wallace_tree_{N}\n")

    print(f"Wallace tree multiplier for N={N} generated and saved as '{filename}'.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate Wallace Tree Multiplier for given N")
    parser.add_argument("-n", required=True, type=int, help="Specify the size N for the Wallace Tree Multiplier")
    args = parser.parse_args()

    if not args.n:
        print("Usage: python generate_wallace_tree.py -n <N>")
        sys.exit(1)

    N = args.n
    generate_wallace_tree(N)
