import sys
import argparse

def generate_partial_products(N, f):
    # Generate partial products
    f.write("// Partial products generation\n")
    
    # Define bit groups here, then populate it as we generate the partial products
    bit_groups = {i: [] for i in range(2 * N)}
    
    for i in range(N):
        for j in range(N):
            f.write(f"wire w_pp_{i}_{j} = i_multiplier[{i}] & i_multiplicand[{j}];\n")
            bit_groups[i + j].append(f"w_pp_{i}_{j}")

    f.write("\n")
    return bit_groups

def reduce_partial_products(bit_groups, N, f):
    f.write("// Partial products reduction using Wallace tree\n")

    for bit_idx in range(2 * N - 1):
        while len(bit_groups[bit_idx]) > 2:
            # If there are three or more bits, use a full adder
            a, b, c = bit_groups[bit_idx][:3]
            sum_name = f"w_sum_{bit_idx}_{len(bit_groups[bit_idx])}"
            carry_name = f"w_carry_{bit_idx}_{len(bit_groups[bit_idx])}"

            f.write(f"wire {sum_name}, {carry_name};\n")
            f.write(f"math_adder_full FA_{bit_idx}_{len(bit_groups[bit_idx])}(.i_a({a}), .i_b({b}), .i_c({c}), .ow_sum({sum_name}), .ow_c({carry_name}));\n")

            # Remove the used bits and append the new sum and carry
            bit_groups[bit_idx] = bit_groups[bit_idx][3:]
            bit_groups[bit_idx].append(sum_name)
            bit_groups[bit_idx + 1].append(carry_name)
            
        while len(bit_groups[bit_idx]) == 2:
            # If there are two bits, use a half adder
            a, b = bit_groups[bit_idx][:2]
            sum_name = f"w_sum_{bit_idx}_{len(bit_groups[bit_idx])}"
            carry_name = f"w_carry_{bit_idx}_{len(bit_groups[bit_idx])}"

            f.write(f"wire {sum_name}, {carry_name};\n")
            f.write(f"math_adder_half HA_{bit_idx}_{len(bit_groups[bit_idx])}(.i_a({a}), .i_b({b}), .ow_sum({sum_name}), .ow_c({carry_name}));\n")

            # Remove the used bits and append the new sum and carry
            bit_groups[bit_idx] = bit_groups[bit_idx][2:]
            bit_groups[bit_idx].append(sum_name)
            bit_groups[bit_idx + 1].append(carry_name)

    f.write("\n")

def generate_final_assignments(bit_groups, N, f):
    f.write("// Final product assignment\n")
    
    for i in range(2 * N):
        if bit_groups[i]:
            f.write(f"assign ow_product[{i}] = {bit_groups[i][0]};\n")
        else:
            f.write(f"assign ow_product[{i}] = 0;\n")
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
    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, math_multiplier_wallace_tree_{N});
    end
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
