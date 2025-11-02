rm -rf ./PNG
mkdir ./PNG
rm -rf ./SVG
mkdir -p ./SVG
find ./ -name "*.json" | while read file; do
    # Extract the test directory name (e.g., test_gaxi_skid_buffer_arrows_moderate)
    test_name=$(echo "$file" | sed 's|^\./local_sim_build/\([^/]*\)/.*|\1|')
    # Extract just the filename without extension
    base_name=$(basename "${file%.json}")
    # Create output with test name prepended
    wavedrom-cli -i "$file" -s "./SVG/${test_name}_${base_name}.svg" -p "./PNG/${test_name}_${base_name}.png"
#    wavedrom-cli -i "$file" -s "./SVG/${test_name}_${base_name}.svg"
#    wavedrom-cli -i "$file" -p "./PNG/${test_name}_${base_name}.png"
done

