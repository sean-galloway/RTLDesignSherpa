import os
import re

# Example mapping (old -> new)
old2new_map = {
        "APB" : "apb",
        "APBTransactionExtra": "apb_transaction_extra",
        "ConstrainedRandom": "constrained_random",
        "FlexRandomizer": "delay_randomizer",
        "MemoryModel": "memory_model",
        "RegisterMap": "register_map",
        "TBBase": "tbbase"
}


# Compile a regex to capture the class/module name after 'from CocoTBFramework.TBClasses.'
# Example match: "from CocoTBFramework.TBClasses.tbbase"
# Group(1) would be "TBBase".
pattern = re.compile(r'(from\s+TBClasses\.)([A-Za-z0-9_]+)')

def replace_in_file(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()

    # Define a function used by re.sub() to handle each match
    def replacement_func(match):
        prefix = match.group(1)   # "from CocoTBFramework.TBClasses."
        old_str = match.group(2)  # e.g. "TBBase"

        # If old_str is in our map, replace it; otherwise, keep as-is
        new_str = old2new_map.get(old_str, old_str)
        return f'{prefix}{new_str}'

    new_content = pattern.sub(replacement_func, content)

    # Write changes back to file only if there are differences
    if new_content != content:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(new_content)

def main():
    for root, dirs, files in os.walk('./val/'):
        for filename in files:
            if filename.endswith('.py'):
                print(f"working on {filename}\n")
                file_path = os.path.join(root, filename)
                replace_in_file(file_path)

if __name__ == '__main__':
    main()

