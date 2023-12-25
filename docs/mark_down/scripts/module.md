# module

The `module.py` file is a Python class that facilitates the construction of Verilog module templates. It allows users to programmatically define modules with parameters, input and output ports, wires, and other Verilog constructs.

![Module UML](../../images_scripts_uml/verilog_Module.svg)

## Class: Module

```python
class Module(object):
    def __init__(self, module_name='', instance_name=''):
        # Initialization of module attributes and collections
```

### Properties

- `module_name`: A string to hold the name of the Verilog module.
- `instance_name`: A string to hold the instance name within the module.
- `params`: An instance of `Param` class to manage module parameters.
- `ports`: An instance of `Signal` class to manage module ports.
- `wires`: A list to hold wires and their types.

### Methods

#### `add_port_string(ports: str)`

Adds the string representation of ports to the module.

#### `wire(name, _type)`

Defines a wire within the module.

#### `start()`

Begins the definition of a Verilog module by generating the appropriate timescale and parameter configurations.

#### `end()`

Terminates the Verilog module definition with `endmodule`.

#### `stmt_assign(lhs, rhs)`

Creates an assignment statement in Verilog syntax.

#### `instruction(instruction)`

Appends a raw instruction to the module body.

#### `comment(c)`

Adds a comment line within the module.

#### `write(file_path, filename)`

Writes the module to a Verilog file at `file_path/filename`.

#### `__str__()`

Returns a string representation of the instructions.

#### `instantiate(instance_name, inputs, outputs)`

Generates an instantiation of the defined module with provided inputs and outputs.

#### Static Methods

##### `in_connector(port, connector)`

Creates a dictionary that represents an input connector.

##### `out_connector(port, connector)`

Creates a dictionary that represents an output connector.

## Dependency Files

- `signal.py`: Includes the `Signal` class used to represent Verilog signals such as ports.
- `param.py`: Includes the `Param` class used for handling Verilog parameters.

To generate a Verilog module using `Module` class, you should first create an instance of the class, configure its parameters, ports, and wires using the provided methods, and then write to a file or instantiate as needed.

```python
# Example Usage
module_instance = Module('my_module')
module_instance.add_port_string('input clk, input rst')
module_instance.wire('internal_sig', 'logic')
module_instance.start()
module_instance.stmt_assign('output_sig', 'internal_sig')
module_instance.end()
module_instance.write('./', 'my_module.v')
```

This example will generate a Verilog file `my_module.v` with a module that includes an input clock, reset signal, an internal signal, and an output signal assigned from the internal signal.

Keep in mind that this class does not check the syntax or semantic correctness of the Verilog code being generated. The user is responsible for ensuring that the constructed module is valid and synthesizable according to Verilog standards.

---

[Back to Scripts Index](index.md)
