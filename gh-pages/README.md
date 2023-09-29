# RTL_Design_Projects

A couple notes for the folks that have been grabbing code. I am almost done with the basic common code; there are a few dividers left. I got sucked into the rabbit hole of adder and multipliers. Here are  the next few things on my list:
- Get an automated WaveDrom flow working. This will provide graphs for the GitHub pages documentation. I will need to perform pretty major surgery on the vcd2wavedrom script as I want to be able to group the signals. The grouping will come from tags in the debug.gtkw files.
- Figure out GitHub pages and how to incorporate WaveDrom. I know it can be done, I don't know how, though.
- Once I have GitHub pages up, I want to have one page that is a KanBan type page listing what is IP and what is coming up. This is more for myself than anything else.
- Document all open source tools used with links. This will take a bit.
- Document my homebrew tools.
- Document all or a major cross-section of the common blocks, including theory and waveforms.
- Start on the FPro Book
- When I'm bored go through the common tests and make them less "brittle." I was learning as I was going with cocotb. I eventually got my tests fairly robust. Most are very brittle and break if one changes any of the parameters in the RTL from what the golden test uses.

This Repo is intended to show the progress I make as I venture into experimenting with FPGA's and  RTL Design experiments. I also hope to instill in others industry standard (or maybe better) practices. My goal is to start folks off learning basic Python, SystemVerilog and the UVM methodology and slowly progress to designing their own RiscVI32 microprocessor, IO Sub-system, AMBA fabric, and possibly some Tensor Processing Units for inference experiments with the intent of loading this onto an appropriate FPGA. All of the code in the repo is considered to be a jumping off point. I fully expect and encourage others to make the code their own; like make personal async fifo's and possibly do it better than mine. (If you do, I'll post it here and make sure you get the proper credit.)

My goal is to use all free tools in this project, but also prepare folks to work in the industry. These are the tools I am using (note, this may get updated):
- I am working most in in a VM Linux-Ubuntu shell on a Window 11 machine. From what I have seen in the industry one will spend most of their time in Linux. I have included my .aliases file that work in bash. I don't have a whole lot, but they have been battle tested over the years.
    - Note: I have a dedicated VM for verilog work that has only the tools required. I tried using a common environment with some of my data analysis work, but some tools conflicted and I couldn't find a clean solution. I will create a YouTube video on how to create the VM and quickly install the minimal set of tools required to get you coding and linked to GitHub.
- Python 3.10, there is a requirements.txt included. This may evolve over time.
- VSCode a great free IDE for Python and Verilog. Since this is Verilog and Python focused, I only use these Extensions (if you use VSCode for other purposes, I would not recommend sync'ing your extensions. I saw conflicts where perfectly fine RTL code was throwing lint errors.)
    - Here are the extensions I use, these may evolve over time: ctags, GitLens, Makefile Tools, Pylance, Python, SystemVerilog0Language Support, TerosHDL, TODO Highlight, Verilog-HDL/SystemVerilog/BlueSpec SystemVerilog, Code Spell Checker.
- Icarus verilog; this is a nice free verilog simulator. It outputs messages and a vcd file.
- GTKWave - this is very good at viewing the vcd files. I will try to have a <block_name>.gktw file for each testbench so one can see the signals that I think are important and how I've structured them.
- verible - for linting and style checking
- Within Python here are the main usages:
    - Automation where required. I haven't used it yet, but I'm sure I will.
    - CocoTB- this links Python to Icarus verilog runs. I have a makefile with each testbench. The commands I use are: make clean then I just run make
    - PyUVM, this is a port of the UVM standard from SystemVerilog to Python. Everyone in the industry uses UVM. I plan to have a robust UVM Testbench for each block that I design. I'm learning the UVM vernacular myself so, this is a process.
    - LogiSim- I'm using this in Windows. I will try to have a LogiSim version for each of the common files. It may get to be too much as the projects get bigger. I'm new to LogiSim, so this will be a process.
    - Draw.io- I'm using this in windows. I plan to mostly use this for the UML diagrams for the testbenches. I'm used to Visio, so it will be a learning curve getting productive with this tool.

# Style Guide
This is not the place for this, but I am documenting it for myself while I sort out the various documentation resources. These rules are short and simple to keep them easy to be adhered to Note: some naming convention documents are 30+ pages long. For this forum, I want to keep it simple. You can follow (or not) if you like. Be aware some of the tools that I have developed key off of the naming convention.
- Module names are snake case
- Signal names a snake case
- Parameter names are all caps
- Input ports all begin with i_ or iw_. It is assumed all inputs come directly from flops. In the rare cases where that does not occur, the iw_ signifier is used (w meaning wire.)
- Output ports all begin with o_ or ow_. It is assumed all outputs come directly from flops. In the rare cases where that does not occur, the ow_ signifier is used (w meaning wire.)
- All register signals (flops) start with r_.
- All wire signals start with w_.
Note: I was not going to have a strict naming convention. I started exploring automation to create wavedrom diagrams from the existing vcd and gktw files. I want to put a phase of 0.2 on flopped signals (to represent tCO), and 0.8 on wire signals to show artificially large propagation delays. Without the naming convention, none of this can be automated by one person working on a side project like this.

