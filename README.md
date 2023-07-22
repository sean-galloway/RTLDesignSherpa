# RTL_Design_Projects
This Repo is intended to show the progress I make as I venture into experimenting with FPGA's and  RTL Design experiments. I also hope to instill in others industry standard (or maybe better) practices. My goal is to start folks off learning basic Python, SystemVerilog and the UVM methodology and slowly progress to designing their own RiscVI32 microprocessor, IO Sub-system, AMBA fabric, and possibly some Tensor Processing Units for inference experiments with the intent of loading this onto an appropriate FPGA. All of the code in the repo is considered to be a jumping off point. I fully expect and encourage others to make the code their own; like make personal async fifo's and possibly do it better than mine. (If you do, I'll post it here and make sure you get the proper credit.)

My goal is to use all free tools in this project, but also prepare folks to work in the industry. These are the tools I am using (note, this may get updated):
- I am working most in in a VM Linux-Ubuntu shell on a Window 11 machine. From what I have seen in the industry one will spend most of their time in Linux. I have included my .aliases file that work in bash. I don't have a whole lot, but they have been battle tested over the years.
    - Note: I have a dedicated VM for verilog work that has only the tools required. I tried using a common environment with some of my data analysis work, but some tools conflicted and I couldn't find a clean solution. I will create a YouTube video on how to create the VM and quickly install the minimal set of tools required to get you coding and linked to GitHub.
- Python 3.10, there is a requirements.txt included. This may evolve over time.
- VSCode a great free IDE for Python and Verilog. Since this is Verilog and Python focused, I only use these Extensions (if you use VSCode for other purposes, I would not recommend sync'ing your extensions. I saw conflicts where perfectly fine RTL code was throwing lint errors.)
    - Here are the extensions I use, these may evolve over time: ctags, GitLens, Makefile Tools, Pylance, Python, SystemVerilog0Language Support, TerosHDL, TODO Highlight, Verilog-HDL/SystemVerilog/BlueSpec SystemVerilog, Code Spell Checker.
- Icarus verilog; this is a nice free verilog simulator. It outputs messages and a vcd file.
- GTKWave - this is very good at viewing the vcd files. I will try to have a <block_name>.gktw file for each testbench so one can see the signals that I think are important and how I've structured them.
- Within Python here are the main usages:
    - Automation where required. I haven't used it yet, but I'm sure I will.
    - CocoTB- this links Python to Icarus verilog runs. I have a makefile with each testbench. The commands I use are: make clean then I just run make
    - PyUVM, this is a port of the UVM standard from SystemVerilog to Python. Everyone in the industry uses UVM. I plan to have a robust UVM Testbench for each block that I design. I'm learning the UVM vernacular myself so, this is a process.
    - LogiSim- I'm using this in Windows. I will try to have a LogiSim version for each of the common files. It may get to be too much as the projects get bigger. I'm new to LogiSim, so this will be a process.
    - Draw.io- I'm using this in windows. I plan to mostly use this for the UML diagrams for the testbenches. I'm used to Visio, so it will be a learning curve getting productive with this tool.

