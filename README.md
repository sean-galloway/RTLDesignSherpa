# RTL_Design_Projects

A couple of notes for the folks that have been grabbing code. I am almost done with the basic common code; there are a few dividers left. I got sucked into the rabbit hole of adder and multipliers. Here are  the next few things on my list:

- Get an automated WaveDrom flow working. This will provide graphs for the GitHub pages documentation. I will need to perform pretty major surgery on the vcd2wavedrom script as I want to be able to group the signals. The grouping will come from tags in the debug.gtkw files.
- Figure out GitHub pages and how to incorporate WaveDrom. I know it can be done, I don't know how, though.
- Once I have GitHub pages up, I want to have one page that is a KanBan type page listing what is IP and what is coming up. This is more for myself than anything else.
- Document all open source tools used with links. This will take a bit.
- Document my homebrew tools.
- Document all or a major cross-section of the common blocks, including theory and waveforms.
- Start on the FPro Book
- When I'm bored go through the common tests and make them less "brittle." I was learning as I was going with cocotb. I eventually got my tests fairly robust. Most are very brittle and break if one changes any of the parameters in the RTL from what the golden test uses.

This Repo is intended to show the progress I make as I venture into experimenting with FPGA's and I also hope to instill in others industry standard (or maybe better) practices. My goal is to start folks off learning basic Python, SystemVerilog and the UVM methodology and slowly progress to designing their own RiscVI32 microprocessor, IO Sub-system, AMBA fabric, and possibly some Tensor Processing Units for inference experiments with the intent of loading this onto an appropriate FPGA. All of the code in the repo is considered to be a jumping-off point. I fully expect and encourage others to make the code their own; like make personal async fifo's and possibly do it better than mine. (If you do, I'll post it here and make sure you get the proper credit.)

My goal is to use all free tools in this project, but also prepare folks to work in the industry. These are the tools I am using (note this may get updated):

- I am working mostly in a VM Linux-Ubuntu shell on a Windows 11 machine. From what I have seen in the industry, one will spend most of their time in Linux. I have included my .aliases file that works in bash. I don't have a whole lot, but they have been battle-tested over the years.
  - Note: I have a dedicated VM for verilog work that has only the tools required. I tried using a shared environment with some of my data analysis work, but some tools conflicted, and I couldn't find a clean solution. I will create a YouTube video on making the VM and quickly install the minimal tools required to get you coding and linked to GitHub.
- Python 3.10, there is a requirements.txt included. This may evolve.
- VSCode is a tremendous free IDE for Python and Verilog. Since this is Verilog and Python-focused, I only use these Extensions. (if you use VSCode for other purposes, I would not recommend syncing your extensions. I saw conflicts where wonderful RTL code was throwing lint errors.)
  - Here are the extensions I use. These may evolve: ctags, GitLens, Makefile Tools, Pylance, Python, SystemVerilog0Language Support, TerosHDL, TODO Highlight, Verilog-HDL/SystemVerilog/BlueSpec SystemVerilog, Code Spell Checker, TerosHDL, Variable.
- Icarus verilog; this is a nice free verilog simulator. It outputs messages and a VCD file.
- GTKWave - this is very good at viewing the VCD files. I will try to have a debug.gktw file for each golden test so one can see the signals that I think are important and how I've structured them.
- verible - for linting and style checking
- Within Python, here are the main usages:
  - Automation where required. I use Python to automatically create a type of adder and some types of multipliers. I also use Python to run two lint tools on all of the RTL directories and to run test regressions. I'm an automation junky so, there will likely be more of these to come.
  - CocoTB- this links Python to Icarus Verilog runs. I have a makefile with each testbench. The commands I use are: make clean then I just run make
  - PyUVM- This is a port of the UVM standard from SystemVerilog to Python. Everyone in the industry uses UVM. I plan to have a robust UVM test bench for each block I design. I'm learning the UVM vernacular myself so, this is a process.
  - LogiSim- I'm using this in Windows. I will try to have a LogiSim version for each of the common files. It may get to be too much as the projects get more significant. I'm new to LogiSim, so this will be a process.
  - Draw.io- I'm using this in Windows. I plan to use this for the UML diagrams for the testbenches mostly. I'm used to Visio, so it will be a learning curve getting productive with this tool.
