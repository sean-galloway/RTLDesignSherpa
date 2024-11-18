# RTLDesignSherpa: Pioneering Insightful Approaches to Utilizing Open-Source Flows for Crafting High-Caliber Logic Competing with Industry Giants

Initially, this site was only a playground for me to do things I was told at work for years was impossible or above my pay grade. It has since morphed into an area where I want to help folks learn how to code synthesizable RTL using industry-standard flows and processes while using all free tools. Being in the industry for many years, I am very familiar with the flows and how to script and automate them. I am striving to have a set of RTL that is a jumping-off point for folks; they can adapt and change as they like. I also want a robust test or set of tests for each block or mega-block that folks can adjust if needed to their new code. Finally, I want to have all the flows (regression testing, lint, CDC, etc.) automated as it is in the industry so that folks will run them before their turn ins. I will likely write some GitHub hooks so that this happens automatically on turn-ins for me. Nothing is worse than figuring out a turn-in from ten turn-ins ago broke everything. Unwinding that mess is a nightmare.

## Here are a couple of notes for the folks who have been grabbing code.

Here are items I’ve recently done:

-Full documentation with UMLs for all the Python code, even code that wasn’t originally mine, but I hacked on a lot to add new features.
-Word-only documentation for the RTL blocks.
-A Cheat Sheet showing how to use the primary scripts, all in one place.
-Finished the divider, the last of the original batch of blocks I wanted to do and have folks see.
-Did a massive rewrite on vcd2wavedrom and added some valuable features, so automating wavedrom files from regression should be easy.
-I’ve figured out the issue with GitHub Pages; I have dummy content as proof of concept.

Here are the items that are coming next:

-Waveforms, walk-throughs, and block diagrams for all the RTL blocks by themselves
-Waveforms, walk-throughs, and block diagrams for all the CocoTB tests.
-I just found a terrific book on doing math with RTL (adder, subtractors, multipliers and dividers, all integer and floating point), so I might sink back into that rabbit hole again if there are many new blocks I want to add to the randomly chosen arithmetic blocks I have already created. I will likely want some select floating point versions as that is a big gap currently.
-I’ll make this more apparent when I document the CocoTB stuff. These are not my proudest moments. These are the kinds of tests one writes to check code when they have 5,000 lines of RTL that need to be ready at noon on Friday, and it’s 5 pm on Thursday, and you haven’t been able to start coding yet due to other commitments. You want to turn in your code but don’t want validation to find many stupid bugs. I love it when validation finds hard bugs when there are unexpected interactions between FSMs. However, it gets annoying when fixing a bug takes 1/100 of the time it takes to deal with Jira (or whatever bug tool is being used). Some folks wear super buggy code as a badge of honor. To them, it means what they are doing is hard. Many managers, Fellows, and VPs see it the same way. I have never been in that camp.
-Make the CocoTB tests less brittle. For some tests, the testbench breaks if the parameters change to a different but legal value. I’ve learned a lot more about CocoTB since then. This bothers me, and I’m super embarrassed about it.
-Once the documentation is clean, I’ll publish it to GitHub Pages. It’ll be the same content as in the repo, just in a prettier form.
-Get a Kanban-type page going on GitHub Pages. Once I have this, I can point to it in the README instead of listing stuff that maybe no one cares about.
-I want to publish how I did my Linux setup to help others save time.
-Create UVM versions of all the CocoTB tests. I want to learn more about UVM and use it in practice. UVM tests are the Gold Standard in the industry if used correctly.
-The next mega-task is starting on the FPro Book. This is where the real fun begins as we see our RTL work in silicon. Along with FPro examples, I’ll mix some of my own just for fun to see buttons break if we don’t de-bounce them, see how badly done async crossings can have weird behavior, etc.

To see the state of the current scripts documentation, check out this area: [Scripts Doc Index](docs/mark_down/Scripts/index.md)

To see the state of the current RTL documentation, check out this area: [RTL Doc Index](docs/mark_down/CommonRTL/index.md)

## Here is some quick info on my setup

- I mainly work in a VM Linux-Ubuntu shell on a Windows 11 machine. From what I have seen in the industry, one will spend most of their time in Linux. I have included my .aliases file that works in bash. I don't have much, but they have been battle-tested.

- Note: I have a dedicated VM for Verilog work with only the required tools. I tried using a shared environment with some of my data analysis work, but some tools conflicted, and I needed help finding a clean solution. I will create a YouTube video on making the VM and quickly install the minimal tools required to get you coding and linked to GitHub.

- Python 3.10, there is a requirements.txt included. This may evolve.

- VSCode is a tremendous free IDE for Python and Verilog. Since this is Verilog and Python-focused, I only use these Extensions. (If you use VSCode for other purposes, I will not recommend syncing your extensions. I saw conflicts where excellent RTL code was throwing lint errors.)

- Here are the extensions I use. These may evolve: ctags, GitLens, Makefile Tools, Pylance, Python, SystemVerilog0Language Support, TerosHDL, TODO Highlight, Verilog-HDL/SystemVerilog/BlueSpec SystemVerilog, Code Spell Checker, TerosHDL, Variable.

- Icarus Verilog; this is a nice free Verilog simulator. It outputs messages and a VCD file.

- GTKWave - this is very good at viewing VCD files. I will have at least one debug.gktw file for each CocoTB golden test to see the critical signals and how I've structured them.

- verible - for linting and style checking

- Within Python, here are the main usages:

- Automation where required. I use Python to automatically create a type of adder and some types of multipliers. I also use Python to run two lint tools on all the RTL directories and to test regressions. I'm an automation junkie, so there will likely be more of these to come.

- CocoTB- this links Python to Icarus Verilog runs. I have a makefile with each testbench. The commands I use are: make clean, then I just run make

- PyUVM- This is a port of the UVM standard from SystemVerilog to Python. Everyone in the industry uses UVM. I plan to have a robust UVM test bench for each block I design. I'm learning the UVM vernacular myself, so this is a process.

- PlantUML- I used this for all of the UML diagrams. The syntax is very clean, and I love that it is also hierarchical (one can include other files)

### Instructions to, hopefully, painlessly replicate my environment

- Get a virtual maching software (VMWare, or any other, I use Oracle VirtualBox)
-- The VM will need at least 4GB of memory and 20GB of disk space. More of each is always better
-- I use Ubuntu for the Linux image. The instructions below assume that. An LLM could probably adapt the instructions for other distribuitons.
-- In Linux, do these itmes (download and install or use the sudo commands):
    # Vscode:
    Install thru Ubuntu UI

    # Icarus:
    sudo apt-get install build-essential autoconf gpref flex bison
    sudo apt install iverilog

    # Verilator:
    sudo apt-get install verilator

    # Ctags:
    sudo snap install universal-ctags 
    Update the ctags path in the vscode preferences

    # Git:
    sudo apt install git

    # Vim:
    sudo apt install vim

    # Tkdiff:
    sudo apt install tkdiff

    # Make:
    sudo apt install make

    # GTKWave:
    sudo apt-get install gtkwave
    sudo apt-get install libcanberra-gtk-module libcanberra-gtk3-module

    # GraphViz (needed for PlantUML):
    sudo apt install graphviz

    # Java (needed for PlantUML):
    sudo apt install default-jre

    # Wavedrom-cli:
    sudo apt update
    sudo apt install nodejs npm
    sudo npm install -g wavedrom-cli

    # Ruby and Jekyll:
    sudo apt-get install ruby-full build-essential zlib1g-dev
    gem install jekyll bundler

    # Scala-CLI:
    curl -sSLf https://scala-cli.virtuslab.org/get | sh

    # Verible:
    download the latest version:
    Releases · chipsalliance/verible (github.com)
    tar xvzf verible-v0.0-3430-g060bde0f-Ubuntu-20.04-focal-x86_64.tar.gz 
    sudo mv  verible-v0.0-3430-g060bde0f /usr/bin/verible-v0.0-3430-g060bde0f/

-- Once all is installed, make a github directory, cd into it and clone the repo:
mkdir github
cd github
git clone https://github.com/sean-galloway/RTLDesignSherpa.git

you now need to create a virtual environment for python with something like this command:
cd into the RTLDesignSherpa area
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt

now you need to add the python dependencies that are local source this seperately or add it to the activate command:
source env_python

## Starter Reading List

For the designs in the rtl/common area the inspiration for the choices come mostlyu from these two books:

- Advanced FPGA Design by Steve Kilts
- Synthesis of Arithmetic Circuits by Deschamps, Bioul, Sutter

Note: all of my circuits are my own design or are based off of credited code. For the most part, my designs are an order of magnitude more complex than circuits in books like these. For example the CRC circuit from one of the books is very simple and will not work on any of the standards. The one I have is validated across about 300 standards. The adders, subtractors, multipliers and dividers are alos more complex and based on fairly recent research. However, I have never built these full-time for production. I am certain most any folks with ALU experience would laugh at how simplistic they are. I learned a lot building them, though.

Try code out and learn through experience. To test the RTL cd into the val/unit_common area and run this command:
pytest test_shifter_lfsr.py
to run all of the tests in one of the areas type:
pytest

All of the tests use the pytest and cocotb flows. There are many tutorials out there for these. If you look through my tests, you might find that they all follow the same formula. Try things out and have fun!

----------
