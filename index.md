---
title: RTL Design Sherpa
layout: home
description: RTL Design Sherpa is your ultimate guide to mastering Register Transfer Level (RTL) design. Explore expert tutorials, insightful articles, and practical tips to elevate your skills in digital circuit design and hardware engineering.
keywords: RTL design, Register Transfer Level, Digital circuit design, Hardware engineering, FPGA (Field-Programmable Gate Array), ASIC (Application-Specific Integrated Circuit), Verilog, VHDL (VHSIC Hardware Description Language), Hardware description languages, Synthesis, Synthesis, Timing analysis, RTL simulation, Design verification, Hardware architecture
---

# RTLDesignSherpa: Pioneering Insightful Approaches to Utilizing Open-Source Flows for Crafting High-Caliber Logic Competing with Industry Giants

<br>
<br>
Initially, this site was only a playground for me to do things I was told at work for years was impossible or above my pay grade. It has since morphed into an area where I want to help folks learn how to code synthesizable RTL using industry-standard flows and processes while using all free tools. Being in the industry for many years, I am very familiar with the flows and how to script and automate them. I am striving to have a set of RTL that is a jumping-off point for folks; they can adapt and change as they like. I also want a robust test or set of tests for each block or mega-block that folks can adjust if needed to their new code. Finally, I want to have all the flows (regression testing, lint, CDC, etc.) automated as it is in the industry so that folks will run them before their turn ins. I will likely write some GitHub hooks so that this happens automatically on turn-ins for me. Nothing is worse than figuring out a turn-in from ten turn-ins ago broke everything. Unwinding that mess is a nightmare.

## Here are a couple of notes for the folks who have been grabbing code.

Here are items I’ve recently done:

- Full documentation with UMLs for all the Python code, even code that wasn’t originally mine, but I hacked on a lot to add new features.
- Word-only documentation for the RTL blocks.
- A Cheat Sheet showing how to use the primary scripts, all in one place.
- Finished the divider, the last of the original batch of blocks I wanted to do and have folks see.
- Did a massive rewrite on vcd2wavedrom and added some valuable features, so automating wavedrom files from regression should be easy.
- I’ve figured out the issue with GitHub Pages; I have dummy content as proof of concept.

Here are the items that are coming next:

- Waveforms, walk-throughs, and block diagrams for all the RTL blocks by themselves
- Waveforms, walk-throughs, and block diagrams for all the CocoTB tests.
- I just found a terrific book on doing math with RTL (adder, subtractors, multipliers and dividers, all integer and floating point), so I might sink back into that rabbit hole again if there are many new blocks I want to add to the randomly chosen arithmetic blocks I have already created. I will likely want some select floating point versions as that is a big gap currently.
- I’ll make this more apparent when I document the CocoTB stuff. These are not my proudest moments. These are the kinds of tests one writes to check code when they have 5,000 lines of RTL that need to be ready at noon on Friday, and it’s 5 pm on Thursday, and you haven’t been able to start coding yet due to other commitments. You want to turn in your code but don’t want validation to find many stupid bugs. I love it when validation finds hard bugs when there are unexpected interactions between FSMs. However, it gets annoying when fixing a bug takes 1/100 of the time it takes to deal with Jira (or whatever bug tool is being used). Some folks wear super buggy code as a badge of honor. To them, it means what they are doing is hard. Many managers, Fellows, and VPs see it the same way. I have never been in that camp.
- Make the CocoTB tests less brittle. For some tests, the testbench breaks if the parameters change to a different but legal value. I’ve learned a lot more about CocoTB since then. This bothers me, and I’m super embarrassed about it.
- Once the documentation is clean, I’ll publish it to GitHub Pages. It’ll be the same content as in the repo, just in a prettier form.
- Get a Kanban-type page going on GitHub Pages. Once I have this, I can point to it in the README instead of listing stuff that maybe no one cares about.
- I want to publish how I did my Linux setup to help others save time.
- Create UVM versions of all the CocoTB tests. I want to learn more about UVM and use it in practice. UVM tests are the Gold Standard in the industry if used correctly.
- The next mega-task is starting on the FPro Book. This is where the real fun begins as we see our RTL work in silicon. Along with FPro examples, I’ll mix some of my own just for fun to see buttons break if we don’t de-bounce them, see how badly done async crossings can have weird behavior, etc.

To see the state of the current scripts documentation, check out this area: [Scripts Doc Index](file:///C:\Users\Sean%20Galloway\OneDrive\Documents\rtldesignsherpa_mark_down\docs\mark_down\scripts\index.md)

To see the state of the current RTL documentation, check out this area: [RTL Doc Index](file:///C:\Users\Sean%20Galloway\OneDrive\Documents\rtldesignsherpa_mark_down\docs\mark_down\rtl\index.md)

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

- Draw.io- I'm using this in Windows. I plan to use this for the UML diagrams for the testbenches mostly. I'm used to Visio, so getting productive with this tool will be a learning curve.
