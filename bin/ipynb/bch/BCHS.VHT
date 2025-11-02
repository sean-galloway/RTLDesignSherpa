The file bchs.dat is used by bch.exe program.
for generating files: bch.cmd and bch.cme. 

In the place, where there is character '#', some data will be inserted
and the rest of file will be only coped by the program.

sim.cmd for symulation before synthesis
--------------------------------------------------------------------
#restart

wfm /clk @0 = 1 (50ns=0 50ns=1)*#

wfm /reset @0 = 1 + 
@220ns = 0

wfm /error @0 = #



wfm /din @0 = #

 

wave sim.wfm /wrong /wrongNow /vdout

run
#

sim.cme for symulating bch.vhd after synthesis 
---------------------------------------------------------------
#restart 

vector din din[0:#] 
radix bin din 

vector error error[0:#] 
radix bin error 

vector dout dout[0:#] 
radix bin dout 

wfm clk @0 = 1 (50ns=0 50ns=1)*#

wfm error @0 = #
 
wfm din @0 = #

wfm reset @0 = 1 + 
@#20ns = 0

wave sim.wfm  wrong wrongNow vdout reset

run
