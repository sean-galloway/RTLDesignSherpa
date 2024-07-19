The file bch.vht is used by bch.exe 
and should not be changed by hand
To change BCH code (n,k) change file bch.in
This file contains data for enc.vhd and for bch.vhd 

Data for sim.txt 
#
Help text file for bch.exe program that generate binary (n,k) BCH code.

bch.exe program uses following input files:
bch.in - to specify input parameters of BCH code, only this file 
	should be changed (if the bch.exe cannot find bch.in file then
	it requests the user to type BCH code and program parameters
bch.vht - data needed to generate enc.vhd and sim.vhd and sim.txt files
bch1.vht - data needed to generate dec.vhd if t (no. of errors) = 1
bch2.vht - data needed to generate dec.vhd if t = 2
bch3.vht - data needed to generate dec.vhd if t > 2
bchs.vht - data needed to generate sym.cmd and sym.cme

bch.exe generates (overwrites !!!) following files:
const.vhd - VHDL package file that contains useful constants
enc.vhd - VHDL file for generating BCH code encoder
dec.vhd - VHDL file for generating BCH code decoder
sim.vhd - VHDL file for generating file for simulation encoder and decoder
sim.cmd - command file for simulation before synthesis
sim.cme - command file for simulation after synthesis

bch.in file should consists of following:
m= xx - specify width of Galois Field GF(2^m), n=2^m-1
t= xx - specify number of errors to be may corrected
program option (placed in bch.in):
-oxx - for t>2 circuit option;
	xx = 2 - parallel architecture
	xx = 3 - serial architecture - preferred.
-sxx - generate sym.cmd and sym.cme with specified 
	by xx simulation time (number of codewords to simulate)
	xx=0 - do not generate simulation command files.
-ix - xx - interleave number. The frequency of Berlekamp-Massey 
	Algorithm in comparison to data transfer (syndrome calculation) frequency.
	f_BMA = interleave * f_syn
-mxx - design optimization by extracting
	xx= 0 -  without optimisation
	xx= 1,2... - with optimization - introduce a new intermediate
		signal only if it reduces the number of XOR at least by xx


#
---------------------------------------------------------------------
Data for const.vhd
#-- Constant necessary for decoder and encoder

PACKAGE   const IS
	CONSTANT m: INTEGER:= #;
	CONSTANT n: INTEGER:= #;  -- n= 2^m -1  -size of block
	CONSTANT k: INTEGER:= #;  -- BCH code (n,k) -no. of information bits
	CONSTANT nk: INTEGER:= #; -- nk=n-k
	CONSTANT t: INTEGER:= #;  -- no. of errors to be corrected

	CONSTANT sizea: INTEGER:= #; -- size of counter ca
	CONSTANT sizeb: INTEGER:= #; -- size of counter cb 
		-- count = iteration* cb + ca
	CONSTANT sizel: INTEGER:= #; 
		-- size of l integer (degree of error polynomial BMA)
END const;	

# 



Data for encoder
#-------------------------------------------------------------------------
-- File enc.vhd consists following entities: enc, ering, ecount
--------------------------------------------------------------------------

-- LFSR for encoder
	USE WORK.const.ALL;
ENTITY ering IS
PORT (clk, rll, din: IN BIT;
	dout: OUT BIT); --output serial data
END ering;

ARCHITECTURE eringa OF ering IS
	SIGNAL rin, rout: BIT_VECTOR(0 TO nk-1); -- ring register
	SIGNAL rin0: BIT;
  BEGIN
	dout<= rout(nk-1); 
 	rin0 <= (din XOR rout(nk-1)) AND rll;	

	rin(0)<= rin0;
#
  PROCESS BEGIN 
	WAIT UNTIL clk'EVENT AND clk='1';
	rout<= rin;
  END PROCESS;
END eringa;
--------------------------------------------------------------------------
-- COUNTER MODULO n FOR ENCODER BCH CODE (n,k)  
--  rll-ring loop lock - control signal for LFSR

	USE WORK.const.ALL;
ENTITY ecount IS
PORT (clk, reset: IN BIT;
	vdin: OUT BIT);  
END ecount;

ARCHITECTURE ecounta OF ecount IS
	SIGNAL cout: BIT_VECTOR(0 TO m-1); -- cout in GF(2^m); cout= L^count 
	SIGNAL vdinR, vdinS, vdin1: BIT;
BEGIN
	vdinR<=#; 
		-- reset vdin if cout==k-1
	vdinS<= (#) OR reset; 
		-- vdinS=1 if cout==n-1
	vdin<= vdin1 AND NOT reset;

  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	IF vdinR='1' THEN
		vdin1<= '0';
	ELSIF vdinS='1' THEN
		vdin1<= '1';
	END IF;
  END PROCESS;	

  PROCESS BEGIN -- increment or reset cout in ring, cout=L^count
	WAIT UNTIL clk'EVENT AND clk='1';
	cout(0)<= cout(m-1) OR reset;
#  END PROCESS;
END ecounta;

-----------------------------------------------------------------
--		ENCODER

	USE WORK.const.ALL;
ENTITY enc IS
PORT (clk, reset, din: IN BIT; 
	vdin, dout: OUT BIT); --output serial data
END enc;  -- vdin - valid data in - to enable external data shifting

ARCHITECTURE enca OF enc IS
	SIGNAL vdin1, rin, rout, rll: BIT; 
		-- rll-ring loop lock, pe-parallel enable din

	COMPONENT ecount --counter encoder
		PORT(clk, reset: IN BIT; vdin: OUT BIT); 
		END COMPONENT;
		FOR ALL: ecount USE ENTITY WORK.ecount (ecounta);
	COMPONENT ering --ring for encoder
		PORT(clk, rll,  din: IN BIT; dout: OUT BIT); 
		END COMPONENT;
		FOR ALL: ering USE ENTITY WORK.ering (eringa);
  BEGIN
	c1: ecount
		PORT MAP (clk, reset, vdin1);
	r1: ering
		PORT MAP (clk, rll, rin, rout);
	rin<= din AND NOT reset;
	rll<= vdin1 AND NOT reset;
	vdin<= vdin1;

  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	dout<= (NOT vdin1 AND rout) OR (vdin1 AND rin);
  END PROCESS;
END enca;
#




------------------------------------------------------------------------
------------------------------------------------------------------------
the data for generating file SIM.VHD

#-- The simulation file - encoder & decoder & error generating circuit
-- for enc.vhd and dec.vhd files.

	-- buffer for encoder data in
	USE WORK.const.ALL;
ENTITY encBuf IS
PORT(clk, pe: IN BIT;
	din: IN BIT_VECTOR(0 TO k-1); 
	dout: OUT BIT);
END encBuf;

ARCHITECTURE encBufa OF encBuf IS
	SIGNAL buf: BIT_VECTOR(0 TO k-1);
  BEGIN
	dout<= buf(k-1);	
  PROCESS BEGIN 
	WAIT UNTIL clk'EVENT AND clk='1';
	IF pe='1' THEN
		buf<= din;
	ELSE
		buf<= '0' & buf(0 TO k-2); 	
	END IF;
  END PROCESS;
END encBufa;
-----------------------------------------------------------------------------------

	-- buffer for error - corrupting transmitted data
	USE WORK.const.ALL;
ENTITY errBuf IS
PORT(clk, pe: IN BIT;
	din: IN BIT_VECTOR(0 TO n-1); 
	dout: OUT BIT);
END errBuf;

ARCHITECTURE errBufa OF errBuf IS
	SIGNAL buf: BIT_VECTOR(0 TO n-1);
  BEGIN
	dout<= buf(n-1);	
  PROCESS BEGIN 
	WAIT UNTIL clk'EVENT AND clk='1';
	IF pe='1' THEN
		buf<= din;
	ELSE
		buf<= '0' & buf(0 TO n-2); 	
	END IF;
  END PROCESS;
END errBufa;
-----------------------------------------------------------------------------------

	-- buffer for comparing data before the encoder with data after the decoder
	USE WORK.const.ALL;
ENTITY comBuf IS
PORT(clk, din: IN BIT; 
	dout: OUT BIT);
END comBuf;

ARCHITECTURE comBufa OF comBuf IS
	CONSTANT bufSize: INTEGER:= #;  
	SIGNAL buf: BIT_VECTOR(0 TO bufSize-1);
  BEGIN
	dout<= buf(bufSize-1);	
  PROCESS BEGIN 
	WAIT UNTIL clk'EVENT AND clk='1';
	buf<= din & buf(0 TO bufSize-2);
  END PROCESS;
END comBufa;

-----------------------------------------------------------------------------------

	-- buffer for storing decoder output data
	USE WORK.const.ALL;
ENTITY decBuf IS
PORT(clk, ce, din: IN BIT; 
	dout: OUT BIT_VECTOR(0 TO k-1));
END decBuf;

ARCHITECTURE decBufa OF decBuf IS  
	SIGNAL buf: BIT_VECTOR(0 TO k-1);
  BEGIN
	dout<= buf;	
  PROCESS BEGIN 
	WAIT UNTIL clk'EVENT AND clk='1';
	IF ce='1' THEN
		buf<= din & buf(0 TO k-2);
	ELSE
		buf<= buf;
	END IF;
  END PROCESS;
END decBufa;

-----------------------------------------------------------------------------------

	USE WORK.const.ALL;
ENTITY sim IS
PORT(clk, reset: IN BIT;
	din: IN BIT_VECTOR(0 TO k-1); 
	error: IN BIT_VECTOR(0 TO n-1);
	vdin, vdout, wrongNow, wrong: OUT BIT; 
	-- if wrong=1 - the circuit does not work properly 
	dout: OUT BIT_VECTOR(0 TO k-1));
END sim;

ARCHITECTURE sima OF sim IS 
	SIGNAL encIn, encOut, decIn, err, decOut: BIT; 
	SIGNAL vdin1, vdout1, encBPe, encBOut, comBOut: BIT; 
		-- valid din, dout - enable shifting data
	SIGNAL wrongIn, vdinPrev, vdin0_1, resetDec, clkEnc: BIT;

  	COMPONENT enc			
		PORT(clk, reset, din: IN BIT;
			vdin, dout: OUT BIT); 
		END COMPONENT;
		FOR ALL : enc USE ENTITY WORK.enc (enca);
	COMPONENT dec
		PORT(clk, reset, din: IN BIT;
			vdout, dout: OUT BIT); 
		END COMPONENT;
		FOR ALL : dec USE ENTITY WORK.dec (deca); 
	COMPONENT encBuf
		PORT(clk, pe: IN BIT; din: IN BIT_VECTOR(0 TO k-1); 
			dout: OUT BIT);
		END COMPONENT;
		FOR ALL : encBuf USE ENTITY WORK.encBuf (encBufa); 
	COMPONENT errBuf
		PORT(clk, pe: IN BIT; din: IN BIT_VECTOR(0 TO n-1); 
			dout: OUT BIT);
		END COMPONENT;
		FOR ALL : errBuf USE ENTITY WORK.errBuf (errBufa); 
	COMPONENT comBuf
		PORT(clk, din: IN BIT; dout: OUT BIT);
		END COMPONENT;
		FOR ALL : comBuf USE ENTITY WORK.comBuf (comBufa); 
	COMPONENT decBuf
		PORT(clk, ce, din: IN BIT; dout: OUT BIT_VECTOR(0 TO k-1));
		END COMPONENT;
		FOR ALL : decBuf USE ENTITY WORK.decBuf (decBufa);
#5	COMPONENT dci  -- interleave counter
		PORT (clk, reset: IN BIT; dout: OUT BIT); -- dout=1 if count=0
		END COMPONENT; 
	  	FOR ALL: dci USE ENTITY WORK.dci (dcia);
	SIGNAL clkEncEn: BIT;
#0	
  BEGIN
   	e1: enc
		PORT MAP (clkEnc, reset, encIn, vdin1, encOut);
	d1: dec
		PORT MAP (clk, resetDec, decIn, vdout1, decOut);

	encBPe<= NOT vdin1;
	encB: encBuf
		PORT MAP (clkEnc, encBPe, din, encBOut);
	encIn<= encBOut AND NOT reset;
	vdin0_1<= (NOT vdinPrev AND vdin1) OR reset;
	errB: errBuf
		PORT MAP (clkEnc, vdin0_1, error, err);
	comB: comBuf
		PORT MAP (clkEnc, encIn, comBOut);
	decB: decBuf
		PORT MAP (clk, vdout1, decOut, dout);

	decIn<= (encOut XOR err) AND NOT reset; -- corrupting transmitted data

#5	ci: dci  -- interleave counter
		PORT MAP (clk, reset, clkEncEn);
	clkEnc<= clkEncEn AND NOT clk;
#6	clkEnc<= clk;
#0		
	wrongIn<=  (decOut XOR comBOut) AND NOT reset AND vdout1; 
	vdout<= vdout1;
	vdin<= vdin1;
	

  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	-- wrong ones set always 1
	IF reset='1' THEN
		wrong<= '0';
	ELSIF wrongIn='1' THEN
		wrong<= '1';
	END IF;
	wrongNow<= wrongIn;
	resetDec<= reset;
  END PROCESS;

  PROCESS BEGIN
	WAIT UNTIL clkEnc'EVENT AND clkEnc='1';
	vdinPrev<= vdin1;
  END PROCESS;
END sima;

#-------
