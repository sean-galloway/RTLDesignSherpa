The file bch1.vht is used by bch.exe program
and should not be changed by hand.
To change BCH code (n,k) change file bch.in
This file contains data for enc and for 1 error correcting dec 

Data for one error correcting decoder (Hamming code)

#-------------------------------------------------------------
-- counter modulo n

	USE WORK.const.ALL;
ENTITY dcount IS
PORT (clk, reset: IN BIT; 
	pe, vdout, vdout1: OUT BIT);
END dcount;

ARCHITECTURE dcounta OF dcount IS	
	SIGNAL cout: BIT_VECTOR(0 TO m-1);
	SIGNAL vdout11, vdoutS, vdoutR, nFirst: BIT;
  BEGIN
	pe<= #;
		-- pe=1 if count=0
	vdoutS<= nFirst AND (#);
		-- vdout=1 if count=1
	vdoutR<= reset OR (#);
		-- vdout=1 if count=k+1
	vdout1<= vdout11;

  PROCESS BEGIN -- increment or reset cout in ring, cout=L^count
	WAIT UNTIL clk'EVENT AND clk='1';
	IF reset='1' THEN
		nFirst<= '0';
	ELSIF vdoutR='1' THEN
		nFirst<= '1';
	END IF;

	IF vdoutR='1' THEN
		vdout11<= '0';
	ELSIF vdoutS='1' THEN
		vdout11<= '1';
	END IF;
	vdout<= vdout11; -- delay by one clock

	cout(0)<= cout(m-1) OR reset;
#  END PROCESS;
END dcounta;

----------------------------------------------------------------------------
--	syndrome circuit
#
----------------------------------------------------------------------------
--	Chien's searching circuit
#
----------------------------------------------------------------------
-- circuit for storing data to be corrected or already corrected

	USE WORK.const.ALL;
ENTITY dbuf IS
PORT (clk, err, vdout, din: IN BIT;
	dout: OUT BIT); 
END dbuf;

ARCHITECTURE dbufa OF dbuf IS
	SIGNAL buf: BIT_VECTOR(0 TO n+1); 
	-- siso shift registers for storing data to be corrected
  BEGIN
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	buf<= din & buf(0 TO n);
	dout<= (buf(n+1) XOR err) AND vdout;
  END PROCESS;
END dbufa;

----------------------------------------------------------------------
--		decoder for one error (hamming code)
--		DECODER HAMMING CODE

	USE WORK.const.ALL;
ENTITY dec IS
PORT (clk, reset, din: IN BIT; 
	vdout, dout: OUT BIT); 
END dec;

ARCHITECTURE deca OF dec IS
	SIGNAL  pe, err, vdout1, din_reset: BIT;
	--pe -parallel enable syn->ch;  er - correct error,
	--vdout - valid data out - remember data register 
	SIGNAL syn1, ch1, ch_and: BIT_VECTOR(0 TO m-1);

	COMPONENT dcount -- counter decoder 
		PORT(clk, reset: IN BIT; pe, vdout, vdout1: OUT BIT); 
		END COMPONENT;
		FOR ALL: dcount USE ENTITY WORK.dcount (dcounta);
	COMPONENT dsyn1 -- syndrome calculating circuit 
		PORT (clk, pe, din: IN BIT;
			dout1: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
		FOR ALL: dsyn1 USE ENTITY WORK.dsyn1 (dsyn1a);
	COMPONENT dch1 -- error finding circuit (Chien's ring)
		PORT (clk, pe: IN BIT; 
			din: BIT_VECTOR(0 TO m-1);
			dout: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
		FOR ALL: dch1 USE ENTITY WORK.dch1 (dch1a);
	COMPONENT dbuf -- buffer shift registers 
		PORT (clk, err, vdout, din: IN BIT; 
			dout: OUT BIT); 
		END COMPONENT;
		FOR ALL: dbuf USE ENTITY WORK.dbuf (dbufa);
  BEGIN
	count: dcount
		PORT MAP (clk, reset, pe, vdout, vdout1);
	s1: dsyn1
		PORT MAP (clk, pe, din_reset, syn1);
	h1: dch1
		PORT MAP (clk, pe, syn1, ch1);	
	b1: dbuf
		PORT MAP (clk, err, vdout1, din_reset, dout);

	din_reset<= din AND NOT reset;
	err<= ch_and(m-1);
		-- err<= not ch1(0) and ch1(1) and ch1(2) and ...	
	ch_and(0)<= ch1(0);
	gen:
	FOR i IN 1 TO m-1 GENERATE
	  ch_and(i)<= ch_and(i-1) AND NOT ch1(i);
	END GENERATE;
END deca;
