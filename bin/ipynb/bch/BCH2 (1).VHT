The file bch2.vht is used by bch.exe program
and should not be changed by hand.
To change BCH code (n,k) change file bch.in
This file contains data for 2 errors correcting decoder 

#-------------------------------------------------------------------

ENTITY ffce IS
PORT (clk, ce, din: IN BIT; -- ce- clock enable
	dout: OUT BIT); --output serial data
END ffce;

ARCHITECTURE ffcea OF ffce IS
	SIGNAL q: BIT;
  BEGIN
	dout<= q;
  PROCESS BEGIN 
	WAIT UNTIL clk'EVENT AND clk='1';
	IF ce='1' THEN
	  q<= din;
	ELSE
	  q<= q;
	END IF;
  END PROCESS;
END ffcea;	

-------------------------------------------------------------------
-- counter modulo n

	USE WORK.const.ALL;
ENTITY dcount IS
PORT (clk, reset: IN BIT; 
	cef, pe, vdout, vdout1: OUT BIT);
END dcount;

ARCHITECTURE dcounta OF dcount IS	
	SIGNAL cout: BIT_VECTOR(0 TO m-1);
	SIGNAL vdout11, vdoutS, vdoutR, nFirst, cef1: BIT;
  BEGIN
	pe<= #;
		-- pe=1 if count=0
	cef1<= #;
		-- cef=1 if count= 1;
	cef<= cef1;
	vdoutS<= nFirst AND cef1;
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

---------------------------------------------------------------------
-- buffer circuit

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
---------------------------------------------------------------------------
-- Syndromes calculation circuits
#

-----------------------------------------------------------------
-- dout<= din^3

	USE WORK.const.ALL;
ENTITY dpow3 IS
PORT (din: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1));
END dpow3;

ARCHITECTURE dpow3a OF dpow3 IS
#	
END dpow3a;

---------------------------------------------------------------------------
-- compare if equal = dout<= ((syn1)^3 == syn3) 

	USE WORK.const.ALL;
ENTITY deq IS
PORT (syn1, syn3: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT);
END deq;

ARCHITECTURE deqa OF deq IS
	SIGNAL neq_or: BIT_VECTOR(0 TO m-1);
	SIGNAL power: BIT_VECTOR(0 TO m-1); -- power =(syn1)^3	
		-- power 3 circuit
	COMPONENT dpow3 -- dout<= din^3
		PORT (din: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
		FOR ALL: dpow3 USE ENTITY WORK.dpow3 (dpow3a);
  BEGIN
	p1: dpow3
		PORT MAP(syn1, power);
	dout<= neq_or(m-1);
	neq_or(0)<= syn3(0) XOR power(0);
	gen:
	FOR i IN 1 TO m-1 GENERATE
		neq_or(i)<= neq_or(i-1) OR (syn3(i) XOR power(i)); 
	END GENERATE;	
END deqa;

---------------------------------------------------------------------------
-- Chien search circuit
#
---------------------------------------------------------------------------
-- decoder circuit
	USE WORK.const.ALL;
ENTITY dec IS
PORT (clk, reset, din: IN BIT; 
	vdout, dout: OUT BIT); 
END dec;

ARCHITECTURE deca OF dec IS
	SIGNAL  pe, cef, cefa, vdout1, din_reset: BIT;
	--pe -parallel enable sr->sc;  er - correct error,
	--vdout - valid data out - remember data register 
	SIGNAL ff1, ff3, err, err1, err2, errcheck, ce, neq: BIT; 
	SIGNAL syn1, syn3: BIT_VECTOR(0 TO m-1); -- syndromes
	SIGNAL ch1, ch3: BIT_VECTOR(0 TO m-1); -- Chien output
	SIGNAL ch1_or: BIT_VECTOR(0 TO m-1);

	COMPONENT deq -- dout<= ( syn1^3 != syn3 )
		PORT (syn1, syn3: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT); 
		END COMPONENT;
		FOR ALL: deq USE ENTITY WORK.deq (deqa);
	COMPONENT ffce  
		PORT (clk, ce, din: IN BIT; 
			dout: OUT BIT); 
		END COMPONENT;
		FOR ALL: ffce USE ENTITY WORK.ffce (ffcea);
	COMPONENT dcount -- counter decoder 
		PORT(clk, reset: IN BIT; cef, pe, vdout, vdout1: OUT BIT); 
		END COMPONENT;
		FOR ALL: dcount USE ENTITY WORK.dcount (dcounta);
	COMPONENT dbuf -- buffer shift registers 
		PORT (clk, err, vdout, din: IN BIT; 
			dout: OUT BIT); 
		END COMPONENT;
		FOR ALL: dbuf USE ENTITY WORK.dbuf (dbufa);
	COMPONENT dsyn1 -- syndrome calculation 
		PORT (clk, pe, din: IN BIT; 
			dout1: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
		FOR ALL: dsyn1 USE ENTITY WORK.dsyn1 (dsyn1a);
	COMPONENT dsyn3 -- syndrome calculation 
		PORT (clk, pe, din: IN BIT; 
			dout3: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
		FOR ALL: dsyn3 USE ENTITY WORK.dsyn3 (dsyn3a);
	COMPONENT dch1 -- Chien's search circuit 
		PORT (clk, err, errcheck, pe: IN BIT;
			 din: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
		FOR ALL: dch1 USE ENTITY WORK.dch1 (dch1a);
	COMPONENT dch3 -- Chien's search circuit 
		PORT (clk, err, errcheck, pe: IN BIT;
			 din: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
		FOR ALL: dch3 USE ENTITY WORK.dch3 (dch3a);

  BEGIN
	c1: dcount
		PORT MAP (clk, reset, cef, pe, vdout, vdout1);
	b1: dbuf
		PORT MAP (clk, err, vdout1, din_reset, dout);
	e1: deq
		PORT MAP (ch1, ch3, neq);
	f1: ffce
		PORT MAP (clk, cefa, ch1_or(m-1), ff1);
	f2: ffce
		PORT MAP (clk, cefa, neq, ff3);
	s1: dsyn1
		PORT MAP (clk, pe, din_reset, syn1); 
	s3: dsyn3
		PORT MAP (clk, pe, din_reset, syn3); 
	h1: dch1
		PORT MAP (clk, err, errcheck, pe, syn1, ch1); 
	h3: dch3
		PORT MAP (clk, err, errcheck, pe, syn3, ch3); 


	din_reset<= din AND NOT reset;

	--  ch1_or eq_or gates
	ch1_or(0)<= ch1(0);
	gen:
	FOR i IN 1 TO m-1 GENERATE
		ch1_or(i)<= ch1_or(i-1) OR ch1(i);
	END GENERATE;	

	-- cefa - clock enable p1, p3 - cepa=1 if start of a new word or err
	cefa <= cef OR err; 
	-- error decision circuit
	err1<= NOT ff3 AND  NOT neq AND ff1 AND NOT ch1_or(m-1); 
		--single err
	err2<= ff1 AND ch1_or(m-1) AND ff3 AND NOT neq; 
		-- double error
	err<= err1 OR err2; -- error has been found
	errcheck<= NOT cef; -- 
END deca;
