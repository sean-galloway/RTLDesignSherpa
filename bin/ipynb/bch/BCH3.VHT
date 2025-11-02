The file bch3.dat is used by bch.exe 
and should not be changed by hand.
To change BCH code (n,k) change file bch.in
This file contains data for dec.vhd for t>2
drdcesone count dinv dec dsq dci dp1 invSel
# 

-------------------------------------------------------------------
-- 2-1 multiplexer

	USE WORK.const.ALL;
ENTITY dmul21 IS
PORT ( sel: IN BIT;
	d0, d1: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1));  
END dmul21;

ARCHITECTURE dmul21a OF dmul21 IS
  BEGIN
	gen:
	FOR i IN 0 TO m-1 GENERATE
	  dout(i)<= (NOT sel AND d0(i)) OR (sel AND d1(i));
	END GENERATE;
END dmul21a;

--------------------------------------------------------------------
-- single register with clock enable

ENTITY drd1ce IS
PORT ( clk, ce, din: IN BIT; 
	dout: OUT BIT);  
END drd1ce;

ARCHITECTURE drd1cea OF drd1ce IS
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
END drd1cea;

--------------------------------------------------------------------
-- PIPO registers m bits wide with clock enable and reset

	USE WORK.const.ALL;
ENTITY drdcer IS
PORT ( clk, ce, reset: IN BIT;
	din: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1));  
END drdcer;

ARCHITECTURE drdcera OF drdcer IS
	SIGNAL q: BIT_VECTOR(0 TO m-1);
  BEGIN
	dout<= q;
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	FOR i IN 0 TO m-1 LOOP
	  IF reset='1' THEN
		q(i)<= '0';
	  ELSIF ce='1' THEN
		q(i)<= din(i);
          ELSE 
		q(i)<= q(i);
	  END IF;
	END LOOP;
  END PROCESS;
END drdcera;

--------------------------------------------------------------------
-- PIPO registers m bits wide with clock enable and set to one

	USE WORK.const.ALL;
ENTITY drdceSOne IS
PORT ( clk, ce, set, dinone: IN BIT;
	din: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1));  
END drdcesone;

ARCHITECTURE drdcesonea OF drdcesone IS
	SIGNAL q: BIT_VECTOR(0 TO m-1);
  BEGIN
	dout<= q;
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	IF set='1' THEN 
		q(0)<= dinone;
	ELSIF ce='1' THEN
		q(0)<= din(0);
	ELSE
		q(0)<= q(0);
	END IF;
	
	FOR i IN 1 TO m-1 LOOP
	  IF set='1' THEN
		q(i)<= '0';
	  ELSIF ce='1' THEN
		q(i)<= din(i);
	  ELSE
		q(i)<= q(i);
          END IF;
	END LOOP;
  END PROCESS;
END drdcesonea;


--------------------------------------------------------------------
-- m registers with clock enable

	USE WORK.const.ALL;
ENTITY drdce IS
PORT ( clk, ce: IN BIT;
	din: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1));  
END drdce;

ARCHITECTURE drdcea OF drdce IS
	SIGNAL q: BIT_VECTOR(0 TO m-1);
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
END drdcea;
--------------------------------------------------------------------
-- PIPO registers m bits wide

	USE WORK.const.ALL;
ENTITY drd IS
PORT (clk: IN BIT;
	din: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1));  
END drd;

ARCHITECTURE drda OF drd IS
	SIGNAL q: BIT_VECTOR(0 TO m-1);
  BEGIN
	dout<= q;
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	q<= din;
  END PROCESS;
END drda;

-- sum m * XOR; dout<= din0 XOR din1

	USE WORK.const.ALL;
ENTITY dxorm IS
PORT (din0, din1: IN BIT_VECTOR(0 TO m-1);
	dout: OUT BIT_VECTOR(0 TO m-1));
END dxorm;

ARCHITECTURE dxorma OF dxorm IS
  BEGIN
	dout<= din0 XOR din1;
END dxorma;

-----------------------------------------------------------------

--------------- OPTION 3 -serial
-------------------------------------------------------------------
-- Serial In Parallel Out m bits shift register

	USE WORK.const.ALL;
ENTITY dsipo IS
PORT (clk, din: IN BIT;
	dout: OUT BIT_VECTOR(0 TO m-1)); 
END dsipo;

ARCHITECTURE dsipoa OF dsipo IS
	SIGNAL q: BIT_VECTOR(0 TO m-1);
  BEGIN
	dout<= q;
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	q<= din & q(0 TO m-2);
  END PROCESS;
END dsipoa;

-------------------------------------------------------------------
-- Shift register with serial XOR, and parallel in

	USE WORK.const.ALL;
ENTITY dshpe IS
PORT (clk, ce, pe: IN BIT;
	din: IN BIT_VECTOR(0 TO m-1); -- parallel in
	dout: OUT BIT_VECTOR(0 TO m-1)); 
END dshpe;

ARCHITECTURE dshpea OF dshpe IS
	SIGNAL ring: BIT_VECTOR(0 TO m-1);
  BEGIN
	dout<= ring;
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	IF pe= '1' THEN
	  ring<= din;	
	ELSIF ce='1' THEN
	  ring<= ring(m-1) & ring(0 TO m-2);
	END IF;
  END PROCESS;
END dshpea;

-------------------------------------------------------------------
-- Shift register with serial XOR, and reset

	USE WORK.const.ALL;
ENTITY dshr IS
PORT (clk, ce, reset, din: IN BIT;
	dout: OUT BIT_VECTOR(0 TO m-1)); 
END dshr;

ARCHITECTURE dshra OF dshr IS
	SIGNAL ring: BIT_VECTOR(0 TO m-1);
	SIGNAL dmul1: BIT;
  BEGIN
	dout<= ring;
	dmul1<= ring(m-1) XOR din;
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	IF reset='1' THEN 
	  ring(0)<= '0';
	ELSIF ce='1' THEN 
	  ring(0)<= ring(m-1) XOR din;
	END IF;	

	FOR i IN 1 TO m-1 LOOP
	  IF reset= '1' THEN
	    ring(i)<= '0';	
	  ELSIF ce='1' THEN
	    ring(i)<= ring(i-1);
	  END IF;
	END LOOP;
  END PROCESS;
END dshra;

---------------------------------------------------------------------
-- dout<= en And din

	USE WORK.const.ALL;
ENTITY dandm IS
PORT (en: IN BIT;
	din: IN BIT_VECTOR(0 TO m-1);
	dout: OUT BIT_VECTOR(0 TO m-1)); 
END dandm;

ARCHITECTURE dandma OF dandm IS
  BEGIN
	gen:
	FOR i IN 0 TO m-1 GENERATE
	  dout(i)<= din(i) AND en;
	END GENERATE;
END dandma;


---------------------------------------------------------------------
---------------------------------------------------------------------
-- buffer circuit

	USE WORK.const.ALL;
ENTITY dbuf IS
PORT (clk, bufCe, bufkCe, err, vdout1, din: IN BIT;
	dout: OUT BIT); 
END dbuf;

ARCHITECTURE dbufa OF dbuf IS
	CONSTANT buf_size: INTEGER:= #; 
	-- buf_size= chpe/interleave + 2 if buf_size<k+1; else buf_size= k 
	SIGNAL bufk: BIT_VECTOR(0 TO k-1); 
	-- bufk - first buffer for storing only first k bits
	SIGNAL buf: BIT_VECTOR(0 TO buf_size-1); -- second buffer
  BEGIN
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	IF bufCe='1' THEN
		buf<= bufk(k-1) & buf(0 TO buf_size-2);
	END IF;
	IF bufkCe='1' THEN
		bufk<= din & bufk(0 TO k-2);
	END IF;
	dout<= (buf(buf_size-1) XOR err) AND vdout1;
  END PROCESS;
END dbufa;

-----------------------------------------------------------------
-- Bit-Serial Berlekamp (Dual Basis) Multiplier without registers

	USE WORK.const.ALL;
ENTITY dsdbm IS
PORT (dbin, sbin: IN BIT_VECTOR(0 TO m-1); -- standard & dual basis input
	dout: OUT BIT); -- serial output 
END dsdbm;

ARCHITECTURE dsdbma OF dsdbm IS
	SIGNAL dxor: BIT_VECTOR(0 TO m-1); -- xor gates signals
  BEGIN
	dout<= dxor(m-1);
	dxor(0)<= sbin(0) AND dbin(0);
	gen:
	FOR i IN 1 TO m-1 GENERATE
	  dxor(i)<= dxor(i-1) XOR (sbin(i) AND dbin(i));
	END GENERATE;
END dsdbma;

-----------------------------------------------------------------
--  Bit-Serial Berlekamp (Dual Basis) Multiplier LFSR

	USE WORK.const.ALL;
ENTITY dsdbmRing IS
PORT (clk, pe: IN BIT;   -- pe- parallel enable
	din: IN BIT_VECTOR(0 TO m-1); -- dual basis input
	dout: OUT BIT_VECTOR(0 TO m-1)); 
END dsdbmRing;

ARCHITECTURE dsdbmRinga OF dsdbmRing IS
	SIGNAL ring: BIT_VECTOR(0 TO m-1); 
  BEGIN
	dout<= ring;
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	IF pe='1' THEN 
	  ring<= din;
	ELSE
	  ring(0 TO m-2)<= ring(1 TO m-1);
	  ring(m-1)<= ring(0)#;
	END IF;
  END PROCESS;
END dsdbmRinga;

-------------------------------------------------------------------
-- Bit-Parallel Dual-Basis Multiplier

	USE WORK.const.ALL;
ENTITY dpdbm IS
PORT (ddin, dsin: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1));  
END dpdbm;

ARCHITECTURE dpdbma OF dpdbm IS
	COMPONENT dsdbm -- Serial Dual Basis Multiplier without registers
	  PORT (dbin, sbin: IN BIT_VECTOR(0 TO m-1); 
	  	  -- dual & standard basis in
		dout: OUT BIT); 
	  END COMPONENT;
	  FOR ALL: dsdbm USE ENTITY WORK.dsdbm (dsdbma);

	SIGNAL aux: BIT_VECTOR(0 TO m-2); -- auxiliary signals
	SIGNAL m0in#
END dpdbma; 

-------------------------------------------------------------------
-- Bit-Parallel Multiplier 

	USE WORK.const.ALL;
ENTITY dpm IS
PORT (din1, din2: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1));  
END dpm;

ARCHITECTURE dpma OF dpm IS
	COMPONENT dsdbm -- Serial Dual Basis Multiplier without registers
	  PORT (dbin, sbin: IN BIT_VECTOR(0 TO m-1); 
	  	  -- dual & standard basis in
		dout: OUT BIT); 
	  END COMPONENT;
	  FOR ALL: dsdbm USE ENTITY WORK.dsdbm (dsdbma);

	SIGNAL b: BIT_VECTOR(0 TO #
END dpma;

----------------------------------------------------------------------------------
-- Bit-Serial Standard Basis Multiplier for syn*c=dr module2 - ring

	USE WORK.const.ALL;
ENTITY dssbm IS
PORT (clk, ce, pe : IN BIT;
	din: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1)); 
END dssbm;

ARCHITECTURE dssbma OF dssbm IS
	SIGNAL ring: BIT_VECTOR(0 TO m-1);
  BEGIN
	dout<= ring;
  PROCESS BEGIN
      WAIT UNTIL clk'EVENT AND clk='1';
      IF pe='1' THEN 
	ring<= din;
      ELSIF ce='1' THEN
	ring(0)<= din(0) XOR (NOT pe AND ring(m-1));
#      END IF;
  END PROCESS;
END dssbma;	

-------------------------------------------------------------------
-- sum t* XOR - dout= din(0) xor din(1) .... xor din(t)

	USE WORK.const.ALL;
ENTITY dxort IS
PORT (din0#: IN BIT;
	dout: OUT BIT);
END dxort;

ARCHITECTURE dxorta OF dxort IS
  BEGIN
	dout<= din0#;
END dxorta;


--------------------------------------------------------------------

-- Multiply by L^i, where gen. polynomial = 1+ x^i + x^m (for m!=8)

	USE WORK.const.ALL;
ENTITY dmli IS
PORT (din: IN BIT_VECTOR(0 TO m-1);
 	dout: OUT BIT_VECTOR(0 TO m-1));
END dmli;

ARCHITECTURE dmlia OF dmli IS
BEGIN
#END dmlia;

---------------------------------------------------------------------------
-- squaring dout<= (din)^2 in standard basis -- for inverse calculator

	USE WORK.const.ALL;
ENTITY dsq IS
PORT ( din: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1)); -- serial output 
END dsq;

ARCHITECTURE dsqa OF dsq IS
# 
END dsqa;

-----------------------------------------------------------------------------
-- m* registers with reset to dual basis one

	USE WORK.const.ALL;
ENTITY drdrDualOne IS
PORT (clk, ce, reset: BIT;
	din: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT_VECTOR(0 TO m-1)); -- serial output 
END drdrDualOne;

ARCHITECTURE drdrDualOnea OF drdrDualOne IS
	SIGNAL q: BIT_VECTOR(0 TO m-1);
  BEGIN
	dout<= q;
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	IF reset='1' THEN
		q<= "#";
	ELSIF ce='1' THEN
		q<= din;
	ELSE 
		q<= q;
	END IF;
  END PROCESS;
END drdrDualOnea;

----------------------------------------------------------------------------------
-- Inverter dout<= din^(-1)<= din^(2)*din^(4)*...*din^(2^(m-1))

	USE WORK.const.ALL;
ENTITY dinv IS
PORT (clk, cbBeg, bsel, caLast, cce, drnzero, snce, synpe: IN BIT;  
	din: IN BIT_VECTOR(0 TO m-1); --input data selected by sel_in
	dout: OUT BIT_VECTOR(0 TO m-1));
END dinv;

ARCHITECTURE dinva OF dinv IS
	SIGNAL qsq, sq, msin, mdin, mout: BIT_VECTOR(0 TO m-1);
	-- sq- square, q??- RD out, m??? - parallel multiplier, ?d/s -dual standard basis
	SIGNAL ce1, ce2a, ce2b, ce2, reset, sel: BIT;
	
	COMPONENT dmul21   -- 2-1 multiplexer
	  	PORT ( sel: IN BIT; d0, d1: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
	  	FOR ALL: dmul21 USE ENTITY WORK.dmul21 (dmul21a);
	COMPONENT drdce     -- PIPO register
	  	PORT (clk, ce: IN BIT; din: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1));  
		END COMPONENT;
	  	FOR ALL: drdce USE ENTITY WORK.drdce (drdcea);
	COMPONENT drdrDualOne -- registers with and reset to dual basis one
		PORT (clk, ce, reset: IN BIT; din: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
	  	FOR ALL: drdrDualOne USE ENTITY WORK.drdrDualOne (drdrDualOnea);
	COMPONENT dsq    -- dout<= (din)^2
	  	PORT ( din: IN BIT_VECTOR(0 TO m-1);
			dout: OUT BIT_VECTOR(0 TO m-1));
		END COMPONENT;
		FOR ALL: dsq USE ENTITY WORK.dsq (dsqa);
	COMPONENT dpdbm    -- Parallel dual basis multiplier
		PORT (ddin, dsin: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1));  
		END COMPONENT;
	  	FOR ALL: dpdbm USE ENTITY WORK.dpdbm (dpdbma);
  BEGIN
	ce1<= ce2 OR caLast OR synpe;
	ce2a<= drnzero AND cbBeg;
	ce2b<= bsel OR ce2a;
	ce2<= cce AND NOT snce AND ce2b;
	reset<= (snce AND bsel) OR synpe;
	sel<= caLast OR synpe;

	dout<= mout;
	x1: dmul21
	  PORT MAP (sel, qsq, din, msin);
	s1: dsq
	  PORT MAP (msin, sq);
	q1: drdce  
	  PORT MAP (clk, ce1, sq, qsq);
	q2: drdrDualOne
	  PORT MAP (clk, ce2, reset, mout, mdin);
	m1: dpdbm
	  PORT MAP (mdin, msin, mout);
END dinva;

---------------------------------------------------------------------------------
-- Find if chien search circuit is equal 0

	USE WORK.const.ALL;
ENTITY dcheq IS
PORT (#: IN BIT_VECTOR(0 TO m-1); 
	dout: OUT BIT); -- dout=1 if equal 
END dcheq;

ARCHITECTURE dcheqa OF dcheq IS
	SIGNAL eq: BIT_VECTOR(0 TO m-1);
  BEGIN
#);
END dcheqa;

----------------------------------------------------------------------------------
---------------------------------------------------------------------------
-- Syndromes calculation circuits
#
---------------------------------------------------------------------------
-- Chien search circuits
#
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
-- CONTROL ENTITIES - counters
-- counter a

	USE WORK.const.ALL;
ENTITY dca IS
PORT (clk, reset: IN BIT;
	cRes: OUT BIT; -- cRes<= countLast OR  reset
	dout: OUT BIT_VECTOR(0 TO sizea-1)); -- count
END dca;

ARCHITECTURE dcaa OF dca IS
	SIGNAL ca, cin, cand: BIT_VECTOR(0 TO sizea-1);
	SIGNAL CRes1, cLast: BIT;
  BEGIN
	dout<= ca;
	cRes<= cRes1;
	cRes1<= cLast OR reset;
#		--cLast=1 - when c= iteration-1
	cand(0)<= ca(0);
	cin(0)<= NOT ca(0);

	   gen_cin:
	FOR i IN 1 TO sizea-1 GENERATE
		cin(i)<= cand(i-1) XOR ca(i);
	END GENERATE;
	  den_cand_if:
	IF sizea>2 GENERATE
	  gen_cand:
	  FOR i IN 1 TO sizea-2 GENERATE
		cand(i)<= ca(i) AND cand(i-1);
	  END GENERATE;
	END GENERATE;
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	FOR i IN 0 TO sizea-1 LOOP
	  IF cRes1='1' THEN
        	ca(i)<= '0';	
	  ELSE
		ca(i)<= cin(i);
	  END IF;
	END LOOP;
  END PROCESS;
END dcaa;

#5-------------------------------------------------------------------------------
-- interleave counter - copied only if interleave>1

	USE WORK.const.ALL;
ENTITY dci IS
PORT (clk, reset: IN BIT;
	dout: OUT BIT); -- dout=1 if count=0
END dci;

ARCHITECTURE dcia OF dci IS
	CONSTANT sizei: INTEGER:= #5; -- =log2(interleave)
	SIGNAL ci, cin, cand: BIT_VECTOR(0 TO sizei-1);
	SIGNAL cBeg, cLast, res: BIT;
  BEGIN
	dout<= cBeg;
	res<= cLast OR reset;
	--cLast=1 - when ci= interleave-1
#5	cand(0)<= ci(0);
	cin(0)<= NOT ci(0);
#5
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	FOR i IN 0 TO sizei-1 LOOP
	  IF res='1' THEN
        	ci(i)<= '0';	
	  ELSE
		ci(i)<= cin(i);
	  END IF;
	END LOOP;
  END PROCESS;
END dcia;

#-------------------------------------------------------------------------------
-- counter b -- no. of cicles count= iteration*cb +ca 

	USE WORK.const.ALL;
ENTITY dcb IS
PORT (clk, ce, reset: IN BIT;
	dout: OUT BIT_VECTOR(0 TO sizeb-1)); -- count
END dcb;

ARCHITECTURE dcba OF dcb IS
	SIGNAL cb, cin, cand: BIT_VECTOR(0 TO sizeb-1);
  BEGIN
	dout<= cb;
	cand(0)<= cb(0);
	cin(0)<= NOT cb(0);

	   gen_cin:
	FOR i IN 1 TO sizeb-1 GENERATE
		cin(i)<= cand(i-1) XOR cb(i);
	END GENERATE;
		gen_cand:
	FOR i IN 1 TO sizeb-2 GENERATE
		cand(i)<= cb(i) AND cand(i-1);
	END GENERATE;
  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	FOR i IN 0 TO sizeb-1 LOOP
	  IF reset='1' THEN
        	cb(i)<= '0';	
	  ELSIF ce='1' THEN
		cb(i)<= cin(i);
	  END IF;
	END LOOP;
  END PROCESS;
END dcba;
-------------------------------------------------------------------------------
-- l (degree of error polynomial in BMA) circuit  

	USE WORK.const.ALL;
ENTITY dcl IS
PORT (clk, ce, reset, bsel: IN BIT;
	cb: BIT_VECTOR(0 TO sizeb-1);
	dout: OUT BIT); -- dout=1 if l<= cb
END dcl;

ARCHITECTURE dcla OF dcl IS
	SIGNAL l, lin, lcarry, lxor, lcomp: BIT_VECTOR(0 TO sizel-1);
	SIGNAL lce: BIT;
  BEGIN
	dout<= lcomp(sizel-1);
	-- compare --> lcomp(sizel-1)<= (cb>=l)
	lcomp(0)<= NOT l(0) OR cb(0);
	gencomp:
	FOR i IN 1 TO sizel-1 GENERATE
	  lcomp(i)<= (lcomp(i-1) AND (NOT l(i) OR cb(i)))  OR  (NOT l(i) AND cb(i));
	END GENERATE;
		
	-- register l subtractor; lin<= 2*cb-l+1 <=> { lin<=2*cb+2+NOT(l) }
	lin(0)<= NOT l(0);
	lin(1) <= cb(0) XOR l(1);
	lcarry(1)<= cb(0) OR NOT l(1);
	      genl:
	FOR i IN 2 TO sizel-1 GENERATE
		lxor(i)<= cb(i-1) XOR NOT l(i);
		lin(i)<= lxor(i) XOR lcarry(i-1);
		lcarry(i)<= (NOT l(i) AND cb(i-1)) OR (lxor(i) AND lcarry(i-1));
	END GENERATE;
	lce<= ce AND bsel;
  PROCESS BEGIN  
	WAIT UNTIL clk'EVENT AND clk='1';
	-- l register 
	IF reset='1' THEN
		l(0)<= bsel;   -- if Syn1=0 l<= 0, else l<=1
	ELSIF lce='1' THEN
		l(0)<= lin(0);
	END IF;

	FOR i IN 1 TO sizel-1 LOOP
	  IF reset='1' THEN
		l(i)<= '0';
	  ELSIF lce='1' THEN
		l(i)<= lin(i);
	  END IF;
	END LOOP;
  END PROCESS;
END dcla;

-------------------------------------------------------------------------------	
-- control system and counter

	USE WORK.const.ALL;
ENTITY dcount IS
PORT (clk, reset, drnzero: IN BIT;
	bsel, bufCe, bufkCe, chpe, msmpe, snce, synpe, vdout, vdout1#0: OUT BIT);
		-- vdout - delayed by one clock vdout11
END dcount;

ARCHITECTURE dcounta OF dcount IS
	COMPONENT drd1ce -- single register with clock enable
		PORT ( clk, ce, din: IN BIT; dout: OUT BIT);
		END COMPONENT; 
	  	FOR ALL: drd1ce USE ENTITY WORK.drd1ce (drd1cea);
	COMPONENT dca  -- counter a
		PORT (clk, reset: IN BIT; cRes: OUT BIT;
		dout: OUT BIT_VECTOR(0 TO sizea-1));	
		END COMPONENT; 
	  	FOR ALL: dca USE ENTITY WORK.dca (dcaa);
	COMPONENT dcb  -- counter b
		PORT (clk, ce, reset: IN BIT;
		dout: OUT BIT_VECTOR(0 TO sizeb-1));	
		END COMPONENT; 
	  	FOR ALL: dcb USE ENTITY WORK.dcb (dcba);
	COMPONENT dcl -- l (degree of error polynomial in BMA) circuit  
		PORT (clk, ce, reset, bsel: IN BIT; -- dout=1 if l<= cb
		cb: BIT_VECTOR(0 TO sizeb-1); dout: OUT BIT); 
		END COMPONENT; 
	  	FOR ALL: dcL USE ENTITY WORK.dcL (dcLa);
#5	COMPONENT dci  -- interleave counter
		PORT (clk, reset: IN BIT; dout: OUT BIT); -- dout=1 if count=0
		END COMPONENT; 
	  	FOR ALL: dci USE ENTITY WORK.dci (dcia);
# 
	-- VHDL Template
	SIGNAL ca: BIT_VECTOR(0 TO sizea-1); -- counter a
	SIGNAL cb: BIT_VECTOR(0 TO sizeb-1); --  count= ca+ iteration*cb
	SIGNAL res, bsel1, caRes, bufR, bufRa, bufRb, bufS, bufSa, bufSb, bufSR: BIT; 
	SIGNAL chpe1, chpe1a, chpe1b, synpe1,  msmpe1, cei1: BIT;
	-- cei - interleave clock enable
	SIGNAL vdout11, vdout11a, vdout1R, vdout1Ra, vdout1Rb: BIT;
	SIGNAL vdout1S, vdout1Sa, vdout1Sb: BIT;
	SIGNAL ca0, caLast,caNextLast, cb0, cLast, cLasta, cLastb, lCe, lcomp: BIT;
	SIGNAL bufkCeCe, one, vdout11Ce, vdout11In, bufCe1, bufkCe1: BIT;
	SIGNAL noFirstVdoutIn, noFirstVdout, vdout11aDel: BIT;
  BEGIN
	res<= reset OR clast;
	a1: dca
		PORT MAP (clk, res, caLast, ca);
	b1: dcb
		PORT MAP (clk, caLast, res, cb);
	l1: dcl
		PORT MAP (clk, lCe, synpe1, bsel1, cb, lcomp); -- lcomp=1 if cb>=l
	bufkCeCe<= res OR bufR;
	bufk_Ce: drd1ce  -- buffer Clock Enable register
		PORT MAP (clk, bufkCeCe, res, bufkCe1);
	bufkCe<= bufkCe1 AND cei1;

	one<= '1'; 
	vDoutD: drd1ce -- delay vdout by one clock signal: vdout11
		PORT MAP (clk, one, vdout11, vdout);
	vdout11Ce<= reset OR vdout1R OR vdout1S;
	vdout11In<= vdout1S AND NOT reset;
	vdout11P: drd1ce  -- set if vdout1S; reset if reset or vdout1R
		PORT MAP (clk, vdout11Ce, vdout11In, vdout11a);	
	-- After reset the first vdout11a is not valid
	vdout1aDelay: drd1ce
		PORT MAP (clk, one, vdout11a, vdout11aDel); 
	noFirstVdoutIn<= NOT reset AND ((NOT vdout11a AND vdout11aDel) OR noFirstVdout); 
		-- falling edge of vdout1a - set; reset - reset
	noFirstAfterReset: drd1ce
		PORT MAP (clk, one, noFirstVdoutIn, noFirstVdout); 

	vdout11<= vdout11a AND cei1 AND noFirstVdout;

	snce<= ca0;
	chpe<= chpe1;
	synpe<= synpe1;
	synpe1<= ca0 AND cb0;
	vdout1<= vdout11;
	msmpe<= msmpe1;
	bsel<= bsel1;
	bsel1<= drnzero AND (lcomp OR synpe1);

	-- generated by C program
#END dcounta;	


------------------------------------------------------------------------------
----------------------------------------------------------------------------------
-- decoder

	USE WORK.const.ALL;
ENTITY dec IS
PORT (clk, reset, din: IN BIT;
	vdout, dout: OUT BIT);
END dec;

ARCHITECTURE deca OF dec IS

	COMPONENT dbuf   -- input output buffer
		PORT (clk, bufCe, bufkCe, err, vdout1, din: IN BIT;
			dout: OUT BIT);
		END COMPONENT; 
	  	FOR ALL: dbuf USE ENTITY WORK.dbuf (dbufa);
	COMPONENT drd1ce -- single register with clock enable
		PORT ( clk, ce, din: IN BIT; dout: OUT BIT);
		END COMPONENT; 
	  	FOR ALL: drd1ce USE ENTITY WORK.drd1ce (drd1cea);
	COMPONENT dmul21 
		PORT ( sel: IN BIT; d0, d1: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1));  
		END COMPONENT; 
	  	FOR ALL: dmul21 USE ENTITY WORK.dmul21 (dmul21a);
	COMPONENT drd     -- PIPO register
	  	PORT (clk: IN BIT; din: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1));  
		END COMPONENT;
	  	FOR ALL: drd USE ENTITY WORK.drd (drda);
	COMPONENT drdce   -- PIPO register
	  	PORT (clk, ce: IN BIT; din: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1));  
		END COMPONENT;
	  	FOR ALL: drdce USE ENTITY WORK.drdce (drdcea);
	COMPONENT drdcer   -- PIPO register
	  	PORT (clk, ce, reset: IN BIT; din: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1));  
		END COMPONENT;
	  	FOR ALL: drdcer USE ENTITY WORK.drdcer (drdcera);
	COMPONENT drdcesone   -- m registers with CE and if set='1' dout<=din0&"00.." 
		PORT ( clk, ce, set, dinone: IN BIT; din: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1));
		END COMPONENT;
	  	FOR ALL: drdcesone USE ENTITY WORK.drdcesone (drdcesonea);
	COMPONENT dpm    -- Parallel dual basis multiplier
		PORT (din1, din2: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1));  
		END COMPONENT;
	  	FOR ALL: dpm USE ENTITY WORK.dpm (dpma);
	COMPONENT dxorm            -- dout<= din1 xor din0; opt.1
		PORT (din0, din1: IN BIT_VECTOR(0 TO m-1);
			dout: OUT BIT_VECTOR(0 TO m-1));
		END COMPONENT;
	  	FOR ALL: dxorm USE ENTITY WORK.dxorm (dxorma);


		-- OPTION 3
	COMPONENT dshr   -- shift register with reset and serial XOR, opt.3
		PORT (clk, ce, reset, din: IN BIT;
			dout: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
	  	FOR ALL: dshr USE ENTITY WORK.dshr (dshra);
	COMPONENT dshpe   -- shift register with parallel in and serial XOR, opt.3
		PORT (clk, ce, pe: IN BIT; din: IN BIT_VECTOR(0 TO m-1);
			dout: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
	  	FOR ALL: dshpe USE ENTITY WORK.dshpe (dshpea);
	COMPONENT dsdbm -- serial dual basis multiplier without ring, opt.3
		PORT (dbin, sbin: IN BIT_VECTOR(0 TO m-1); dout: OUT BIT);
		END COMPONENT;
	  	FOR ALL: dsdbm USE ENTITY WORK.dsdbm (dsdbma);
	COMPONENT  dsdbmRing  -- serial dual basis multiplier ring, opt.3
		PORT (clk, pe: IN BIT;   -- pe- parallel enable
			din: IN BIT_VECTOR(0 TO m-1);
			dout: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
	  	FOR ALL: dsdbmRing USE ENTITY WORK.dsdbmRing (dsdbmRinga);
	COMPONENT dssbm   -- serial standard basis multiplier ring, opt3
		PORT (clk, ce, pe: IN BIT; din: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT_VECTOR(0 TO m-1)); 
		END COMPONENT;
	  	FOR ALL: dssbm USE ENTITY WORK.dssbm (dssbma);
	COMPONENT dmli  -- multiply by alpha^i (1 + x^i + x^m; for m!=8), opt.3
		PORT (din: IN BIT_VECTOR(0 TO m-1);
 			dout: OUT BIT_VECTOR(0 TO m-1));
		END COMPONENT;
	  	FOR ALL: dmli USE ENTITY WORK.dmli (dmlia);
	COMPONENT dinv  -- inverter
		PORT (clk, cbBeg, bsel, caLast, cce, drnzero, snce, synpe: IN BIT;  -- pe- parallel enable - if dr!=0; 
			din: IN BIT_VECTOR(0 TO m-1);
			dout: OUT BIT_VECTOR(0 TO m-1));
		END COMPONENT;
	  	FOR ALL: dinv USE ENTITY WORK.dinv (dinva);
	COMPONENT dandm  -- dout<= din AND en
		PORT (en: IN BIT; din: IN BIT_VECTOR(0 TO m-1);
		dout: OUT BIT_VECTOR(0 TO m-1));
		END COMPONENT;
	  	FOR ALL: dandm USE ENTITY WORK.dandm (dandma);
	
		-- common
	COMPONENT dxort                       -- (t-1) * XOR
		PORT (din0#: IN BIT; dout: OUT BIT);
		END COMPONENT;
	  	FOR ALL: dxort USE ENTITY WORK.dxort (dxorta);
	COMPONENT dcheq   -- check if Chien search circuit is zero
		PORT (din#: IN BIT_VECTOR(0 TO m-1); 
			dout: OUT BIT); -- dout=1 if an error occur
		END COMPONENT;
	  	FOR ALL: dcheq USE ENTITY WORK.dcheq (dcheqa);

	-- SYNDROMES & CHIEN SEARCH
#2
	--  option 2 VHDL template
	SIGNAL  chpe, msmPe, snce, synpe, vdout1: BIT; 
		-- from counter - control signals
	SIGNAL cs, dr, drnzero: BIT_VECTOR(0 TO m-1);
	SIGNAL err, bsel, bufCe, bufkCe, b23set, b2s, b3s: BIT;  
		-- bsel=1 - Br+1<- Br*x^2
	SIGNAL one: BIT;
	SIGNAL dp, qdpin, xc1in: BIT_VECTOR(0 TO m-1);
	SIGNAL qdpce, qdpset: BIT;

	COMPONENT dcount --counter
		PORT (clk, reset, drnzero: IN BIT;
		bsel, bufCe, bufkCe, chpe, msmpe, snce, synpe, vdout, vdout1: OUT BIT);
		END COMPONENT; 
	  	FOR ALL: dcount USE ENTITY WORK.dcount (dcounta);
 
  BEGIN
	xqdp: dmul21
		PORT MAP (synpe, dr, syn1, qdpin);
	qdpce<= bsel AND snce;
	qdpset<= synpe AND NOT drnzero(m-1);
	qdp: drdcesone
		PORT MAP (clk, qdpce, qdpset, one, qdpin, dp);
	count: dcount
		PORT MAP (clk, reset, drnzero(m-1), bsel, bufCe, bufkCe, chpe, msmpe, snce, synpe, vdout, vdout1#5, cei#2);
	msm: drdce
		PORT MAP (clk, msmpe, cs, dr);
	c0: drdcesone
		PORT MAP (clk, snce, synpe, one, mc0out, c0out);
	ch0: drdce
		PORT MAP (clk, chpe, c0out, ch0out);
	c1: drdce
		PORT MAP (clk, snce, c1in, c1out);
	xc1: dmul21
		PORT MAP (synpe, mc1out, syn1, c1in);
	drnzero(0)<= qdpin(0);
	gen_drnzero:
	FOR i IN 1 TO m-1 GENERATE
		drnzero(i)<= drnzero(i-1) OR qdpin(i);
	END GENERATE;
	b23set<= synpe OR (snce AND NOT bsel);
	b2s<= synpe AND drnzero(m-1);
	b2: drdcesone
		PORT MAP (clk, snce, b23set, b2s, c0out, b2out);
	b3s<= synpe AND NOT drnzero(m-1);
	b3:  drdcesone
		PORT MAP (clk, snce, b23set, b3s, c1out, b3out);

#3
	--  option 3 VHDL template
	SIGNAL  chpe, msmPe, msmCe, snce, synpe, vdout1, caLast: BIT; 
	SIGNAL  cce, cbBeg: BIT; 
		-- from counter - control signals
	SIGNAL err, bsel, bufCe, bufkCe: BIT;
	SIGNAL b3set, b3sIn, b2out, b2ce, b3ce, xbsel: BIT;  
		-- bsel=1 - Br+1<- Br*x^2 
	SIGNAL drnzero, dringPe, ccCe, qdr_or, qdr_orCe: BIT;
	SIGNAL one, c0first: BIT;
	SIGNAL c1in, cs, dr, dra, dr_or: BIT_VECTOR(0 TO m-1);
	SIGNAL drpd, qd, dli, dmIn, dm: BIT_VECTOR(0 TO m-1);
	SIGNAL cin: BIT_VECTOR(2 TO t);
#8	-- only for m=8
	SIGNAL xdaOut, xdbOut, xdcOut, xddOut, xdeOut: BIT_VECTOR(0 TO 7);
	SIGNAL d1L, d2L, d2La, d3L, dm1l, dxOut: BIT_VECTOR(0 TO 7);
	SIGNAL ca3, ca4, ca5, ca45: BIT;
#3  BEGIN
	b2: drd1ce
		PORT MAP (clk, b2ce, bsel, b2out);
	b3ce<= caLast AND NOT cbBeg;
	b2ce<= synpe OR b3ce;

	dr_or(0)<= dra(0);  -- dr_or<= dra(0) OR dra(1) ... OR dra(m-1)
	gen_dr:
	FOR i IN 1 TO m-1 GENERATE
		dr_or(i)<= dr_or(i-1) OR dra(i);
	END GENERATE;
	qdr_orCe<= synpe OR caLast;
	qdrOr: drd1ce
		PORT MAP (clk, qdr_orCe, dr_or(m-1), qdr_or);
	drnzero<= (synpe AND dr_or(m-1)) OR (NOT synpe AND qdr_or);
	msmCe<= NOT caLast;
	msm: dssbm
		PORT MAP (clk, msmce, msmpe, cs, dr);	

	xdr: dmul21
		PORT MAP (synpe, dr, syn1, dra);
	
	inv: dinv
		PORT MAP (clk, cbBeg, bsel, caLast, cce, drnzero, snce, synpe, dra, drpd);
		-- c0first - count next to the last
	qdd: drdce
		PORT MAP (clk, caLast, drpd, qd);

	b3set<= synpe OR (b3ce AND NOT bsel);
	b3sIn<= synpe AND NOT drnzero;
	b3:  drdcesone
		PORT MAP (clk, b3ce, b3set, b3sIn, c1out, b3out);
	xbsel<= bsel OR cbBeg;  -- cbBeg to reset b:
	ccCe<= (msmPe AND cbBeg) OR caLast;
	c1in<= syn1(m-1) & syn1(0 TO m-2);
	c1: dshpe
		PORT MAP (clk, cce, synpe, c1in, c1out);
	cin(2)<= dm(0) AND b2out AND NOT cbBeg;
#9	-- for m!= 8
	mli: dmli  -- multiply by second non-zero coefficient no
		PORT MAP (drpd, dli);
	xdm: dmul21
		PORT MAP (caLast, qd, dli, dmIn);
	dring: dsdbmRing
		PORT MAP (clk, dringPe, dmIn, dm);	
#8
	-- only for m=8
	xda: dmul21
		PORT MAP (caLast, qd, drpd, xdaOut);	
	mla: dmli	-- multiply by L^1
		PORT MAP (xdaOut, d1L);
	mlb: dmli	-- total L^2
		PORT MAP (d1L, d2L);
	mlc: dmli	-- total L^3
		PORT MAP (d2L, d3L);
	mlm: dmli	-- multiply dm by L^1
		PORT MAP (dm, dm1L);

	dring: drd
		PORT MAP(clk, dmIn, dm);
	xdb: dmul21
		PORT MAP (caLast, dxOut, d3L, dmIn);
	dx: dxorm 
		PORT MAP (xdeOut, xdcOut, dxOut);
	ca45<= ca4 OR ca5;
	xdc: dmul21
		PORT MAP (ca45, dm1L, xddOut, xdcOut);
	xdd: dmul21
		PORT MAP (ca5, qd, d1L, xddOut);	
	xde: dmul21
		PORT MAP (ca3, d2La, d3L, xdeOut);	
	d2And: dandm
		PORT MAP (ca4, d2L, d2La);
	-- dmIn<= qd*L^3 <-caLast;  qd*(L^3+L^7) =qd*L^3+dm*L^1 <-ca3; 
	-- qd*(L^0+L^2) <-ca4; qd*L^1 <-ca5; dm*L^1 <-default
# 
	--- common for all option VHDL template 
	one<= '1';
	buf: dbuf
		PORT MAP (clk, bufCe, bufkCe, err, vdout1, din, dout);
END deca;
#
----
#
----
