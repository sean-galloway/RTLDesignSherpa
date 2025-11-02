-- BCH codes file
-- input output interface for decoder and encoder
-- entities are use if defferent input/output interface is needed
-- normally encoder (decoder) supports the interface that cannot accept
-- data continuasly but only if vdin (vdout )signal is high

-- Therefore this interface is that encoder (decoder) accepts data with 
-- continouosly (clkout) frequency (without additional control signal)
-- it should be mantioned that these circuit should be rather not used
-- as they only show how the system may work (the system is not optimized).


-- for encoder

	USE WORK.const.ALL;
ENTITY ioenc IS
PORT (clk, clkinf, reset, din: IN BIT;
	dout: OUT BIT); 
END ioenc;
	-- clk -  to clock encoded data frequency 
	-- clkinf - to clock input information data
	-- din - information data clocked with clkio clock
	-- dout - encoded data to be transmitted 

ARCHITECTURE ioenca OF ioenc IS
  	COMPONENT enc			
		PORT(clk, reset, din: IN BIT;
			vdin, dout: OUT BIT); 
		END COMPONENT;
		FOR ALL : enc USE ENTITY WORK.enc (enca);

	SIGNAL qin, qout: BIT_VECTOR(0 TO k-1);
	SIGNAL vdin, prevVdin, pe: BIT;
  BEGIN
   	e1: enc
		PORT MAP (clk, reset, qout(k-1), vdin, dout);
	
	pe<= NOT vdin AND prevVdin;	
  PROCESS BEGIN
	WAIT UNTIL clkinf'EVENT AND clkinf='1';
	qin(0)<= din;
	qin(1 TO k-1)<= qin(0 TO k-2); -- shift registers
  END PROCESS;

  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	prevVdin<= vdin;
	qout(0)<= qin(0);
	
	IF pe='0' THEN
	  qout(1 TO k-1)<= qout(0 TO k-2); -- shift registers
	ELSE
	  qout(1 TO k-1)<= qin(1 TO k-1);
	END IF;
  END PROCESS;
END ioenca;


-- for decoder

	USE WORK.const.ALL;
ENTITY iodec IS
PORT (clk, clkinf, reset, din: IN BIT;
	dout: OUT BIT); 
END iodec;
	-- clk -  to clock encoded data frequency 
	-- clkinf - to clock input information data
	-- din - recieved data
	-- dout - information data 

ARCHITECTURE iodeca OF iodec IS
 	COMPONENT dec
		PORT(clk, reset, din: IN BIT;
			vdout, dout: OUT BIT); 
		END COMPONENT;
		FOR ALL : dec USE ENTITY WORK.dec (deca); 

	SIGNAL qin, qout: BIT_VECTOR(0 TO k-1);
	SIGNAL vdout, prevVdout, pe, ddec: BIT;
  BEGIN
   	d1: dec
		PORT MAP (clk, reset, din, vdout, ddec);
	
	pe<= NOT vdout AND prevVdout;	
  PROCESS BEGIN
	WAIT UNTIL clkinf'EVENT AND clkinf='1';
	prevVdout<= vdout;
	qout(0)<= qin(0);

	IF pe='1' THEN
	  qout(1 TO k-1)<= qin(1 TO k-1); -- parallel enable
	ELSE 
	  qout(1 TO k-1)<= qout(0 TO k-2); -- shift
	END IF;
  END PROCESS;

  PROCESS BEGIN
	WAIT UNTIL clk'EVENT AND clk='1';
	qin(0)<= ddec;
	qin(1 TO k-1)<= qin(0 TO k-2); -- shift registers
  END PROCESS;
END iodeca;
