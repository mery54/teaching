-------------------------------- MODULE pluscalex0 ----------------
EXTENDS TLC, Integers, Naturals

CONSTANTS M,N,x0,y0


-----------------------------
ASSUME x0 \in \in 1..M /\ y0 \in \in 1..N


(*
--algorithm ex { 
	    variables x = x0, y = y0;
	    { 
	    while (x # y) { 
	    	  if (x < y) 
		     { y := y - x; } 
		  else 
		     { x := x-y; } };
	    assert x = GCD(x0, y0) /\ y = GCD(x0, y0) } } 

*)

=============================================================================
\* Modification History
\* Last modified Thu Oct 08 13:34:12 CEST 2026 by mery
\* Created Wed Nov 18 16:12:05 CET 2015 by mery
