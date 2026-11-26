-------------------------------- MODULE pluscal-ex0 ----------------
EXTENDS TLC, Integers, Naturals

CONSTANTS M,N,x0,y0

EXTENDS notations
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
\* Last modified Mon Dec 18 15:39:24 CET 2017 by mery
\* Created Wed Nov 18 16:12:05 CET 2015 by mery
