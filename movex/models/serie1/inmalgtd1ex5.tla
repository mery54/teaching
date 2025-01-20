------------MODULE inmalgtd1ex5 --------

EXTENDS Integers,TLC
--------------------------------------------------------------
CONSTANTS mini,maxi,und, bund (* constants for undefinedness,  bounds of domain *)
--------------------------------------------------------------
prime(u) == \A v \in 2..u-1: u % v # 0   (* define that x is a prime number *)
(* requires *) 
CONSTANTS x0,y0,z0  (* x is the input *)
ASSUME x0 \in Nat /\ y0 \in Int /\ z0 \in {FALSE,TRUE} 
(* ensures *)
post(u0,v0,w0,u,v,w) == (w = prime(u0)) 
--------------------------------------------------------------
VARIABLES  x,y,z,pc
--------------------------------------------------------------
Init ==  x=x0 /\ y=y0  /\ z=z0 /\ pc="start"
--------------------------------------------------------------
L1 == pc = "start" /\ y'=2 /\ pc'="loop" /\ UNCHANGED <<x,  z >> /\ PrintT(y)
L2 == pc = "loop" /\ y \geq  x /\ z'=TRUE /\ pc'="halt" /\ UNCHANGED << x,y  >>
L3 == pc="loop" /\ y<x /\ x % y =0 /\ z'= FALSE /\ pc'="halt" /\ UNCHANGED << x,y  >> 
L4 == pc="loop" /\ y<x /\ x % y # 0  /\ y'=y+1 /\ UNCHANGED << x,pc,z  >>
skip == UNCHANGED << pc,z,y,x >>
--------------------------------------------------------------
Next == L1 \/ L2 \/ L3 \/ L4 \/ skip
-------------------------------------------------------------
(* auxiliary definitions *)
Dint == mini..maxi (* domain for integer variables *)
Dbool == {FALSE,TRUE}
DDint(v) == v # und => v \in Dint
DDbool(v) == v # bund => v \in Dbool
-------------------------------------------------------------
Q1 == pc="halt" => post(x0,y0,z0,x,y,z) (* is the  algorithm partially correct? *)
SafePC == pc="halt" => post(x0,y0,z0,x,y,z) (* the algorithm is partially  correct *)
Q2 == pc # "halt"
Q3 == DDint(x) /\ DDint(y) /\ DDbool(z) (* is the  algorithm runtime errors free? *)
SafeRTE == DDint (x) /\ DDint(y) /\ DDbool(z) (* the  algorithm is  runtime errors free. *) 
Safe == SafePC /\ SafeRTE
================