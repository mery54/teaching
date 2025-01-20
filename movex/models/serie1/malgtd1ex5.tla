------------MODULE malgtd1ex5 --------

EXTENDS Integers,TLC
--------------------------------------------------------------
------------------------------------------------------------------------
(* contract *)
(* variables x,y,z *)
(* requires x0 \in Nat /\ y0 \in Nat /\ Z \IN BOOL *)
(* ensures zf= prime(x0) *)
CONSTANTS mini,maxi,und, bund (* constants for undefinedness,  bounds of domain *)
--------------------------------------------------------------
(* requires *) 
CONSTANTS x0  (* x0 is the input *)
--------------------------------------------------------------
(* precondition *)
ASSUME x0 \in Nat 
--------------------------------------------------------------
VARIABLES  x,y,z,pc
--------------------------------------------------------------
Init ==  x = x0 /\ y=und  /\ z=bund /\ pc="start"
--------------------------------------------------------------
L1 == pc = "start" /\ y'=2 /\ pc'="loop" /\ UNCHANGED <<x,z>>
L2 == pc = "loop" /\ y \geq  x /\ z'=TRUE /\ pc'="halt" /\ UNCHANGED << x,y>>
L3 == pc="loop" /\ y<x /\ x % y =0 /\ z'= FALSE /\ pc'="halt" /\ UNCHANGED <<x,y>> 
L4 == pc="loop" /\ y<x /\ x % y # 0  /\ y'=y+1 /\ UNCHANGED << pc,x,z>>
skip == UNCHANGED << pc,x,z,y  >>
--------------------------------------------------------------
Next == L1 \/ L2 \/ L3 \/ L4 \/ skip
-------------------------------------------------------------
(* auxiliary definitions *)
prime(u) == \A v \in 2..u-1: u % v # 0   (* define that u is a prime number *)
Dbool == {FALSE,TRUE}
Dint == mini..maxi (* domain for integer variables *)
DDint(v) == v # und => v \in Dint
DDbool(v) == v # bund => v \in Dbool
-------------------------------------------------------------
(* properties to check *)
SafePC == pc="halt" => z=prime(x0) /\ PrintT(z)(* the algorithm is partially  correct *)
SafeRTE == DDint(y) /\ DDbool(z) (* the  algorithm is  runtime errors free. *) 
Safe == SafePC /\ SafeRTE 
================================================================================

