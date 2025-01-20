-------------------------------- MODULE malgtd1ex4 --------------------------
EXTENDS Naturals,TLC,Integers
------------------------------------------------------------------------
(* contract *)
(* variables x,y1,y2,z *)
(* requires x0 \in Nat /\ y10,y20,z0 \in Nat /\ pc="l0" *)
(* ensures zf=f91(x0) *)

------------------------------------------------------------------------
CONSTANTS x0
-------------------------------------------------------------------
(* auxiliary definitions *)
mini  ==  -2^15
maxi == 2^15-1
D == mini..maxi
UND == -650000
f91 == [i \in Int |-> IF i > 100 THEN i-10 ELSE 91]
-------------------------------------------------------------------------
VARIABLES  x,y1,y2,z,pc
------------------------------------------------------------------------
(* preconditions *)
ASSUME x0 \geq 0
-----------------------------
(* actions *)
a  == 
    /\ pc="START" 
    /\ y1'=x /\ y2'=1
    /\ pc'="LOOP"  
    /\ UNCHANGED <<x,z>>

b == 
    /\ pc="LOOP" /\  y1  \leq 100 
    /\ y1'=y1+11 /\ y2'=y2+1 
    /\  UNCHANGED <<x,z,pc>> 

cc == 
    /\ pc="LOOP" /\  y1  > 100 /\ y2#1
    /\ y1'=y1-10 /\ y2'=y2-1 
    /\  UNCHANGED <<x,z,pc>>
    /\ PrintT(y1) /\ PrintT(y2)
d ==
    /\ pc="LOOP" /\  y1  > 100 /\ y2=1
    /\ z'=y1-10 /\ pc'="HALT"
    /\ UNCHANGED <<x,y1,y2>>
-------------------------------------------------------------------------
(* spcification *)
Next == a \/ b \/ cc \/ d  \/ UNCHANGED <<y1,y2,z,x,pc>> 
init1 == x=x0 /\ y1 \in Int /\ y2 \in Int /\ z \in Int /\ pc = "START"
Init  == y1 = UND  /\ y2 = UND /\ z = UND  /\  x =  x0 /\ pc = "START"
-------------------------------------------------------------------------
(* analyse *)
Q1 == pc#"HALT"  (* pc prned la valeur HALT *)  (* fausse *)
Qpc == pc="HALT" => z=IF x>100 THEN x-10 ELSE 91
Q(y) ==  y # UND => mini \leq y /\ y \leq maxi 
Qover == Q(y1) /\ Q(y2) /\ Q(z) /\ Q(x)
Q2== Qpc /\ Qover
tocheck == Qover
=============================================
