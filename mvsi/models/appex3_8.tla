-------------------------------- MODULE appex3_8 --------------------------------
EXTENDS Naturals, Integers
CONSTANTS x0, intmin, intmax
VARIABLES  x,pc
ASSUME x0 \in Nat 
typeInt(u) == u \in Int  (* u is an integer *)
D(X) == intmin \leq X /\ X \leq intmax

---------------------------------------------------------------------
al0l1 ==
    /\ pc="l0"
    /\ pc'="l1"
    /\ 0<x
    /\ x' = x
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ x'=x-1 
  
al2l3 ==
    /\ pc="l2"
    /\ pc'="l3"
    /\ 0 \geq x
    /\ x'=x 
    
al2l1 ==
    /\ pc="l2"
    /\ pc'="l1"
    /\ 0  <  x
    /\ x'=x 
al0l3 ==
    /\ pc="l0"
    /\ pc'="l3"
    /\ 0 \geq x
    /\  x'=x 

 

---------------------    
Next == 
    \/ al0l1 \/ al1l2 \/ al2l3  
    \/ al0l3 \/ al2l1 
    \/ UNCHANGED <<x,pc>>
Init == pc="l0" /\ x=x0
----------------------
inv ==
    /\ typeInt(x)
    /\ pc \in {"l0","l1","l2","l3"} 
    /\ pc="l0" =>  x=x0 /\ x0 \in Nat
    /\ pc="l1" => 0 < x /\ x \leq x0 /\ x0 \in Nat
    /\ pc="l2" => 0 \leq x  /\  x  < x0 /\ x0 \in Nat
    /\ pc="l3" => x = 0 
saferte ==   D(x)
     
safepc ==  pc="l3" => x=0 

safe == safepc /\ saferte /\ inv

=============================================================================
\* Modification History
\* Last modified Mon Oct 02 17:44:48 CEST 2023 by mery
\* Created Wed Sep 09 18:19:08 CEST 2015 by mery
