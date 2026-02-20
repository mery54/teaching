------------------- MODULE gcd -----------------
EXTENDS gcddef,Naturals,TLC
CONSTANTS x0,y0
VARIABLES  x,y
-----------------------------------
ASSUME x0 \in Nat /\ y0 \in Nat
Init == x=x0 /\ y=y0
-----------------------------------
(* actions *)
a1 ==
   /\ x > y 
    /\ x'=x-y
    /\ y'=y
a2 == x < y /\ y'=y-x /\ x'=x
over == x=y /\ x'=x /\ y'=y
------------------------------------
Next == a1 \/ a2  \/ over 
------------------------------------
(* Safety properties to be verified *)
TypeOK ==
       /\ x \in Int
       /\ y \in Int
Inv == GCD(x,y)=GCD(x0,y0)       
=============================================



