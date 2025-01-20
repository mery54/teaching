------------- MODULE malgtd1ex10 --------------------------------
EXTENDS Naturals, Integers, TLC, TLAPS
CONSTANTS x0,y0,z0
VARIABLES  x,y,z,pc
-------------------------------------------------------------------------------
(* Auxiliary definitions *)
typeInt(u) == u \in Int
pre(u,v,w) == 
    /\ u \in Int /\ v \in Int /\ w \in Int
    /\  u=3 /\ v=w+u /\ w=2*u
       
L == {"l1","l2"}

ppre == pre(x0,y0,z0)
------------------------------------------------------------------------------
(* Interpretation: we assume that the precondition can hold and we have to find possible values for x0,y0, z0 to validate or not *)
ASSUME   ppre
---------------------------------------------------------------------
(* Action for transition of the algorithm *)
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ y'=z+x
    /\ z'=z /\ x'=x
---------------------------------------------------------------
(* Computations *)
vars ==  <<x,y,z,pc>>
Next == al1l2  \/ UNCHANGED vars
Init == pc="l0" /\ x=x0 /\ y =y0 /\ z = z0  /\ pre(x0,y0,z0)
----------------------
(* Checking the annotation by checking the invariant i derived from the annotation *)
i ==
    /\ typeInt(x) /\ typeInt(y) /\ typeInt(z) /\ pc \in  L
    /\ pc="l1" =>  x=x0 /\ y=y0 /\ z=z0 /\ pre(x0,y0,z0)
    /\ pc="l2" =>  x=3 /\ y = x +6 /\ pre(x0,y0,z0)

Safe ==  i


Spec == Init /\ [][Next]_vars

=============================================================================
