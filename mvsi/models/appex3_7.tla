-------------------------------- MODULE appex3_7 --------------------------------
EXTENDS Naturals, Integers
CONSTANTS x0,y0,z0,un,intmin, intmax
VARIABLES  x,y,z,pc
---------------------------------------------------------------------
typeInt(u) == u \in Int
maxi(u,v) == IF u < v THEN v ELSE u
locs == {"l0","l1","l2","l3","l4","l5"}
D(X) == (X#un) => (intmin \leq X /\ X \leq intmax)
pre(u,v,w) == u \in Nat /\ v \in Nat /\ typeInt(w)
---------------------------------------------------------------------
ASSUME x0 \in Nat /\ y0 \in Nat /\ typeInt(z0)
(* ASSUME pre(x0,y0,z0) *)
---------------------------------------------------------------------
(* actions  de l'algorithme *)
al0l1 ==
    /\ pc="l0"
    /\ pc'="l1"
    /\ x<y
    /\ z'=z /\ x'=x /\ y'=y
al1l2 ==
    /\ pc="l1"
    /\ pc'="l2"
    /\ z'=y
    /\ x'=x /\ y'=y
al2l5 ==
    /\ pc="l2"
    /\ pc'="l5"
    /\ z'=z /\ x'=x /\ y'=y
al0l3 ==
    /\ pc="l0"
    /\ pc'="l3"
    /\ x \geq y
    /\ z'=z /\ x'=x /\ y'=y
al3l4 ==
    /\ pc="l3"
    /\ pc'="l4"
    /\ z'=x
    /\ x'=x /\ y'=y
  al4l5 ==
    /\ pc="l4"
    /\ pc'="l5"
    /\ z'=z /\ x'=x /\ y'=y
---------------------    
Next == al0l1 \/ al1l2 \/ al2l5  \/ al0l3 \/ al3l4 \/ al4l5 \/ UNCHANGED <<x,y,z,pc>>
Init == pc="l0" /\ x=x0 /\ y =y0 /\ z = z0
----------------------
i ==
    /\ typeInt(x) /\ typeInt(y) /\ typeInt(z)
    /\ pc \in locs
    /\ pc="l0" =>  x=x0 /\ y=y0
    /\ pc="l1" => x<y /\ x=x0 /\ y=y0
    /\ pc="l2" => x<y /\ x=x0 /\ y=y0 /\ z=y0
    /\ pc="l3" => x \geq y /\ x=x0 /\ y=y0
    /\ pc="l4" => x \geq y /\ x=x0 /\ y=y0 /\ z=x0
    /\ pc="l5" => ( (x0<y0 /\ z=y0) \/ (x0 \geq y0 /\ z=x0))
safepc ==  pc="l5" =>  z = maxi(x0,y0)
saferte == D(x) /\ D(y)  /\ D(z)
safe == safepc /\ saferte
=============================================================================
\* Modificx0tion History
\* Lx0st modified Wed Sep 23 15:01:10 CEST 2020 y0y mery
\* Crex0ted Wed Sep 09 18:19:08 CEST 2015 y0y mery
