-------------------------------- MODULE malgtd1ex11 --------------------------------
EXTENDS Naturals, Integers
CONSTANTS x0,y0,z0,mini0,maxi0
VARIABLES  x,y,z,pc
typeInt(u) == u \in Int
maxi(u,v) == IF u < v THEN v ELSE u
pre ==  x0 \in Nat /\ y0 \in Nat /\ z0 \in Int
ASSUME pre
---------------------------------------------------------------------
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
    /\ UNCHANGED <<z,x,y>>
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
    /\ pc="l0" =>  x=x0 /\ y=y0 /\ z=z0 /\ pre
    /\ pc="l1" => x<y /\ x=x0 /\ y=y0 /\ z=z0 /\ pre
    /\ pc="l2" => x<y /\ x=x0 /\ y=y0 /\ z=y0 /\ pre
    /\ pc="l3" => x \geq y /\ x=x0 /\ y=y0 /\ z=z0 /\ pre
    /\ pc="l4" => x \geq y /\ x=x0 /\ y=y0 /\ z=x0  /\ pre
    /\ pc="l5" => z = maxi(x0,y0) /\ x=x0 /\ y=y0  /\ pre
safepc ==  pc="l5" =>  z = maxi(x0,y0)
safeab == x=x0 /\ y=y0
saferte == 
    /\ mini0 <= x /\ x <= maxi0
    /\ mini0 <= y /\ y <= maxi0
=============================================================================
\* Modification History
\* Last modified Wed Feb 08 10:52:27 CET 2023 by mery
\* Created Wed Sep 09 18:19:08 CEST 2015 by mery
