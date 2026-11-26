---------------------- MODULE contrat1  --------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT x0,y0,z0,c0,r0

(*
-termination
-wfNext
--algorithm contreat1 {
  variables x,y,z,c,r;
{
    l1: assert x == 49 /\ z ==  2*c /\ y == (z+1)*(z+1);
    y= x+z+1;
    l2: assert x == 49 /\ z ==  2*c /\ y ==  (c+1)*(c+1);
}
*)

==================================================================
\* Modification History
\* Last modified Mon Oct 03 09:02:48 CEST 2016 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
