--------- MODULE pluscal_minmax--------
EXTENDS Integers,TLC
CONSTANTS x1,x2
--------------------------------------------------------------

ominus(u,v) == IF u <v THEN 0 ELSE u-v
vmax(u,v) == IF u <v THEN v ELSE u
vmin(u,v) == IF u <v THEN u ELSE v

(*
--algorithm  minmax  {
variables y1=x1,y2=x2,z1=x1,z2=x2;
{
l1: y1:= ominus(z1,ominus(z1,z2));
l2: y2:= ominus(z1, ominus(z2,z1));
l3: z1:=y1;
l4: z2:=y2;
l5:print <<x1,x2,z1,z2>>;
}
}
}
*)
\* BEGIN TRANSLATION
VARIABLES y1, y2, z1, z2, pc

vars == << y1, y2, z1, z2, pc >>

Init == (* Global variables *)
        /\ y1 = x1
        /\ y2 = x2
        /\ z1 = x1
        /\ z2 = x2
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ y1' = ominus(z1,ominus(z1,z2))
      /\ pc' = "l2"
      /\ UNCHANGED << y2, z1, z2 >>

l2 == /\ pc = "l2"
      /\ y2' = ominus(z1, ominus(z2,z1))
      /\ pc' = "l3"
      /\ UNCHANGED << y1, z1, z2 >>

l3 == /\ pc = "l3"
      /\ z1' = y1
      /\ pc' = "l4"
      /\ UNCHANGED << y1, y2, z2 >>

l4 == /\ pc = "l4"
      /\ z2' = y2
      /\ pc' = "l5"
      /\ UNCHANGED << y1, y2, z1 >>

l5 == /\ pc = "l5"
      /\ PrintT(<<x1,x2,z1,z2>>)
      /\ pc' = "Done"
      /\ UNCHANGED << y1, y2, z1, z2 >>

Next == l1 \/ l2 \/ l3 \/ l4 \/ l5
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION




MAX == 32768  (* 16 bits *)
D == 0..32768
(*  x \leq 32760 *)
(*
DD(X) == (X # defaultInitValue => X \in D)

Safety_absence ==  DD(y1)  /\ DD(y2) /\ DD(y3) /\ DD(z)

*)

safety == pc="Done" => (z1=vmin(x1,x2) /\ z2=vmax(x1,x2))




=========


