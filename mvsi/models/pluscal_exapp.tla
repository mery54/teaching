--------------------- MODULE pluscal_exapp --------------------------------
EXTENDS Naturals, Integers, TLC

(*
--algorithm max {
  variables x=a, 
            y = b, 
            z;
            
{


(*
--algorithm  ex1{
variables   u=5;
            v=u+7;
{
  l1: u:=u+v+5;
  l2: v:=v+u;
  l3: skip;
}
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

Init == (* Global variables *)
        /\ x = a
        /\ y = b
        /\ z = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ Assert(x=a /\ y=b, "Failure of assertion at line 16, column 5.")
      /\ IF x < y
            THEN /\ pc' = "l1"
            ELSE /\ pc' = "l3"
      /\ UNCHANGED << x, y, z >>

l1 == /\ pc = "l1"
      /\ Assert(x=a /\ y=b /\ x<y, 
                "Failure of assertion at line 18, column 8.")
      /\ z' = y
      /\ pc' = "l2"
      /\ UNCHANGED << x, y >>

l2 == /\ pc = "l2"
      /\ Assert(x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z, 
                "Failure of assertion at line 20, column 7.")
      /\ pc' = "l5"
      /\ UNCHANGED << x, y, z >>

l3 == /\ pc = "l3"
      /\ Assert(x=a /\ y=b /\  x >= y, 
                "Failure of assertion at line 24, column 6.")
      /\ z' = x
      /\ pc' = "l4"
      /\ UNCHANGED << x, y >>

l4 == /\ pc = "l4"
      /\ Assert(x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z, 
                "Failure of assertion at line 26, column 6.")
      /\ pc' = "l5"
      /\ UNCHANGED << x, y, z >>

l5 == /\ pc = "l5"
      /\ Assert(z \in  {a,b} /\ a <= z /\ b <= z, 
                "Failure of assertion at line 28, column 6.")
      /\ PrintT("done")
      /\ pc' = "l6"
      /\ UNCHANGED << x, y, z >>

l6 == /\ pc = "l6"
      /\ Assert(z \in  {a,b} /\ a <= z /\ b <= z, 
                "Failure of assertion at line 30, column 6.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, y, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

ISDEF(X,Y) == X # defaultInitValue => X \in Y
Inv ==
    /\ pc \in {"l0","l1","l2","l3","l4","l5","l6","Done"}
    /\ ISDEF(x,Int)  /\ ISDEF(x,Int) /\ ISDEF(z,Int)
    /\ pc="l0" => x=a /\ y=b
    /\ pc = "l1"  => x=a /\ y=b /\ x<y
    /\ pc = "l2" => x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "l3" => x=a /\ y=b /\  x >= y 
    /\ pc = "l4" => x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "l5" => z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "l6" => z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "Done" => z \in  {a,b} /\ a <= z /\ b <= z
    
DD(X) == X # defaultInitValue => X \in min..max

safetyrte ==DD(x) /\ DD(y) /\ DD(z)


safetypc == pc="Done" =>  z \in  {a,b} /\ a <= z /\ b <= z
==================================================================
\* Modification History
\* Last modified Fri Nov 20 09:16:07 CET 2020 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
