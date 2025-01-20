--------------------- MODULE pluscal_max --------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANTS a,b,min,max
x0 == a
y0 == b

pre == a \in min..max /\ b \in min..max 

ASSUME pre


(*
--algorithm max {
  variables x=a, 
            y = b, 
            z;
            
{
 l0:assert x=a /\ y=b /\ pre;
 if ( x < y ) {
  l1:  assert x=a /\ y=b /\ x<y  /\ pre;
  z:=y;
  l2: assert x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z  /\ pre;
  }
else
{ 
 l3: assert x=a /\ y=b /\  x >= y  /\ pre;
 z:= x;
 l4: assert x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z /\ pre;
 };
 l5: assert z \in  {a,b} /\ a <= z /\ b <= z /\ pre;
 print "done";
 l6: assert z \in  {a,b} /\ a <= z /\ b <= z /\ pre;
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
      /\ Assert(x=a /\ y=b /\ pre, 
                "Failure of assertion at line 20, column 5.")
      /\ IF x < y
            THEN /\ pc' = "l1"
            ELSE /\ pc' = "l3"
      /\ UNCHANGED << x, y, z >>

l1 == /\ pc = "l1"
      /\ Assert(x=a /\ y=b /\ x<y  /\ pre, 
                "Failure of assertion at line 22, column 8.")
      /\ z' = y
      /\ pc' = "l2"
      /\ UNCHANGED << x, y >>

l2 == /\ pc = "l2"
      /\ Assert(x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z  /\ pre, 
                "Failure of assertion at line 24, column 7.")
      /\ pc' = "l5"
      /\ UNCHANGED << x, y, z >>

l3 == /\ pc = "l3"
      /\ Assert(x=a /\ y=b /\  x >= y  /\ pre, 
                "Failure of assertion at line 28, column 6.")
      /\ z' = x
      /\ pc' = "l4"
      /\ UNCHANGED << x, y >>

l4 == /\ pc = "l4"
      /\ Assert(x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z /\ pre, 
                "Failure of assertion at line 30, column 6.")
      /\ pc' = "l5"
      /\ UNCHANGED << x, y, z >>

l5 == /\ pc = "l5"
      /\ Assert(z \in  {a,b} /\ a <= z /\ b <= z /\ pre, 
                "Failure of assertion at line 32, column 6.")
      /\ PrintT("done")
      /\ pc' = "l6"
      /\ UNCHANGED << x, y, z >>

l6 == /\ pc = "l6"
      /\ Assert(z \in  {a,b} /\ a <= z /\ b <= z /\ pre, 
                "Failure of assertion at line 34, column 6.")
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
    /\ ISDEF(x,Int)  /\ ISDEF(y,Int) /\ ISDEF(z,Int)
    /\ pc="l0" => x=a /\ y=b
    /\ pc = "l1"  => x=a /\ y=b /\ x<y
    /\ pc = "l2" => x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "l3" => x=a /\ y=b /\  x >= y 
    /\ pc = "l4" => x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "l5" => z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "l6" => z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "Done" => z \in  {a,b} /\ a <= z /\ b <= z
    
DD(X) == X # defaultInitValue => X \in min..max

SafetyRTE ==DD(x) /\ DD(y) /\ DD(z)


SafetyPC == pc="Done" =>  z \in  {a,b} /\ a <= z /\ b <= z
myprop == [] (x=a /\ y=b)
==================================================================
\* Modification History
\* Last modified Tue Mar 26 10:57:30 CET 2024 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
