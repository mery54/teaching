--------- MODULE appex4_1_3 --------
EXTENDS Integers,TLC

--------------------------------------------------------------
CONSTANTS x0,y0

pre == x0=1 /\ y0=12

(*

--algorithm  test  {
variables x=x0,y=y0;
{
l1:assert x=1 /\ y=12;
x:=2*y;
l2:assert x=24 /\ y=12;
}
}
*)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ y = y0
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(x=1 /\ y=12, "Failure of assertion at line 14, column 4.")
      /\ x' = 2*y
      /\ pc' = "l2"
      /\ y' = y

l2 == /\ pc = "l2"
      /\ Assert(x=24 /\ y=12, "Failure of assertion at line 16, column 4.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ l2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION




MAX == 32768  (* 16 bits *)
D == 0..32768
(*  x \leq 32760 *)

DD(X) == ( X \in D)

Safety_absence ==  DD(x)  /\ DD(y) 


Inv ==
    /\ pc="l1" =>  x=1 /\ y=12
    /\ pc="l2" =>  x=1 /\ y=24

=========
