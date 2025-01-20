--------- MODULE appex4_1_4 --------
EXTENDS Integers,TLC

--------------------------------------------------------------

(*
--algorithm  test  {
variables x=11,y=13,z;
{
l1:assert x=11 /\ y=13;
z:=x;x:=y;y:=z;
l2:assert x=26 \div 2 /\ y=33 \div 3;

l3:print <<x,y>>;
}
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

Init == (* Global variables *)
        /\ x = 11
        /\ y = 13
        /\ z = defaultInitValue
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(x=11 /\ y=13, "Failure of assertion at line 10, column 4.")
      /\ z' = x
      /\ x' = y
      /\ y' = z'
      /\ pc' = "l2"

l2 == /\ pc = "l2"
      /\ Assert(x=26 \div 2 /\ y=33 \div 3, 
                "Failure of assertion at line 12, column 4.")
      /\ pc' = "l3"
      /\ UNCHANGED << x, y, z >>

l3 == /\ pc = "l3"
      /\ PrintT(<<x,y>>)
      /\ pc' = "Done"
      /\ UNCHANGED << x, y, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ l2 \/ l3
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
    /\ pc="l1" =>  x=11 /\ y=13
    /\ pc="l2" =>  x=26 \div 2 /\ y=33 \div 3

=========
