---------------------- MODULE pluscal_loop --------------------------------
EXTENDS Naturals, Integers, TLC
CONSTANT x0,intmin,intmax
pre(x) == x \in Nat

ASSUME pre(x0)

typeInt(u) == u \in Int  (* u is an integer *)
D(X) == intmin \leq X /\ X \leq intmax

---------


(*
--algorithm  loop{
variables x=x0;
{
 l0: assert  x=x0 /\ x0 \in Nat;
 l00: while (0<x)
  {  l1: assert  0 < x /\ x \leq x0 /\ x0 \in Nat;
     x := x - 1;
     l2: assert  0 \leq x  /\  x  < x0 /\ x0 \in Nat;
     
  }; 
  l3: assert x=0;
}
}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "1ba3a7bf" /\ chksum(tla) = "72103e5b")
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ Assert(x=x0 /\ x0 \in Nat, 
                "Failure of assertion at line 17, column 6.")
      /\ pc' = "l00"
      /\ x' = x

l00 == /\ pc = "l00"
       /\ IF 0<x
             THEN /\ pc' = "l1"
             ELSE /\ pc' = "l3"
       /\ x' = x

l1 == /\ pc = "l1"
      /\ Assert(0 < x /\ x \leq x0 /\ x0 \in Nat, 
                "Failure of assertion at line 19, column 10.")
      /\ x' = x - 1
      /\ pc' = "l2"

l2 == /\ pc = "l2"
      /\ Assert(0 \leq x  /\  x  < x0 /\ x0 \in Nat, 
                "Failure of assertion at line 21, column 10.")
      /\ pc' = "l00"
      /\ x' = x

l3 == /\ pc = "l3"
      /\ Assert(x=0, "Failure of assertion at line 24, column 7.")
      /\ pc' = "Done"
      /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l00 \/ l1 \/ l2 \/ l3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 



-----------------------
inv ==
    /\ typeInt(x)
    /\ pc \in {"l0","l00","l1","l2","l3","Done"} 
    /\ pc="l0" =>  x=x0 /\ x0 \in Nat
    /\ pc="l00" => 0 \leq x  /\  x  \leq x0 /\ x0 \in Nat
    /\ pc="l1" => 0 < x /\ x \leq x0 /\ x0 \in Nat
    /\ pc="l2" => 0 \leq x  /\  x  < x0 /\ x0 \in Nat
    /\ pc="l3" => x = 0 
    /\ pc="Done" => x=0 
saferte ==   D(x)
     
safepc ==  pc="Done" => x=0 

safe == safepc /\ saferte /\ inv

=============================================================================
\* Modif

===============
