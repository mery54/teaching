--------- MODULE appex4_1_1 --------
EXTENDS Integers,TLC
--------------------------------------------------------------
CONSTANTS x0,y0,z0

pre == x0=10 /\ z0=2*x0 /\ y0=z0+x0
L == {"l1","l2"}

ASSUME pre
(*  *)
(*
--algorithm  test  {
variables x=x0,z=z0,y=y0;
{
l1: y:=z+x;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "66c6fc76" /\ chksum(tla) = "678ca025")
VARIABLES x, z, y, pc

vars == << x, z, y, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ z = z0
        /\ y = y0
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ y' = z+x
      /\ pc' = "Done"
      /\ UNCHANGED << x, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


\* ASSUME pre


MAX == 32767  (* 16 bits *)
D == -32768..32767
(*  x \leq 32760 *)

DD(X) == (X \in D)

Inv ==
    /\ pc \in {"l1","Done"}
    /\ x \in Int /\ y \in Int /\ z \in Int
    /\ pc="l1" =>  x=10 /\  z=2*x /\ y=z+x
    /\ pc="Done" =>   x=10 /\ y=x+2*10
    
Safety_Partial_Correctness == pc="Done" =>   x=10 /\ y=x+2*10

Safety_rte ==  DD(x)  /\ DD(y) /\  DD(z) 

check == Inv /\ Safety_Partial_Correctness /\ Safety_rte 

prop == [] (x=x0)




=========
