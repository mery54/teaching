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
l1: assert x=10 /\ z=2*x /\ y = z + x;
y:=z+x;
l2: assert x = 10 /\ y = x + 2*10;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "18d45d79" /\ chksum(tla) = "85f2b28f")
VARIABLES x, z, y, pc

vars == << x, z, y, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ z = z0
        /\ y = y0
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(x=10 /\ z=2*x /\ y = z + x, 
                "Failure of assertion at line 15, column 5.")
      /\ y' = z+x
      /\ pc' = "l2"
      /\ UNCHANGED << x, z >>

l2 == /\ pc = "l2"
      /\ Assert(x = 10 /\ y = x + 2*10, 
                "Failure of assertion at line 17, column 5.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, z, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ l2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

\* ASSUME pre


MAX == 32767  (* 16 bits *)
D == -32768..32767
(*  x \leq 32760 *)

DD(X) == (X \in D)

inv ==
    /\ pc \in {"l1","l2","Done"}
    /\ x \in Int /\ y \in Int /\ z \in Int
    /\ pc="l1" =>  x=10 /\  z=2*x /\ y=z+x
    /\ pc="l2" =>   x=10 /\ y=x+2*10
    /\ pc="Done" =>   x=10 /\ y=x+2*10
    
Safety_Partial_Correctness == pc="Done" =>   x=10 /\ y=x+2*10

Safety_rte ==  DD(x)  /\ DD(y) /\  DD(z) 

check == inv /\ Safety_Partial_Correctness /\ Safety_rte 

prop == [] (x=x0)




=========
