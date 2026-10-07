--------- MODULE appex4_1_1 --------
EXTENDS Integers,TLC
--------------------------------------------------------------
CONSTANTS x0,y0,z0
--------------------------------------------------------------
pre(a,b,c)  == a=10 /\ c=2*a /\ b=c+a
--------------------------------------------------------------
(* Verifying the existence of a triple that satisfies pre(x0;y0,z0) *)
ASSUME pre(x0,y0,z0)
--------------------------------------------------------------
(*
--algorithm  test  {
variables x=x0,z=z0,y=y0,t;
{
l1:\* assert x=10 /\ z=2*x /\ y = z + x;
y:=z+x;
l2: \* assert x = 10 /\ y = x + 2*10
    skip ;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "cec661f" /\ chksum(tla) = "51e99e7b")
CONSTANT defaultInitValue
VARIABLES x, z, y, t, pc

vars == << x, z, y, t, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ z = z0
        /\ y = y0
        /\ t = defaultInitValue
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ y' = z+x
      /\ pc' = "l2"
      /\ UNCHANGED << x, z, t >>

l2 == /\ pc = "l2"
      /\ TRUE
      /\ pc' = "Done"
      /\ UNCHANGED << x, z, y, t >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ l2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

\* ASSUME pre
--------------------------------------------------------------
(* premiminaries for checking  on  pssible values *)
MAX == 32767  (* 16 bits *)
D == -32768..32767
DD(X) ==  (X # defaultInitValue) => (X \in D)
--------------------------------------------------------------
Inv ==
    /\ pc \in {"l1","l2","Done"}
    /\ x \in Int /\ y \in Int /\ z \in Int
    /\ pc="l1" =>  x=10 /\  z=2*x /\ y=z+x
    /\ pc="l2" =>   x=10 /\ y=x+2*10
    /\ pc="Done" =>   x=10 /\ y=x+2*10
Safety_Partial_Correctness == pc="Done" =>   x=10 /\ y=x+2*10
Safety_rte ==  DD(x)  /\ DD(y) /\  DD(z) /\ DD(t) 
check == Inv /\ Safety_Partial_Correctness /\ Safety_rte 
prop == [] (x=x0)
=============================================
