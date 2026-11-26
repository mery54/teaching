--------- MODULE pluscal_ex2 --------
EXTENDS Integers,TLC
CONSTANTS p,u  (* p is the input *)

--------------------------------------------------------------

(*
--algorithm  test {
variables x=p^3,z=u^3, y=p*u*(p+u) ;
{
l1:assert x=p^3 /\  y=p*u*(p+u)  /\  z = u^3;
y := 3*y+x+z;
l2:assert y=(p+u)^3; 

l3:print <<x,y,z>>;
}
}
*)
\* BEGIN TRANSLATION
VARIABLES x, z, y, pc

vars == << x, z, y, pc >>

Init == (* Global variables *)
        /\ x = p^3
        /\ z = u^3
        /\ y = p*u*(p+u)
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(x=p^3 /\  y=p*u*(p+u)  /\  z = u^3, 
                "Failure of assertion at line 11, column 4.")
      /\ y' = 3*y+x+z
      /\ pc' = "l2"
      /\ UNCHANGED << x, z >>

l2 == /\ pc = "l2"
      /\ Assert(y=(p+u)^3, "Failure of assertion at line 13, column 4.")
      /\ pc' = "l3"
      /\ UNCHANGED << x, z, y >>

l3 == /\ pc = "l3"
      /\ PrintT(<<x,y,z>>)
      /\ pc' = "Done"
      /\ UNCHANGED << x, z, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ l2 \/ l3
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION



MAX == 32768  (* 16 bits *)
D == 0..MAX
(*  x \leq 32768 *)
DD(X) ==  ( X # u =>  X \in D)
init(X) ==  ( X # u)

Safety_absence ==  DD(x)  /\ DD(y)

Safety_partialcorrectness == pc="Done" =>  x= 5*2^{p} /\   y = 2^{p+1}

Inv == 
    /\ pc \in {"l1","l2","Done"}
    /\  (init(x) /\ init(y)) => (x \in Nat /\ y \in Nat)
    /\ pc = "l1" => x=2^p /\ y=2^(p+1) /\ x*y=2^(2*p+1)
    /\ pc = "l2" => x= 5*2^p /\   y = 2^(p+1)
    /\ Safety_partialcorrectness 

check ==  
    /\ Safety_absence
    /\ Safety_partialcorrectness
    /\ Inv

=========
