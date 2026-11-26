--------- MODULE pluscal_ex3 --------
EXTENDS Integers,TLC
CONSTANTS  p,q,r,u
\* ASSUME (p+q)*(p+q)=r
--------------------------------------------------------------

(*
--algorithm  test {
variables x=p^2,y=q^2,z;
{
l1:assert  x=p^2 /\ y=q*q  ;
z:=x+y+2*p*q;
l2:assert  z=r; 

l3:print <<x,y,z>>;
}
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

Init == (* Global variables *)
        /\ x = p^2
        /\ y = q^2
        /\ z = defaultInitValue
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(x=p^2 /\ y=q*q, "Failure of assertion at line 11, column 4.")
      /\ z' = x+y+2*p*q
      /\ pc' = "l2"
      /\ UNCHANGED << x, y >>

l2 == /\ pc = "l2"
      /\ Assert(z=r, "Failure of assertion at line 13, column 4.")
      /\ pc' = "l3"
      /\ UNCHANGED << x, y, z >>

l3 == /\ pc = "l3"
      /\ PrintT(<<x,y,z>>)
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
