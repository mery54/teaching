--------- MODULE pluscal_alg_stat1 --------
EXTENDS Integers,TLC
CONSTANTS p,u  (* p is the input *)

--------------------------------------------------------------

(*
--algorithm  test {
variables x=2^p,y=2*2^p;
{
l1:assert x=2^p /\ y=2^(p+1) /\ x*y=2^(2*p+1);
x:=2*y;
l2:assert  x= 5*2^p /\   y = 2^(p+1);    

l3:print <<x,y>>;
}
}
*)



\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = 2^p
        /\ y = 2*2^p
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(x=2^p /\ y=2^(p+1) /\ x*y=2^(2*p+1), 
                "Failure of assertion at line 11, column 4.")
      /\ x' = 2*y
      /\ pc' = "l2"
      /\ y' = y

l2 == /\ pc = "l2"
      /\ Assert(x= 5*2^p /\   y = 2^(p+1), 
                "Failure of assertion at line 13, column 4.")
      /\ pc' = "l3"
      /\ UNCHANGED << x, y >>

l3 == /\ pc = "l3"
      /\ PrintT(<<x,y>>)
      /\ pc' = "Done"
      /\ UNCHANGED << x, y >>

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
