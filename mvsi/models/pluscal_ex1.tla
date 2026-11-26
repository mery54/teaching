--------- MODULE pluscal_ex1 --------
EXTENDS Integers,TLC,Naturals
CONSTANTS p0,u  (* p is the input *)

ASSUME p0 \in Nat
--------------------------------------------------------------

(*
--algorithm  test {
variables x=p0,y=3+x;
{
x:= y*y + 2*p0*y+p0*p0 ;
l2:assert x=(2*p0+3)^2 /\  x \in Nat /\ y \in Nat; 

print <<x,y>>;
}
}
*)



MAX == 32768  (* 16 bits *)
D == 0..MAX
(*  x \leq 32768 *)
DD(X) ==  ( X # u =>  X \in D)
init(X) ==  ( X # u)

Safety_absence ==  DD(x)  /\ DD(y)

Safety_partialcorrectness == pc="Done" =>  x= 5*2^{p0} /\   y = 2^{p0+1}

Inv == 
    /\ pc \in {"l1","l2","Done"}
    /\  (init(x) /\ init(y)) => (x \in Nat /\ y \in Nat)
    /\ pc = "l1" => x=2^p /\ y=2^(p0+1) /\ x*y=2^(2*p0+1)
    /\ pc = "l2" => x= 5*2^p0 /\   y = 2^(p0+1)
    /\ Safety_partialcorrectness <
<
Check ==  
    /\ Safety_absence
    /\ Safety_partialcorrectness
    /\ Inv

=========
