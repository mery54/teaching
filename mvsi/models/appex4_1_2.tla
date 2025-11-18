--------- MODULE appex4_1_2 --------
EXTENDS Integers, Naturals,TLC
CONSTANTS x0,y0,p,maxi 
--------------------------------------------------------------
diviseurs(n) == { m \in 1..maxi:  n % m = 0 }
premier(n) ==  diviseurs(n) = {1,n} /\ n # 1 

pre == x0=2^p /\ y0=2^(p+1) /\ x0*y0=2^(2*p+1)

ASSUME premier(p) /\ pre
(*

--algorithm  test  {
variables x=x0,y=y0;
{
l1:assert x=2^p /\ y=(2^p)*2 /\  x*y=2^(2*p+1);
x:=y+x+(2^x);
l2:assert x=5*(2^p) /\ y=2^(p+1) ;
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
      /\ Assert(x=2^p /\ y=(2^p)*2 /\  x*y=2^(2*p+1), 
                "Failure of assertion at line 16, column 4.")
      /\ x' = y+x+(2^x)
      /\ pc' = "l2"
      /\ y' = y

l2 == /\ pc = "l2"
      /\ Assert(x=5*(2^p) /\ y=2^(p+1), 
                "Failure of assertion at line 18, column 4.")
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
    /\ pc="l1" => x=2^p /\ y=2^p*2 /\  x*y=2^(2*p+1)
    /\ pc="l2" =>    x=5*2^p /\ y=2^(p+1)

=========
