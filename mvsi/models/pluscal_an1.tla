--------------------- MODULE pluscal_an1 --------------------------------
EXTENDS Naturals, Integers, TLC
---------------------------------------------------------------------------
CONSTANTS p
---------------------------------------------------------------------------
Divides(i,j) == \E k \in 0..j: j = i * k
DD(x) == { i \in 1..x :  i \in 1..x /\ Divides(i,x)}
prime(x) ==  x # 1 /\ DD(x) ={1,x} 
--------------------------------------------------------------------------------
ASSUME prime(p)
----------------------------------------------------------------------
(*
--algorithm ann {
  variables x=2^p, 
            y = 2^p*2;

{
 l1:assert x=2^p /\ y = 2^p*2 /\ x*y = 2^(2*p+1);
x:= y+x+2^x;
 l2:assert x=5*2^p /\ y = 2^p*2 
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "947472cf" /\ chksum(tla) = "ae59a63")
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = 2^p
        /\ y = 2^p*2
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ Assert(x=2^p /\ y = 2^p*2 /\ x*y = 2^(2*p+1), 
                "Failure of assertion at line 17, column 5.")
      /\ x' = y+x+2^x
      /\ pc' = "l2"
      /\ y' = y

l2 == /\ pc = "l2"
      /\ Assert(x=5*2^p /\ y = 2^p*2, 
                "Failure of assertion at line 19, column 5.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l1 \/ l2
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


-----------------------------------------------------------------------------
inv ==
  /\  pc = "l1" =>  x=2^p /\ y = 2^p*2 /\ x*y = 2^(2*p+1)
  /\  pc = "l2" =>  x=5*2^p /\ y = 2^p*2 

==================================================================
\* Modification History
\* Last modified Thu Mar 06 09:19:36 CET 2025 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
