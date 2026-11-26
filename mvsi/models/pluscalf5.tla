--------------------- MODULE pluscal_max --------------------------------
EXTENDS Naturals, Integers, TLC
---------------------------------------------------------------------------
CONSTANTS a,b,min,max
---------------------------------------------------------------------------
x0 == a
y0 == b
pre == a \in min..max /\ b \in min..max 
maxi(u,v) == IF u < v THEN v ELSE u
--------------------------------------------------------------------------------
ASSUME pre
----------------------------------------------------------------------
(*
--algorithm max {
  variables ps=0, 
            k = 0, 
            z;
  int ps = 0;
  int k = 0;
  int ok=k, ops = 0;
  while (k < n) {
 /*@ assert 0 <= k && k <= n 
   && ps == S(k) && ops == S(ok);   */    
    ok=k;ops=ps;
    k = ok + 1;
    ps = ops + k;
 /*@ assert 0 <= k && k <= n && ps == S(k) 
   && ops == S(ok);   */        
  };
  return ps;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "c20ccd52" /\ chksum(tla) = "cb62c94")
CONSTANT defaultInitValue
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

Init == (* Global variables *)
        /\ x = a
        /\ y = b
        /\ z = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ Assert(x=a /\ y=b /\ pre, 
                "Failure of assertion at line 20, column 5.")
      /\ IF x < y
            THEN /\ pc' = "l1"
            ELSE /\ pc' = "l3"
      /\ UNCHANGED << x, y, z >>

l1 == /\ pc = "l1"
      /\ Assert(x=a /\ y=b /\ x<y  /\ pre, 
                "Failure of assertion at line 22, column 8.")
      /\ z' = y
      /\ pc' = "l2"
      /\ UNCHANGED << x, y >>

l2 == /\ pc = "l2"
      /\ Assert(x=a /\ y=b /\ z=y /\ pre, 
                "Failure of assertion at line 24, column 7.")
      /\ pc' = "l5"
      /\ UNCHANGED << x, y, z >>

l3 == /\ pc = "l3"
      /\ Assert(x=a /\ y=b /\  x >= y  /\ pre, 
                "Failure of assertion at line 28, column 6.")
      /\ z' = x
      /\ pc' = "l4"
      /\ UNCHANGED << x, y >>

l4 == /\ pc = "l4"
      /\ Assert(x=a /\ y=b /\ z = x /\ pre, 
                "Failure of assertion at line 30, column 6.")
      /\ pc' = "l5"
      /\ UNCHANGED << x, y, z >>

l5 == /\ pc = "l5"
      /\ Assert(z=maxi(a,b) /\ pre, 
                "Failure of assertion at line 32, column 6.")
      /\ PrintT("done")
      /\ pc' = "l6"
      /\ UNCHANGED << x, y, z >>

l6 == /\ pc = "l6"
      /\ Assert(z = maxi(a,b)  /\ pre, 
                "Failure of assertion at line 34, column 6.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, y, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 


-----------------------------------------------------------------------------
(* properties  for checking the algorithm *)
ISDEF(X,Y) == X # defaultInitValue => X \in Y
Inv ==
    /\ pc \in {"l0","l1","l2","l3","l4","l5","l6","Done"}
    /\ ISDEF(x,Int)  /\ ISDEF(y,Int) /\ ISDEF(z,Int)
    /\ pc="l0" => x=a /\ y=b
    /\ pc = "l1"  => x=a /\ y=b /\ x<y
    /\ pc = "l2" => x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "l3" => x=a /\ y=b /\  x >= y 
    /\ pc = "l4" => x=a /\ y=b /\ z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "l5" => z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "l6" => z \in  {a,b} /\ a <= z /\ b <= z
    /\ pc = "Done" => z \in  {a,b} /\ a <= z /\ b <= z
DD(X) == X # defaultInitValue => X \in min..max
-----------------------------------------------------------------------------
(* RTE Run Time Errors   *)
SafetyRTE ==DD(x) /\ DD(y) /\ DD(z)
(* PC Partial Correctness  *)
SafetyPC == pc="Done" =>  z = maxi(a,b)
SafetySpecific == [] (x=a /\ y=b)
check == SafetyPC /\ SafetyRTE
prop == SafetySpecific 
==================================================================
\* Modification History
\* Last modified Thu Mar 06 09:00:37 CET 2025 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
