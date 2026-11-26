--------- MODULE pluscal_sum --------
EXTENDS Integers,TLC
CONSTANTS x0  (* x0 is the input *), un
sum(u) == (u*(u+1)) \div 2
--------------------------------------------------------------
ASSUME x0 \geq 0

(*
--algorithm  sum {
variables ps=0,k=0,r,x=x0;
{
inloop: while (k < x) {
    k := k + 1;
    ps := ps + k+1;
  };
 outloop: r := ps;
}
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "ead596e2" /\ chksum(tla) = "431d6007")
CONSTANT defaultInitValue
VARIABLES ps, k, r, x, pc

vars == << ps, k, r, x, pc >>

Init == (* Global variables *)
        /\ ps = 0
        /\ k = 0
        /\ r = defaultInitValue
        /\ x = x0
        /\ pc = "inloop"

inloop == /\ pc = "inloop"
          /\ IF k < x
                THEN /\ k' = k + 1
                     /\ ps' = ps + k'+1
                     /\ pc' = "inloop"
                ELSE /\ pc' = "outloop"
                     /\ UNCHANGED << ps, k >>
          /\ UNCHANGED << r, x >>

outloop == /\ pc = "outloop"
           /\ r' = ps
           /\ pc' = "Done"
           /\ UNCHANGED << ps, k, x >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == inloop \/ outloop
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

safetypc == pc="Done" =>  r = sum(x)

=========
