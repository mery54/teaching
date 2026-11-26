----------------------------- MODULE pluscal253 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS n

(*

--algorithm ex3{ 
variables x = 1..n,y,s=0;


process (one = 1)
{
  A: await x = {} ;
  D: assert x={};   
};

process (Q = 2)
{
  E: while (x # {})
  {
    F:y := CHOOSE v \in 1..n: v \in x; 
    G: s  := s + y;
    print <<y,x>>;
    H: x := x  \  {y};
  };
  
};

}
end algorithm; 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "45cecbe4" /\ chksum(tla) = "f27a7731")
CONSTANT defaultInitValue
VARIABLES x, y, s, pc

vars == << x, y, s, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ x = 1..n
        /\ y = defaultInitValue
        /\ s = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "A"
                                        [] self = 2 -> "E"]

A == /\ pc[1] = "A"
     /\ x = {}
     /\ pc' = [pc EXCEPT ![1] = "D"]
     /\ UNCHANGED << x, y, s >>

D == /\ pc[1] = "D"
     /\ Assert(x={}, "Failure of assertion at line 14, column 6.")
     /\ pc' = [pc EXCEPT ![1] = "Done"]
     /\ UNCHANGED << x, y, s >>

one == A \/ D

E == /\ pc[2] = "E"
     /\ IF x # {}
           THEN /\ pc' = [pc EXCEPT ![2] = "F"]
           ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
     /\ UNCHANGED << x, y, s >>

F == /\ pc[2] = "F"
     /\ y' = (CHOOSE v \in 1..n: v \in x)
     /\ pc' = [pc EXCEPT ![2] = "G"]
     /\ UNCHANGED << x, s >>

G == /\ pc[2] = "G"
     /\ s' = s + y
     /\ PrintT(<<y,x>>)
     /\ pc' = [pc EXCEPT ![2] = "H"]
     /\ UNCHANGED << x, y >>

H == /\ pc[2] = "H"
     /\ x' = x  \  {y}
     /\ pc' = [pc EXCEPT ![2] = "E"]
     /\ UNCHANGED << y, s >>

Q == E \/ F \/ G \/ H

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ Q
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

P1 == pc[1]="Done" => x={}
P2 == pc[2]="Done" => s = (n*(n+1)) \div  2


====
