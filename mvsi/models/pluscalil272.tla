---------------------------- MODULE pluscalil272 ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS l,r

ASSUME l \leq r
(*
--algorithm ex3
variables i = 0, j = 0,k,halt1=FALSE,halt2=FALSE;

process one = 1
begin
wi:while i < 10 do
	  i: assert i \in 0..10 /\ i+j \in 0..20;
      	  i := i+1;

end while;
final1: halt1 := TRUE;
end process;

process two = 2
begin
wj:while i+j  < 10 do
	  j: assert j \in 0..10 /\ i+j \in 0..20;
      j := j+1;
end while;
final2: halt2 := TRUE;
  end process;

process three = 3
begin
w3:  await halt1=TRUE /\ halt2=TRUE;
final3: k := i + j;
check: assert k \in l..r
end process



end algorithm; 

*)
\* BEGIN TRANSLATION (chksum(pcal) = "9415a1ed" /\ chksum(tla) = "20ea6a7e")
\* Label i of process one at line 13 col 14 changed to i_
\* Label j of process two at line 23 col 14 changed to j_
CONSTANT defaultInitValue
VARIABLES i, j, k, halt1, halt2, pc

vars == << i, j, k, halt1, halt2, pc >>

ProcSet == {1} \cup {2} \cup {3}

Init == (* Global variables *)
        /\ i = 0
        /\ j = 0
        /\ k = defaultInitValue
        /\ halt1 = FALSE
        /\ halt2 = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "wi"
                                        [] self = 2 -> "wj"
                                        [] self = 3 -> "w3"]

wi == /\ pc[1] = "wi"
      /\ IF i < 10
            THEN /\ pc' = [pc EXCEPT ![1] = "i_"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "final1"]
      /\ UNCHANGED << i, j, k, halt1, halt2 >>

i_ == /\ pc[1] = "i_"
      /\ Assert(i \in 0..10 /\ i+j \in 0..20, 
                "Failure of assertion at line 13, column 14.")
      /\ i' = i+1
      /\ pc' = [pc EXCEPT ![1] = "wi"]
      /\ UNCHANGED << j, k, halt1, halt2 >>

final1 == /\ pc[1] = "final1"
          /\ halt1' = TRUE
          /\ pc' = [pc EXCEPT ![1] = "Done"]
          /\ UNCHANGED << i, j, k, halt2 >>

one == wi \/ i_ \/ final1

wj == /\ pc[2] = "wj"
      /\ IF i+j  < 10
            THEN /\ pc' = [pc EXCEPT ![2] = "j_"]
            ELSE /\ pc' = [pc EXCEPT ![2] = "final2"]
      /\ UNCHANGED << i, j, k, halt1, halt2 >>

j_ == /\ pc[2] = "j_"
      /\ Assert(j \in 0..10 /\ i+j \in 0..20, 
                "Failure of assertion at line 23, column 14.")
      /\ j' = j+1
      /\ pc' = [pc EXCEPT ![2] = "wj"]
      /\ UNCHANGED << i, k, halt1, halt2 >>

final2 == /\ pc[2] = "final2"
          /\ halt2' = TRUE
          /\ pc' = [pc EXCEPT ![2] = "Done"]
          /\ UNCHANGED << i, j, k, halt1 >>

two == wj \/ j_ \/ final2

w3 == /\ pc[3] = "w3"
      /\ halt1=TRUE /\ halt2=TRUE
      /\ pc' = [pc EXCEPT ![3] = "final3"]
      /\ UNCHANGED << i, j, k, halt1, halt2 >>

final3 == /\ pc[3] = "final3"
          /\ k' = i + j
          /\ pc' = [pc EXCEPT ![3] = "check"]
          /\ UNCHANGED << i, j, halt1, halt2 >>

check == /\ pc[3] = "check"
         /\ Assert(k \in l..r, "Failure of assertion at line 33, column 8.")
         /\ pc' = [pc EXCEPT ![3] = "Done"]
         /\ UNCHANGED << i, j, k, halt1, halt2 >>

three == w3 \/ final3 \/ check

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == one \/ two \/ three
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

A == {}
B == {}
Safe ==   (\A self \in ProcSet: pc[self] = "Done") => i \in A /\ j \in B

=============================================================================
