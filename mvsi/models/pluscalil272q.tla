---------------------------- MODULE pluscalil272q ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS l,r
ASSUME .....
(*
--algorithm ex3
variables i = 0, j = 0,k,halt1=FALSE,halt2=FALSE;

process one = 1
begin
wi:while i < 10 do
	  i: assert i \in A1  /\ i+j \in B1;
      	  i := i+1;
end while;
final1: halt1 := TRUE;
end process;

process two = 2
begin
wj:while i+j  < 10 do
	  j: assert j \in A2 /\ i+j \in B2;
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

=============================================================================
