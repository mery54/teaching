------------------------- MODULE pluscalconcurrent -------------------------
EXTENDS Integers, TLC,Sequences
-----------------------
(*
--algorithm ExConcurrent1
variables x   = 0;
process (P \in {1,2})
variables localx;
begin
   l1:localx:=self;
   l2:x:=x+localx;
   l3:await x = 3;
end process;

end algorithm;
*)




=============================================================================
\* Modification History
\* Last modified Mon Jan 19 21:51:18 CET 2026 by mery
\* Created Mon Jan 19 21:45:45 CET 2026 by mery
