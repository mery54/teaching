---------------------------- MODULE pluscalil267q ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets


(*
--algorithm ex1{ 
variables x = 1, y = 2;


process (one = 1)
{
  A:
    x := x + 1;
  B: 
    y := y -1;  
  C:
      assert  x \in A1 /\ y \in B1;
};

process (two = 2)
{
  D:
    x := x - 1;
  E:
    y:=y+2;
   F:
    x:= x+2;   
    
    G:assert  x \in A2 /\ y \in B2;
};

}
end algorithm; 

*)

Safe ==   (\A self \in ProcSet: pc[self] = "Done") => x \in A /\ y \in B

=============================================================================
