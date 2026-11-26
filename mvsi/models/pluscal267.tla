----------------------------- MODULE  pluscalil267 ----------------
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
      assert  x \in {1} /\ y \in {2};
};

process (two = 2)
{
  D:
    x := x - 1;
  E:
    y:=y+2;
   F:
    x:= x+2;   
    
    G:assert  x \in {1} /\ y \in {2};
};

}
end algorithm; 

*)

Safe1 ==   (\A self \in ProcSet: pc[self] = "Done") => (x < 3)
Safe == Safe2

==================
