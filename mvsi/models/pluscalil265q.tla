----------------------------- MODULE pluscalil265q -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
(*
--wf
--algorithm ex1{ 
variables x = 5;


process (one = 1)
variables u;
{
  A:
    u := x-1;
  AB:  
    x := u;
  B: 
    x := x -2;   
};

process (two = 2)
{
  C:
    x := x + 3;
  D:
    assert  A;
};

}
end algorithm; 

*)


Safe1 ==   (\A self \in ProcSet: pc[self] = "Done") =>  x \in 0..8
Safe2 ==    (\A self \in ProcSet: pc[self] = "Done") => x \in 3..8

==============
