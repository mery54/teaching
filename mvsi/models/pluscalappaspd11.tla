----------------------------- MODULE pluscalappaspd11 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
(*
--wf
--algorithm ex1{ 
variables x = 1;


process (one = 1)
{
  A:
    x := x - 1;
};

process (two = 2)
{
  C:
    x := x + 1;
  D:
    assert E1;
};

}
end algorithm; 

*)

====
