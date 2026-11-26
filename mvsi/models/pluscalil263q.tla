----------------------------- MODULE pluscalil263q -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
(*
--wf
--algorithm ex1{ 
variables x = 0;


process (one = 1)
variables u;
{
  A:
    u := x+1;
  AB:  
    x := u;
  B: 
    x := x +1;   
};

process (two = 2)
{
  C:
    x := x - 1;
  D:
    assert E;
};

}
end algorithm; 

*)


==============
