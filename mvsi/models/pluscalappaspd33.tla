----------------------------- MODULE pluscalappaspd33 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
(*
--wf
--algorithm ex3{ 
variables x = 0, y = 2;


process (one = 1)
variable u;
{
  A:
  u := x+1;
  AB:
    x := u;
  B: 
    y := y -1;  
  C:
 assert E31; 
};

process (two = 2)
{
  D:
    x := x - 1;
  E:
    y:=y+2;
   F:
    x:= x+2;   
  G:
    assert E32;
};

}
end algorithm; 

*)
\
====
