----------------------------- MODULE  pluscalappaspd5-----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets


(*
--wf
--algorithm ex5{ 
variables x = 0, y = 8;


process (one = 1)
{
  A:
    x := x + 1;
  B: 
    y := y -1;  
  C:
      assert  A1;

process (two = 2)
{
  D:
    x := x - 1;
  E:
    y:=y+2;
   F:
    x:= x+2;   
   assert A2; 
};

}
end algorithm; 

*)
======