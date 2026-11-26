----------------------------- MODULE  pluscalil262 -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets


(*
--algorithm ex2{ 
variables x = 2, y = 9;


process (one = 1)
{
  A:
    x := x + 1;
  B: 
    y := y -1;  
  C:
      assert  A1;
};

process (two = 2)
{
  D:
    x := x - 1;
  E:
    y:=y+2;
   F:
    x:= x+2;   
    
    G:assert  A2;
};

}
end algorithm; 

*)

==================
