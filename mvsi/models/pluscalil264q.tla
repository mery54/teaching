----------------------------- MODULE  pluscalil264q -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets


(*
--algorithm ex2{ 
variables x = 0, y = 0;


process (one = 1)
{
  A:
    x := x + 1;
  B: 
    y := y -1;  
  C:
      assert   A1  /\  B1;
};

process (two = 2)
{
  D:
    x := x - 1;
  E:
    y:=y+2;
   F:
    x:= x+2;   
    
    G:assert   A2 /\  B2;
};

}
end algorithm; 

*)


Safe1 ==   (\A self \in ProcSet: pc[self] = "Done") => (x < 3)
Safe2 ==    (\A self \in ProcSet: pc[self] = "Done") => ({x,y} = {1,2})

==================
