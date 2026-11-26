----------------------------- MODULE pluscalil271 ---------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS n

(*
--algorithm ex2{ 
variables x = 1..n,y,s=0;

process (one = 1)
{
  A: await x = {} ;
  D: assert x={};   
};

process (Q = 2)
{
  E: while (x # {})
  {
    F:y := CHOOSE v \in 1..n: v \in x; 
    G: s  := s + y*y*y;
    H: x := x  \  {y};
  };
  
};

}
end algorithm; 

*)






P1 == pc[1]="Done" => x={}
P2 == pc[2]="Done" => s = ((n*(n+1)) \div  2)^2


====
