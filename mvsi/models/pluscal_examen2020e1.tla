---------------------- MODULE pluscal_examen2020e1 --------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT x0


(*
--algorithm  compte{
variables x=x0;
{
 
  l0:assert 0 \leq x;
  l1: while (0<x)
  {  l3: assert 0 <x /\ x \leq x0 ;
     x := x - 1;
     l4: assert 0 \leq x /\ x \leq x0;
     
  }; 
  l5: assert x=0
}
}

*)

test == pc # "Done"

===============
