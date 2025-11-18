--------------------- MODULE appex4_1_5 --------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANTS x0,y0,min,max

ASSUME x0 \in min..max /\ y0 \in min..max 


(*
--algorithm commeonveut {
  variables x=x0, 
            y = y0, 
            z;
            
{
 l0:assert x=x0/\ y=y0;
 if ( x < y ) {
  l1:  assert x=x0 /\ y=y0 /\ x<y;
  z:=y;
  l2: assert x=x0 /\ y=y0 /\ x \leq z /\ y \leq z /\ z \in {x,y} ;
  }
else
{ 
 l3: assert x=x0 /\ y=y0 /\  x >= y ;
 z:= x;
 l4: assert x=x0 /\ y=y0 /\ z=y0 /\ x \leq z /\ y \leq z /\ z \in {x,y};
 };
 l5: assert x=x0 /\ y=y0 /\ z \in  {x,y} /\ x <= z /\ y <= z;
 print "done";
 l6: assert x=x0 /\ y=y0 /\ z \in  {x,y} /\ x <= z /\ y <= z;

}
}
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES x, y, z, pc

vars == << x, y, z, pc >>

Init == (* Global variables *)
        /\ x = x0
        /\ y = y0
        /\ z = defaultInitValue
        /\ pc = "l0"

l0 == /\ pc = "l0"
      /\ Assert(x=x0/\ y=y0, "Failure of assertion at line 16, column 5.")
      /\ IF x < y
            THEN /\ pc' = "l1"
            ELSE /\ pc' = "l3"
      /\ UNCHANGED << x, y, z >>

l1 == /\ pc = "l1"
      /\ Assert(x=x0 /\ y=y0 /\ x<y, 
                "Failure of assertion at line 18, column 8.")
      /\ z' = y
      /\ pc' = "l2"
      /\ UNCHANGED << x, y >>

l2 == /\ pc = "l2"
      /\ Assert(x=x0 /\ y=y0 /\ x \leq z /\ y \leq z /\ z \in {x,y}, 
                "Failure of assertion at line 20, column 7.")
      /\ pc' = "l5"
      /\ UNCHANGED << x, y, z >>

l3 == /\ pc = "l3"
      /\ Assert(x=x0 /\ y=y0 /\  x >= y, 
                "Failure of assertion at line 24, column 6.")
      /\ z' = x
      /\ pc' = "l4"
      /\ UNCHANGED << x, y >>

l4 == /\ pc = "l4"
      /\ Assert(x=x0 /\ y=y0 /\ z=y0 /\ x \leq z /\ y \leq z /\ z \in {x,y}, 
                "Failure of assertion at line 26, column 6.")
      /\ pc' = "l5"
      /\ UNCHANGED << x, y, z >>

l5 == /\ pc = "l5"
      /\ Assert(x=x0 /\ y=y0 /\ z \in  {x,y} /\ x <= z /\ y <= z, 
                "Failure of assertion at line 28, column 6.")
      /\ PrintT("done")
      /\ pc' = "l6"
      /\ UNCHANGED << x, y, z >>

l6 == /\ pc = "l6"
      /\ Assert(x=x0 /\ y=y0 /\ z \in  {x,y} /\ x <= z /\ y <= z, 
                "Failure of assertion at line 30, column 6.")
      /\ pc' = "Done"
      /\ UNCHANGED << x, y, z >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l5 \/ l6
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


maximum(X,Y,Z) ==  Z \in  {X,Y} /\ X <= Z /\ Y <= Z


Inv == 
    /\ pc \in {"l0","l1","l2","l3","l4","l5","l6","Done"}
    /\ x \in Int /\ y \in Int /\ (z#defaultInitValue => z \in Int)
    /\ pc = "l0" => x=x0/\ y=y0
    /\ pc="l1" => x=x0 /\ y=y0 /\ x<y
    
safetyrte == x \in min..max /\ y \min..max /\ z \ min.max


safetypcv1 == pc="Done" =>  x=x0 /\ y=y0 /\ z \in  {x,y} /\ x <= z /\ y <= z


safetypcv2 == pc="Done" =>  x=x0 /\ y=y0 /\ maximum(x,y,z)

==================================================================
\* Modification History
\* Last modified Tue Oct 04 09:20:27 CEST 2022 by mery
\* Created Wed Sep 09 17:02:47 CEST 2015 by mery
