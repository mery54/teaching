--------- MODULE pluscal_ex0 --------
EXTENDS Integers,TLC
CONSTANTS MAXINT
--------------------------------------------------------------

(*
--algorithm EuclidAlg {
  variables
    u = 24;
    v \in 1..MAXINT;
    w = -1;
    a = -1; b = -1;

  {
    \* print <<u, v>>;
    a1:a:=u;b:=v;
    w:while (u /= 0) {
      a2:if (u < v) {
        u := v || v := u
      };
     a3: u := u - v
    };
   a4:  w:= u+v;
    print <<a,b,w>>;
  }
}

*)
\* BEGIN TRANSLATION
\* Label w at line 17 col 7 changed to w_
VARIABLES u, v, w, a, b, pc

vars == << u, v, w, a, b, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1..MAXINT
        /\ w = -1
        /\ a = -1
        /\ b = -1
        /\ pc = "a1"

a1 == /\ pc = "a1"
      /\ a' = u
      /\ b' = v
      /\ pc' = "w_"
      /\ UNCHANGED << u, v, w >>

w_ == /\ pc = "w_"
      /\ IF u /= 0
            THEN /\ pc' = "a2"
            ELSE /\ pc' = "a4"
      /\ UNCHANGED << u, v, w, a, b >>

a2 == /\ pc = "a2"
      /\ IF u < v
            THEN /\ /\ u' = v
                    /\ v' = u
            ELSE /\ TRUE
                 /\ UNCHANGED << u, v >>
      /\ pc' = "a3"
      /\ UNCHANGED << w, a, b >>

a3 == /\ pc = "a3"
      /\ u' = u - v
      /\ pc' = "w_"
      /\ UNCHANGED << v, w, a, b >>

a4 == /\ pc = "a4"
      /\ w' = u+v
      /\ PrintT(<<a,b,w'>>)
      /\ pc' = "Done"
      /\ UNCHANGED << u, v, a, b >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a1 \/ w_ \/ a2 \/ a3 \/ a4
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


MAX == 32768  (* 16 bits *)
D == 0..MAX
(*  x \leq 32768 *)
DD(X) ==  ( X # u =>  X \in D)
init(X) ==  ( X # u)


=========
