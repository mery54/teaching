--------- MODULE pluscal-exemple1 --------
EXTENDS Integers,TLC
CONSTANTS u0,v0
--------------------------------------------------------------

(*
--algorithm  {
  variables
    u = u0;
    v = v0;
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


======================================================
