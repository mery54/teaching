---------------------- MODULE appex5_1 --------------------------------
EXTENDS Naturals, Integers, TLC

CONSTANT n0

f0 == [k \in 0..n0-1 |->
                    IF k=0 THEN 3
                    ELSE IF k=1 THEN 6
                    ELSE IF k=2 THEN 2*k
                    ELSE IF k=3 THEN 9
                    ELSE 5]


(*
-termination
-wfNext
--algorithm Maximum {
  variables i = 0;
            m=0;
	    f=f0;
	    n=n0;
	    r;
{
            l0:m:=f[0];
            l1:i:=1;
            l2: while (i<n) {
            l3: if (f[i]>m){
            l4: m:=f[i];
            } ;
            l5:i:=i+1;
            };
	    r := m;	    
}
}
*)

===========================================================================
