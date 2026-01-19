----------MODULE cours1 ---------
EXTENDS Integers, TLCy
-------------------------------
CONSTANTS
	\* @type: Int;
	x0,
	\* @type: Int;	
	y0,
	\* @type: Int;
	z0,
	\* @type: Int;
	min,
	\* @type: Int;
	max
VARIABLES
	  \* @type: Int;
	  x,
	  \* @type: Int;
	  y,
	  \* @type: Int;
	  z,
	  \* @type: Str;
   	  pc
 
TypeOK ==
   /\ pc \in {"l2","l1"}
   /\ x \in Int
   /\ y \in Int
   /\ z \in Int

-------------------------------
(* precondition pre(x0,y0,z0) *)
pre(fx,fy,fz)  == fx=10 /\ fz=2*fx /\ fy=fz+fx
ASSUME pre(x0,y0,z0) 
-----------------------------
vars == <<x,y,z,pc>>
(* initial conditions *)
Init == pc = "l1" /\ pre(x,y,z) 
-------------------------------
(* actions *)
skip == UNCHANGED <<pc,x,y,z>>
al1l2 == 
    /\ pc="l1" /\ TRUE 
    /\ pc'="l2" 
    /\ y'=z+x
    /\ x'=x /\ z'=z
-------------------------------
(* next relation *)
Next == skip \/ al1l2
Spec == Init /\ [][Next]_vars /\ WF_vars(al1l2)
-------------------------------
Inv == 
    /\ pc \in {"l2","l1"}
    /\ pc="l1" => x=10 /\ z=2*x /\ y=z+x
    /\ pc="l2" => x=10 /\ y=z+x
    
D == min..max
    
suretecorrectionpartielle ==   pc="l2" => x=10 /\ y=x+2*10  
sureteabsencederreurs == z+x \in D /\ x \in D /\ y \in D /\ z \in D

 \* check inductiveness using Apalache

ConstInit ==
  /\ x0=10
  /\ y0=30
  /\ z0=20  
  /\ min = -2^31
  /\ max  = 2^31-1
  

======================================================
 sh  apalache/bin/apalache-mc  check  --inv=Inv   --length=20 --cinit=ConstInit cours1.tla
 
