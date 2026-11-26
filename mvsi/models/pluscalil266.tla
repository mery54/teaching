----------------------------- MODULE pluscalil266 -------------------
EXTENDS Integers,Naturals,Sequences,TLC
CONSTANTS
	N
ASSUME N >  0



(*
--algorithm algo { 
variable
	canal = <<>>;
	witness = -1;
	result = -1;
\*  Macro for sending primitive: sending a message m on the fifo channel chan  
macro Send(m, chan) {
    chan := Append(chan, m);
  };

\*  Macro for receiving  primitive: receiving  a message m on the fifo channel chan  
macro Recv(v, chan) {
    await chan # <<>>; 
    v := Head(chan);
    chan := Tail(chan);
  };

process (one = 1)
variable 
	 x = 0;
	 v = 0;
	 w = 1;
{
	w:while (x < N) {
         a:x := x + 1;
	 b:w :=  w +2;
	 c:v := v + w; 
d: Send(v,canal);
       };
e: Send(-1,canal);
};

process (two = 2)
variable s = 0,mes;
{
	  w:while (TRUE) {
	  a: if (canal # <<>>) {
	     b:Recv(mes,canal);
		c:if (mes # -1) { d: s := s +mes;}
	  	else {e: goto f;};
	  };
	  };
	  f: print <<s>>;
	  g: result := s; 
      
};

process (three = 3)
{
       w:witness := N*(N+1)*(2*N+1);
       z:witness := witness \div 6;

};
}
end algorithm;


*)


Safe1 ==   (\A self \in ProcSet: pc[self] = "Done") => (result =  witness)
Safe2 ==   (\E self \in ProcSet: pc[self] # "Done")
Safe == Safe1
========================
