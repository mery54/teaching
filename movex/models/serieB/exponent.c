/*@ axiomatic mathexp {
  @ logic integer mathexp(integer n, integer m);
  @ axiom mathexp_1: \forall integer n; n >= 0 
  ==>  mathexp(n,0) == 1;
  @ axiom mathexp_rec:  \forall integer n; n >= 0 
  ==> \forall integer m; m >= 1 
  ==> mathexp(n,m) == mathexp(n,m-1)*n;
  @ } */


/*@ requires n > 0 && m >= 0;
  assigns \nothing;
  ensures \result == mathexp(n,m);
*/
int codeexp(int n,int m) {
  int x1 = n;
  int x2 = m;
  int y1 = x1;
  int y2  = x2;
  int y3 = 1;
  int z;  
  /*@ loop invariant x1 > 0 && x2 >= 0;
    loop invariant mathexp(x1,x2) == mathexp(y1,y2) * y3 && y2 >= 1 && y2 <= x2;    
    loop assigns y1,y2,y3;
   */
  while (y2 != 1) {
    //@ assert mathexp(x1,x2) == mathexp(y1,y2) * y3 && y2 >= 1 && y2 <= x2;    
    if ( y2 % 2 != 0)
      {
    //@ assert mathexp(x1,x2) == mathexp(y1,y2) * y3 && y2==(y2 % 2)*2 + 1;    	
      y2 = y2 - 1;
    //@ assert mathexp(x1,x2) == mathexp(y1,y2) * y1* y3  && y2==(y2 % 2)*2;     
      y3 = y3 * y1;
    //@ assert mathexp(x1,x2) == mathexp(y1,y2) * y3  && y2==(y2 % 2)*2;                   
    };
    //@ assert mathexp(x1,x2) == mathexp(y1,y2) * y3  && y2==(y2 % 2)*2;         
    y1 = y1*y1;
    y2 = y2 /  2;
    //@ assert mathexp(x1,x2) == mathexp(y1,y2) * y3;                  
     };
    //@ assert mathexp(x1,x2) == mathexp(y1,y2) * y3 && y2==1;              
  z = y3;
    //@ assert mathexp(x1,x2) == z;                
  return z;
}


