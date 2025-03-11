/*@ axiomatic mathexp {
  @ logic integer mathexp(integer n, integer m);
  @ axiom mathexp_1: \forall integer n; n >= 0 
  ==>  mathexp(n,0) == 1;
  @ axiom mathexp_rec:  \forall integer n; n >= 0 
  ==> \forall integer m; m > 0 
  ==> mathexp(n,m) == mathexp(n,m-1)*n;
  @ } */

/*@ requires n > 0 && m >= 0;
  assigns \nothing;
  ensures \result == mathexp(n,m);
*/
int codeexp(int n,int m) {
  int y1 = n;
  int y2  = 0;
  int y3 = 1;
  int z;
    //@ assert  y3 == mathexp(y1,y2)  && y2 >= 0 && y2 <= m && y1==n;          
  /*@ loop invariant  y1 == n; 
    loop invariant y3 == mathexp(y1,y2)  && y2 >= 0 && y2 <= m;   
    loop assigns y2,y3;
    loop variant m-y2;
   */
  while (y2 <  m) {
    //@ assert  y3 == mathexp(y1,y2)  && y2 >= 0 && y2 < m && y1==n;                 
      y3 = y3 * y1;
    //@ assert  y3 == mathexp(y1,y2)*y1  && y2 >= 0 && y2 < m && y1==n;                
      y2 = y2 + 1;
    //@ assert  y3 == mathexp(y1,y2)  && y2 >= 0 && y2 <= m && y1==n;                                   
     };
    //@ assert  y3 == mathexp(y1,y2)  && y2 >= 0 && y2 <= m && y1==n;                                     
    //@ assert y3 == mathexp(y1,y2)  && y2==m && y1==n;                        
  z = y3;
  return z;
}


