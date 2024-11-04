#ifndef _A_H
#define _A_H

// Definition of the  mathematical function mathpower2

/*@ axiomatic mathpower2 {
  @ logic integer mathpower2(integer n);
  @ axiom mathpower2_0: mathpower2(0) == 0;
  @ axiom mathpower2_rec: \forall integer n; n > 0 
  ==> mathpower2(n) == mathpower2(n-1) + n+n+1;
  @ } */


/*@ axiomatic matheven {
  @ logic integer matheven(integer n);
  @ axiom matheven_0: matheven(0) == 0;
  @ axiom mathpeven_rec: \forall integer n; n > 0 
  ==> matheven(n) == matheven(n-1) + 2;
  @ } */

// We define v and w in a one shot axiomatic  definition 

/*@ axiomatic vw {
  @ logic integer v(integer n);
  @ logic integer w(integer n);  
  @ axiom v_0: v(0) == 0;
  @ axiom w_0: w(0) == 0;  
  @ axiom v_rec: \forall integer n; n > 0 
  ==> v(n) == v(n-1) +n+n+1 &&  w(n) == w(n-1) + 2;  
@ } */

/*@ lemma propw:
@ \forall int n; n >= 0 ==> w(n) == n+n; @*/



/*@ lemma propv:
@ \forall int n; n >= 0 ==> v(n) == n*n; @*/


/*@ lemma prop1:
@ \forall int n; n >= 0 ==> matheven(n) == n+n; @*/

/*@ lemma prop2:
@ \forall int n; n >= 0 ==> mathpower2(n) == n*n; @*/


/*@ axiomatic auxmath {
  @ lemma rule1: \forall int n; n >0 ==> n*n == (n-1)*(n-1)+2*(n-1)+1; 
  @ } */

/*@  requires  0 <= x; 
     assigns \nothing;
     ensures \result == x*x;
*/
int power2(int x);

#endif

