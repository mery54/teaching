#include <limits.h>
#include  "power2.h"

int power2(int x)
{int  r,k,cv,cw,or,ok,ocv,ocw;
  r=0;k=0;cv=0;cw=0;or=0;ok=k;ocv=cv;ocw=cw;
      /*@ loop invariant 0 <= cv && 0 <= cw && 0 <= k;
	@ loop invariant cv == k*k;
         @ loop invariant k  <= x;
         @ loop invariant cw  == 2*k;        
         @ loop invariant  4*cv  == cw*cw;
         @ loop assigns k,cv,cw,or,ok,ocv,ocw; */
  while (k<x)
    {
    ok=k;ocv=cv;ocw=cw;
      k=ok+1;
      cv=ocv+ocw+1;
      cw=ocw+2;
      
    }
  r=cv;
  return(r);
}

