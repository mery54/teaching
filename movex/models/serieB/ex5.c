int main()
{
 
  //@ assert  4 + 4 + 3  == 11 && 3+4+4+3 == 14 && 4+3 == 7 ;        
  int a = 4;
  //@ assert  a + a + 3  == 11 && 3+a+a+3 == 14 && a+3 == 7 ;        
  int b = 3;
  //@ assert  a + a + b  == 11 && b+a+a+b == 14 && a+b == 7 ;      
  int c = a+b;
  //@ assert  a + c  == 11 && b+a+c == 14 && c == 7 ;    
  a = a +  c;
  //@ assert  a == 11 && b+a == 14 && c == 7 ;  
  b = b +  a;
  //@ assert  a == 11 && b == 14 && c == 7 ;
  return(0);
}
