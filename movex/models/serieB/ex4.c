int main()
{
  int z;
  //@ assert   4 == 4 ;
  int a = 4;
  //@ assert   a == 4 ;
  // ==> 
  //@ assert   3 == 3 && a == 4;  
  int b = 3; 
  //@ assert   b == 3 && a == 4;
  // ==>   
  //@ assert   b == 3 && a+b == 7 && a == 4 ;
  int c = a+b; 
  //@ assert   b == 3 && c == 7 && a == 4 ;
  // ==>
  //@ assert  a +c  == 11 && b +a+c == 14 && c == 7 && a+c+b+a +c== 25;  
  a = a +  c;
  //@ assert  a == 11 && b +a == 14 && c == 7 && a+b+a == 25;
  b = b +  a;
  //@ assert  a == 11 && b == 14 && c == 7 && a+b == 25;
  // ==>
    //@ assert  a == 11 && b == 14 && c == 7 && a*b == 154;
  z = a*b;
  //@ assert  a == 11 && b == 14 && c == 7 && z == 154;
  return(0);
}
