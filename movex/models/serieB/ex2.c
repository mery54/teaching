int q1() {
  /*@ assert 2 == 2;  */   
  int c = 2 ;
  /*@ assert c == 2;  */
    /*@ assert c == 2;  */
  int x;
  /*@ assert c == 2;  */
    /*@ assert 3*c == 6;  */
  x = 3 * c;
  /*@ assert x == 6;  */
  return(0);
}
