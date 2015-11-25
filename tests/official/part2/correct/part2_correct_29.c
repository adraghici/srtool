// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"



int main()
{
 int m;
 int n;
 int i;
 int j;

 /* calculate m times n */
 /* loop counter goes upwards */


 assume(m >= 1000);
 assume(m <= 1024);
 assume(n >= 0);
 assume(n <= 64);
 
 i=0;
 j=0;


 while(j < m)
 candidate_invariant (i == j*n)
 {
  j = j + 1;
  i = i + n;
 }
 
 assert(i == m*n);
 
  return 0;
}
