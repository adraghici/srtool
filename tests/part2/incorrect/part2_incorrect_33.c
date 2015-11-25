// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"



int main()
{
 int m;
 int n;
 int i;
 int j;

 /* calculate m times n */
 /* loop counter goes upwards */

 // large lower bound
 assume(m >= 1000);
 assume(m <= 1024);
 assume(n >= 0);
 assume(n <= 127);
 
 i=0;
 j=0;

 while(j <= m) // incorrect
 invariant (i == j*n),
 invariant (j >= 0),
 invariant (j <= m+1)
 {
  j = j + 1;
  i = i + n;
 }
 
 assert(i == m*n);
 
  return 0;
}
