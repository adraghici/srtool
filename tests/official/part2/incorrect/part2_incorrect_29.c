// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"



int main()
{
 int m;
 int n;
 int i;
 int j;

 /* calculate m times n */
 /* loop counter goes downwards */

 assume(m >= 0);
 assume(m <= 200);
 assume(n >= 0);
 assume(n <= 64);
 
 i=0;
 j=m;

 while(j > 0)
 invariant (i == j*n) // incorrect
 //invariant (i == (m-j)*n)
 //invariant (j >= 0)
 //invariant (j <= m)
 {
  j = j - 1;
  i = i + n;
 }
 
 assert(i == m*n);
 
  return 0;
}
