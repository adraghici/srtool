// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"



int main()
{
 int m;
 int n;
 int i;
 int j;

 /* calculate m times n times 2 */

 assume(m >= 1000);
 assume(m <= 1024);
 assume(n >= 0);
 assume(n <= 64);
 
 i=0;
 j=0;

 while(j < m)
 invariant (i == 2*j*n),
 invariant (j >= 0),
 invariant (j <= m)
 {
  j = j + 1;
  i = i + 2 * n;
 }
 
 assert(i == 2*m*n);
 
  return 0;
}
