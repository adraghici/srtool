// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"



int main()
{
 int m;
 int n;
 int i;
 int j;

 /* calculate m times n times 2 */

 assume(m >= 0);
 assume(m <= 3);
 assume(n >= 0);
 assume(n <= 127);
 
 i=0;
 j=0;

 while(j < m)
 candidate_invariant (i == 2*j*n)
 {
  j = j + 1;
  i = i + 2 * n;
 }
 
 assert(i == 2*m*n);
 
  return 0;
}
