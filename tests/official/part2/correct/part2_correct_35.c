// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"



int main()
{
 int m;
 int n;
 int i;
 int j;

 /* calculate m plus (2 times n) */

 assume(m >= 0);
 assume(m <= 127);
 assume(n >= 0);
 assume(n <= 127);
 
 i=m;
 j=0;

 while(j < n)
 //candidate_invariant (i == m+j*2)
 {
  j = j + 1;
  i = i + 2;
 }
 
 assert(i == m+(2*n));
 
  return 0;
}
