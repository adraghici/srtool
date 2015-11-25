// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"



int main()
{
 int m;
 int n;
 int i;
 int j;

 /* calculate m plus (2 times n) */

 assume(m >= 0);
 assume(m <= 64);
 assume(n >= 0);
 assume(n <= 64);
 
 i=m;
 j=0;

 while(j < n)
 //candidate_invariant (i == m+j*2)
 {
  j = j + 1;
  i = i * 2;
 }
 
 assert(i == m+(2*n));
 
  return 0;
}
