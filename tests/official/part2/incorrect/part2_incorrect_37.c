// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"



int main()
{
 int m;
 int n;
 int i;
 int j;

 /* calculate m plus n */

 assume(m == 5);
 assume(n >= 1000);
 assume(n <= 1024);
 
 i=n; // should be m
 j=0;

 while(j < n)
 candidate_invariant (i == m+j),
 candidate_invariant (j >= 0),
 candidate_invariant (j <= n)
 {
  j = j + 1;
  i = i + 1;
 }
 
 assert(i == m+n);
 
  return 0;
}
