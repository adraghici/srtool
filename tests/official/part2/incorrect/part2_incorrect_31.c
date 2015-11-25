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

 assume(m >= 1000);
 assume(m <= 1024);
 assume(n >= 0);
 assume(n <= 64);
 
 i=0;
 j=m;

 while(j > 0)
 candidate_invariant (i == (m-j)*n),
 candidate_invariant (i-2 <= (m-j)*n),
 candidate_invariant (i <= (m-j)*n + 2),
 invariant (i/2 <= (m-j)*n/2),
 invariant (i/4 <= (m-j)*n/4),
 invariant (i/7 <= (m-j)*n/7),
 candidate_invariant (i/7 <= (m-j)*n/6),
 candidate_invariant (i/7 <= (m-j)*n/9),
 candidate_invariant (j >= 0),
 candidate_invariant (j <= m),
 candidate_invariant (j > 1),
 candidate_invariant (j < 140),
 candidate_invariant (j < 600),
 candidate_invariant (j*2 < 400)
 {
  j = j - 1;
  i = i + n;
 }
 
 assert(i == m*m); // incorrect
 
  return 0;
}
