// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"



int main()
{
 int m;
 int n;
 int res;
 int itLeft;

 /* calculate m times n */
 /* loop counter goes downwards */

 assume(m >= 20);
 assume(m <= 200);
 assume(n >= 0);
 assume(n <= 64);
 
 res=0;
 itLeft=m;

 while(itLeft > 0)
 candidate_invariant (res == (m-itLeft)*n)
 {
  itLeft = itLeft - 1;
  res = res + n;
 }
 
 assert(res == m*m);
 
  return 0;
}
