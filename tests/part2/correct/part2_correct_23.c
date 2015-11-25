// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"



int main()
{
 int m;
 int n;
 int res;
 int itLeft;

 /* calculate m times n */
 /* loop counter goes downwards */

 assume(m >= 1000);
 assume(m <= 1024);
 assume(n >= 0);
 assume(n <= 64);
 
 res=0;
 itLeft=m;

 while(itLeft > 0)
 {
  itLeft = itLeft - 1;
  res = res + n;
 }
 
 assert(res == m*n);
 
  return 0;
}
