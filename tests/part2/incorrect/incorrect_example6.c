// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"



int min(int x, int y)
  ensures \result == (y < x ? y : x)
{
  int result;
  result = x;
  if (y < x) {
    result = y;
  }
  return result;
}

int foo(int a, int b)
  requires b < 100000,
  requires a < b,
  requires a + 12 < b
 {
   int t;
   t = 0;
   while(t < 10000) {
     int u;
     u = min(a + t, b);
     assert u < b;
     t = t + 1;
   }
   return 0;
}
