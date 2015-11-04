// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

// Isn't this cute?

int g;

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
  requires a + 12 < b,
  requires g == 0,
  ensures g <= (10000 - 12)
 {
   int t;
   t = 0;
   while(t < 10000)
         invariant t >= 0,
         invariant t <= 10000,
         invariant (t < 12 ? g == 0 : g <= t - 12)
   {
     int u;
     u = min(a + t, b);

     if(u == b) {
       g = g + 1;
     }

     t = t + 1;
   }
   return 0;
}
