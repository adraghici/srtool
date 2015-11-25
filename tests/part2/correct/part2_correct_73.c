// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int g;

int min(int x, int y)
  ensures \result == x || \result == y
{
  int result;
  result = x;
  if (y < x) {
    result = y;
  }
  return result;
}

int foo(int a, int b)
  requires a < b,
  ensures g == \old(g) * 2
 {
   int t;
   t = min(a, b);
   if(t == a) {
     g = g * 2;
   }
   if(t == b) {
     g = g * 2;
   }
   return 0;
}
