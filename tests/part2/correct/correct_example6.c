// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

// Isn't this cute?

int g;

int min(int x, int y)
  candidate_ensures \result == (y < x ? y : x),
  candidate_ensures \result == x,
  candidate_ensures \result == y,
  candidate_ensures \result == x + y,
  candidate_ensures \result == (y < x ? y : x)
{
  int result;
  result = x;
  if (y < x) {
    result = y;
  }
  return result;
}

int foo(int a, int b)
  candidate_requires b < 100000,
  candidate_requires a < b,
  candidate_requires a + 12 < b,
  candidate_requires g == 0,
  candidate_ensures g <= (10000 - 12),
  candidate_ensures g ^ (10000 - 12),
  candidate_ensures g != (10000 - 12),
  candidate_ensures g >= (10000 - 12),
  candidate_ensures g > (10000 - 12),
  candidate_ensures g <= (10000)
 {
   int t;
   t = 0;
   while(t < 10000)
         candidate_invariant t >= 0,
         candidate_invariant t >= 1,
         candidate_invariant t <= 1000,
         candidate_invariant (t < 11 ? g == 0 : g <= t - 12),
         candidate_invariant t <= 10000,
         candidate_invariant (t < 12 ? g == 0 : g <= t - 12)
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
