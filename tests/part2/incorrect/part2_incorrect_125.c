// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// Although there does exist a spec for min that makes foo correct,
// the given spec is too weak, and the Houdini candidates do not incorporate
// a strong enough spec.  Thus the program is incorrect

int min(int x, int y)
  candidate_requires x == y,
  ensures \result == x || \result == y,
  candidate_ensures \result == x,
  candidate_ensures \result == y,
  candidate_ensures 0,
  candidate_requires 1,
  candidate_requires 0
{
  int result;
  result = x;
  if (y < x) {
    result = y;
  }
  return result;
}

int foo(int a, int b)
  requires a < b
 {
   int t;
   t = min(a, b);
   assert t == a;
   return 0;
}
