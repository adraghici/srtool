// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// Although there does exist a spec for min that makes foo correct,
// the given spec is too weak.  Thus foo is incorrect and the whole program
// is incorrect

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
  requires a < b
 {
   int t;
   t = min(a, b);
   assert t == a;
   return 0;
}
