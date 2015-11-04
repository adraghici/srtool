// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"


// Invariant inference or full unrolling required

int bar(int a)
  ensures \result == a + 1
{
  return a + 1;
}

int foo() {

  int x;
  x = 0;
  while(x < 20) {
    x = bar(x);
  }
  assert x == 20;

  return 0;
}
