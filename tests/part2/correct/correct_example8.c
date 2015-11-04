// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

// Technically correct (think why)
// Given invariants suffice to prove correctness

int g;

int foo() 
  ensures g == \old(g) + 401 {

  int x;
  x = 0;
  while(x < 20)
    invariant x == 0 {
    int y;
    y = 0;
    while(y < 20) 
      invariant y == 0
    {
      g = g + 1;
    }
    x = x + 1;
  }
  return g;
}
