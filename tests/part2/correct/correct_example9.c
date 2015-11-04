// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

// Technically correct (think why).
// Given candidates suffice to prove correctness.

int g;

int foo() 
  ensures g == \old(g) + 401 {

  int x;
  x = 0;
  while(x < 20)
      candidate_invariant x <= 20,
      candidate_invariant x >= 0,
      candidate_invariant x == \old(g),
      candidate_invariant x == 0 || x == 1 {
    int y;
    y = 0;
    while(y < 20)
      candidate_invariant y == 0 || y == 1,
        candidate_invariant(x == y),
	candidate_invariant(x*y < 400) {
      g = g + 1;
    }
    x = x + 1;
  }
  return g;
}
