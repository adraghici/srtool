// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// BMC would find this error with a suitably large unwinding depth.
// The candidates are irrelevant to how well BMC will do.

int g;

int foo() 
  ensures g == \old(g) + 401 {

  int x;
  x = 0;
  while(x < 20)
      candidate_invariant x <= 20,
      candidate_invariant x >= 0,
      candidate_invariant x == \old(g) {
    int y;
    y = 0;
    while(y < 20)
        candidate_invariant(x == y),
	candidate_invariant(x*y < 400) {
      g = g + 1;
      y = y + 1;
    }
    x = x + 1;
  }
  return g;
}
