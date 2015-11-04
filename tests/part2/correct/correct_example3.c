// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int foo() {

  int x;
  x = 0;
  while(x < 30) invariant x >= 0, invariant x <= 30 {
    int y;
    y = x;
    while(y > 0) 
      invariant y >= 0,
	invariant y <= x {
      y = y - 1;
    }
    x = x + 1;
  }
  assert (x % 2) == 0;
  return 0;
}
