// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

// Invariant inference or full unrolling required

int foo() {

  int x;
  x = 0;
  while(x < 8) {
    x = x + 1;
  }
  assert x == 8;

  return 0;
}
