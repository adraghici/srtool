// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

// You would need to infer invariants or fully unwind to verify this one

int foo() {

  int x;
  x = 0;
  while(x < 8) {
    x = x + 1;
  }
  assert x == 8;

  return 0;
}
