// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"


int foo() {

  int x;
  x = 0;
  while(x < 8)
    invariant x <= 8,
    invariant x >= 0 {
    x = x + 1;
  }
  assert x == 8;

  return 0;
}
