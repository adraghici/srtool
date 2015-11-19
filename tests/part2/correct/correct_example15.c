// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {

  int x;
  x = 0;
  while (x < 20)
    candidate_invariant x < 21
  {
    x = x + 1;
  }
  assert x == 20;

  return 0;
}
