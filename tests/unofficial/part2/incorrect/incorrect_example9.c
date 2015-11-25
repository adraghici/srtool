// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo() {

  int x;
  x = 0;
  while(x != 0) invariant x > 0 {
    x = x + 1;
  }
  return 0;
}
