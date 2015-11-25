// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int x;

int foo()
  requires \old(x) == x,
  ensures \old(x) == x,
  ensures \result == x
{
  return x;
}


int bar() {
  x = x + 2;
  x = foo();
  assert x == \old(x);
  return 2;
}
