// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// The example is incorrect because the precondition of bar fails once x gets sufficiently large
// BMC would find this error with a suitably large unwinding depth

int bar(int a)
  requires a < 15,
  ensures \result == a + 1
{
  return a + 1;
}

int foo() {

  int x;
  x = 0;
  while(x < 20) {
    x = bar(x);
  }
  assert x == 20;

  return 0;
}
