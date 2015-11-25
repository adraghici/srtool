// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// The program is buggy because the invariant can fail.
// BMC would find this error with a suitably large unwinding depth

int foo() {

  int x;
  x = 0;
  while(x < 8) invariant x < 8 {
    x = x + 1;
  }
  assert x == 8;

  return 0;
}
