// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// BMC would find this error with a suitably large unwinding depth

int foo() {

  int x;
  x = 0;
  while(x < 8) {
    x = x + 1;
  }
  assert x == 2;

  return 0;
}
