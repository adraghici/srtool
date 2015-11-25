// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// BMC would find this error with a suitably large unwinding depth

int foo() {

  int x;
  x = 0;
  while(x < 30) {
    int y;
    y = x;
    while(y > 0) {
      y = y - 1;
      assert y != 16;
    }
    x = x + 1;
  }
  return 0;
}
