// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// BMC would find this error with a suitably large unwinding depth

int foo() {

  int i;

  int x;
  x = 0;
  while(x < 10) {
    i = 2;
    int i;
    while (x < 5) {
      x = x + 1;
      if (x == 5) {
        i = 8;
      }
    }
    x = x + 1;
  }
  assert x == 10;

  return 0;
}
