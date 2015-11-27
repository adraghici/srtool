// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

// BMC would find this error with a suitably large unwinding depth

int foo() {

  int x;
  x = 0;
  int y;
  y = 0;
  int z;
  z = 0;
  int u;
  u = 0;
  while(x < 100000) {
    x = x + 1;
    while (y < 100000) {
      y = y + 1;
      while (z < 100000) {
        z = z + 1;
        while (u < 100000) {
          u = u + 1;
        }
      }
    }
  }
  assert x == 2;

  return 0;
}
