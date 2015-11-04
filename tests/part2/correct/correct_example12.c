
// Invariant inference or full unrolling required

int foo() {

  int x;
  x = 0;
  while(x < 30) {
    int y;
    y = x;
    while(y > 0) {
      y = y - 1;
    }
    x = x + 1;
  }
  assert (x % 2) == 0;
  return 0;
}
