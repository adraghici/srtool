// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int flump;
int __z2mp;

int __cl3nk()
  requires flump == __z2mp << 3,
  // removed to make incorrect: requires flump == 8,
  ensures \old(flump) == \result << 3
{
  int x;

  x = 3;

  if (__z2mp << 2 == 4) {

    x = x + x*x;

    int x;

    x = x + 1;
    int y;
    y = flump;
    if(x) {
      flump = flump + 0;
      assert y == flump;
    } else {
      flump = flump - 0;
      assert y == flump;
    }
    assert y == flump;

  }

  assert x == 12;

  return __z2mp;

}
