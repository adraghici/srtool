// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int flump;
int __z2mp;

int __cl3nk()
  requires flump == __z2mp << 3,
  requires flump == 8,
  ensures \old(flump) == \result << 3
{
  int x;

  x = 3;

  assume __z2mp << 2 == 16;
  assume __z2mp << 2 == 15;

  if (__z2mp << 2 == 4) {

    x = x + x*x;

    assert 0;

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
