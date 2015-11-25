// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int flump;

int __cl3nk()
  requires 0,
  ensures \result == flump + (16 << 1)
{
  int x;
  assert 0;
  return 5224;
}
