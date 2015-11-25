// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int flump;

int __cl3nk()
  ensures \result == flump
{
  int x;
  x = flump;

  int i;
  i = 0;
  if(i < 5) {
    x = x + 1;
    i = i + 1;
  }
  if(i < 5) {
    x = x + 1;
    i = i + 1;
  }
  if(i < 5) {
    x = x + 1;
    i = i + 1;
  }
  if(i < 5) {
    x = x + 1;
    i = i + 1;
  }
  if(i < 5) {
    x = x + 1;
    i = i + 1;
  }
  // unreachable:
  if(i < 5) {
    x = x + 1;
    i = i + 1;
  }
  // unreachable:
  if(i < 5) {
    x = x + 1;
    i = i + 1;
  }
  // unreachable:
  if(i < 5) {
    x = x + 1;
    i = i + 1;
  }
  assert x == flump + 5;
  return x - 5;
}
