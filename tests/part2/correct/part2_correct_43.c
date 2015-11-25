// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main()
{
  int i;
  int j;
  int n;
  havoc i;
  havoc n;
  assume(0 <= n && n <= 8);
  j = 1 << n;
  i = i & (j - 1);
  assert(i < 256);
  return 0;
}
