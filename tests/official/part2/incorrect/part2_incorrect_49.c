// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
  int i;
  int n;
  havoc n;
  assume(10000 <= n);
  i = 0;
  while (i <= n)
  {
    i = i + 1;
  }
  assert(i == n);
  return 0;
}
