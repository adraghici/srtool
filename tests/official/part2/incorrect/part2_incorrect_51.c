// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
  int i;
  int j;
  i = 0;
  j = 1;
  while (i < 7)
  invariant (j == (1 << i))
  {
    j = j << 1;
    i = i + 1;
  }
  assert(j == 256); // 128
  return 0;
}
