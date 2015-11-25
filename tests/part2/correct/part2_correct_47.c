// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main()
{
  int i;
  int j;
  i = 0;
  j = 1;
  while (i < 5)
  {
    j = j << 1;
    i = i + 1;
  }
  assert(j == 32);
  return 0;
}
