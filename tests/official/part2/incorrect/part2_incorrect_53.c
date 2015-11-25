// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

/* step case of invariant not true */

int main()
{
  int i;
  int j;
  i = 0;
  j = 3;
  while(i < 100)
    invariant (i + j == 3)
  {
    i = i + 1;
    if (j > 0) {
      j = j - 1;
    }
  }
  return 0;
}
