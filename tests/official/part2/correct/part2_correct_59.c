// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"


int main()
{

  int i;
  int j;

  i = j;

  while(i < 5)
  {
    i = i + 1;
    j = j + 1;
  }
  assert(i == j);

  return 0;
}

