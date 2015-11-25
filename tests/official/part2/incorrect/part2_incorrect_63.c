// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"


int main()
{

  int i;
  int j;
  assume(j < 100);
  assume(j >= 0);
  i = j;

  while(i < 10000)
  {
    i = i + 1;
    j = j + 1;
  }
  assert(i == j + 2);

  return 0;
}

