// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int main()
{

  int i;
  int j;

  i = j;

  while(i < 100)
  {
    i = i + 1;
    j = j + 1;
  }
  assert(i == j + 2);

  return 0;
}

