// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"


int main()
{

  int i;
  int j;
  
  i=0;

  j = 5;

  while(i < 5)
  {
    i = i + 1;
    j = j + 1;
  }
  assert(j == 10);

  return 0;
}

