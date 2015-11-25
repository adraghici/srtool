// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{

  int i;
  int j;
  
  i=0;

  j = 5;

  while(i < 100)
  {
    i = i + 1;
    j = j + 1;
  }
  assert(j == 105);

  return 0;
}

