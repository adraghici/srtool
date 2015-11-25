// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
  int i;
  int j;
  i=0;
  j=0;
  while(i < 4)
  {
    i = i + 1;
    j = j + 2;
  }
  
  assert(j == 9);
  
  return 0;
}

