// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main()
{
  int i;
  int j;
  i=0;
  j=0;
  while(i < 5000)
    invariant (j == 2*i),
    invariant (j <= 10000),
    invariant (i <= 5000)
  {
    i = i + 1;
    j = j + 2;
  }
  
  assert(j == 10000);
  
  return 0;
}

