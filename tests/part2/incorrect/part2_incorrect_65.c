// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"


int main()
{

  int i;
  int j;
  
  i=0;

  j = 5;

  int n;
  assume(n >= 50000);
  assume(n <= 100000);

  while(i < n)
  {
    i = i + 1;
    j = j + 1;
  }
  // should be n+5
  assert(j == n);

  return 0;
}

