// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main()
{
  int i;
  int n;
  i = 3;
  assume(n >= 0);
  assume(n <= 4);
  
  int origN; 
  origN = n;

  while (n > 0)
  {
    i = i + 1;
    n = n - 1;
  }
  assert(i >= 3);
  return 0;
}
