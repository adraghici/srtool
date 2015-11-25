// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
  int i;
  int n;
  i = 3;
  assume(n >= 10000);
  assume(n <= 20000);
  
  int origN; 
  origN = n;

  while (n > 0)
  {
    i = i + 1;
    n = n - 1;
  }
  assert(i >= 11000);
  return 0;
}
