// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"


int main()
{

  int i;
  int j;

  i = j;

  int c;
  c=0;

  int n;
  assume(n >= 50000);
  assume(n <= 100000);

  while(c < n)
  {
    i = i + 1;
    j = j + 2;
    c = c + 1;
  }
  // should be +50000
  assert(i+(n/2) == j);

  return 0;
}

