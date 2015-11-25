// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{

  int i;
  int j;

  i = j;

  int c;
  c=0;

  while(c < 100)
  {
    i = i + 1;
    j = j + 2;
    c = c + 1;
  }
  assert(i+100 == j);

  return 0;
}

