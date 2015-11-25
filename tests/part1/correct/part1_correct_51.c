// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{
  assert((2 ^ 3) == 1);
  return 0;
}
