// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
  int i;
  int j;
  int k;
  havoc i;
  havoc j;
  havoc k;
  k = ((i + j)/2) & 255;
  assert(k != 22);
  return 0;
}
