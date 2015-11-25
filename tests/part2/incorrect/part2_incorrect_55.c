// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{

  int i;

  i = 198;

  while(i < 200)
  {
    i = i + 1;
    assert(i > 0);
  }
  assert(i == 201);

  return 0;
}

