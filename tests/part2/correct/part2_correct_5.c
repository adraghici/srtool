// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int main()
{
    int x;
    int y;
    assume(x < 0);
    assume(y > 0);

    // check if x and y have
    // different signs
    assert( (x^y) < 0);
  return 0;
}

