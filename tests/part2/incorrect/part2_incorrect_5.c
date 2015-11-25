// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int main()
{
    int x;
    int y;
    assume(x < 0);
    assume(y > 0);

    // check if x and y have
    // different signs
    assert( (x^y) > 0); // should be <
  return 0;
}

