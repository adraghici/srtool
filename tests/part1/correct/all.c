// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;
int y;

int func(int b)
  requires b > 0,
  ensures \result >= 0
{
    int a;
    havoc a;
    assume(a < b);
    assert(a < b);
    if(1) {
        a = a + a;
    }
    return 0;
}
