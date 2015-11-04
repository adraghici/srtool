// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int func()
{
    int a;
    int b;
    a = 10;
    b = 5;
    while(a > 0)
      invariant a >= 0,
      invariant b == 5
    {
        a = a - 1;
    }
    b = 2;
    return 0;
}
