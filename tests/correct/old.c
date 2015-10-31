// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int x;
int x;
int y;

int foo(int i)
    requires x == y + 1,
    ensures y == \old(x) - 1,
    ensures \result == \old(x) + 1
{
    y = x - 1;
    x = x + 1;
    return x;
}
