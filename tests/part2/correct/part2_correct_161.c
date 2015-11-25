// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo()
    ensures \result == 2
{
    return 2;
}

int bar() {
    int x;
    x = foo();
    assert x == 2;
    return 0;
}
