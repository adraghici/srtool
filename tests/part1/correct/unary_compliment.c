// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {

    int x;
    int y;
    x = 501;
    y = ~x;
    assert (x + y) == -1;
    assert (x & y) == 0;
    assert (x | y) == -1;
    assert (x ^ y) == -1;
    return 0;

}