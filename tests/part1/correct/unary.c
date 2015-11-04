// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {

    int x;
    int y;
    int z;
    x = +501;
    y = - x;
    z = x + y;
    assert z == 0;
    return 0;

}