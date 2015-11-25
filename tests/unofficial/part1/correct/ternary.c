// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {

    assert (1 ? 1 : 0) == 1;
    assert (0 ? 1 : 0) == 0;
    assert (1 ? 1 : 0 ? 2 : 3) == 1;
    assert (0 ? 1 : 1 ? 2 : 3) == 2;
    assert (0 ? 1 : 0 ? 2 : 3) == 3;

    assert (0 ? 1 : 0 ? 2 : 0 ? 3 : 0 ? 4 : 0 ? 5 : 6) == 6;
    return 0;

}