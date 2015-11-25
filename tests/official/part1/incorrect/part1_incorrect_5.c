// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo(int _i, int _j) {
    int i;
    int j;
    i = _i;
    j = _j;
    i = 42;
    j = ~~i;
    assert (j < 0);
    return 3;
}
