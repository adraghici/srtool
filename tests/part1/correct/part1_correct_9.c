// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;

int foo(int i, int j) {
    assume j == 2*2*2*2*2;
    assume i == 2*2*2*2*2*2;
    assert ((j-1)&i) == 0;
    return 0;
}
