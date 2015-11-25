// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int x;

int foo(int i, int j) {
    assume j == 2*2*2*2*2;
    assume i == 2*2*2*2*2*2;
    assert (i|j) == 2*2%2*2*2 + 2*2*2*2*2*2;
    return 0;
}
