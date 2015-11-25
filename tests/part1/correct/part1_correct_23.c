// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int x;

int foo(int i, int j) {
    x = i + j;
    x = x / 2;
    assert(x == (i + j) / 2);
    return x;
}
