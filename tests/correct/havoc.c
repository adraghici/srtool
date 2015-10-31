// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int havocTest() {
    int x;
    int t;
    havoc t;
    x = 1;
    t = t + 4;
    assert x > 0;
    return 1;
}