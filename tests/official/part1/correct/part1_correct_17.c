// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
    int i; int j;
    int k;
    int l;

    k = !i;
    l = i;
    j = k ? 4 : l ? 8 : 3;
    assert j == 4 || j == 8;
    return !!!!!!i;
}
