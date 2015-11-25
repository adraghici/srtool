// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
    int i; int j; int k;
    i = j ? k : i;
    i = j ? i : k;
    assert(i == k);
    return i ? j : j;
}
