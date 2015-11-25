// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo() {
    int i;
    int j;
    int k;
    i = j ? k : k;
    i = j ? j : k;
    assert(i == k);
    return i ? j : j;
}
