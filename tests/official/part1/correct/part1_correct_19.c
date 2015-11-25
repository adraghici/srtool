// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int y;

int foo() {
    int i; int j;
    int k;
    int l;

    l = k ? 1 : 1;
    
    k = l && i && 0;

    i = k && y && (i && j);

    j = i && i;

    assert(l + 1);
    assert(k + 1);
    assert(i + 1);
    assert(j + 1);
    return 0;
}
