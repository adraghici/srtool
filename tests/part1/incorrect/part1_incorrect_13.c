// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo() {
    int k;
    int l;
    int i;
    int j;
    
    k = !!i;
    l = i;
    j = k ? 4 : l ? 8 : 3;
    assert j == 4 || j == 8;
    return !!!!!!i;
}
