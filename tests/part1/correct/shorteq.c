// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int blarp() {

    int a;
    int b;
    int c;

    assume a == b;
    assume a == c;

    assert a == b;

    return 2;    
}
