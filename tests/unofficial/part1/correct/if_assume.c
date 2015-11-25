// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
    int a;
    int b;
    int x;
    int y;

    if(a > b) {
        x = 1;
        assume y == 2;
    } else {
        x = 2;
        assume y > 3;
    }
    assert y > x;
    return 0;
}