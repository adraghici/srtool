// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {

    int x;
    x = 2;
    if( 1 == 1) {
        x = 5;
        int x;
        x = 3;
    } else {
        x = 6;
        int x;
        x = 4;
    }

    assert x == 5;

    return 0;
}