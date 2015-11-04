// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
    int a;
    a = 7-4+2;
    assert a == 5;
    return 0;
}