// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {

    int a;
    a = 20+20+20+30;
    assert a == 90;

    a = 90-20-20-20-30;
    assert a == 0;

    a = 90-20+20-20+30;
    assert a == 100;

    return 0;
}