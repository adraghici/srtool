// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
    int a;
    a = 12;
    assert +a == 12;
    assert -a == -12;
    assert ~a == -13;
    assert !a == 0;
    assert !0 == 1;
    assert !(1==1) == 0;
    assert !(1!=1) == 1;

    assert - - ~a == -13;
    assert - ~ -a == -11;

    assert 3 - - 2 == 5;
    return 0;
}