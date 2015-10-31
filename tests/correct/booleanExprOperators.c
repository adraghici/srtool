// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(){

    int a;
    a = 8 | 0;
    assert a == 8;
    a = 8| 1;
    assert a == 9;
    a = 8 & 0;
    assert a == 0;
    a = 8 & 1;
    assert a == 0;
    a = 8 & 11;
    assert a == 8;
    a = 8 ^ 11;
    assert a == 3;

    a = 1 | 2 | 4 | 8;
    assert a == 15;

    a = 6 & 5 & 15 & 31;
    assert a == 4;

    a = 6 ^ 5 ^ 4 ^ 8;
    assert a == 15;

    a = 8 ^ 14 | 5 & -9;
    assert a == 7;


    return 0;
}