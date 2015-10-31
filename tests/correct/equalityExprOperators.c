// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(){
    int a;
    a = 6 == 6 == 8 == 8;
    assert a == 0;
    a = (6 == 6) == (8 == 8);
    assert a == 1;
    a = 6 == 6 != 8 == 8;
    assert a == 0;
    a = 6 == 6 != 8 == 1;
    assert a == 1;

    return 0;
}