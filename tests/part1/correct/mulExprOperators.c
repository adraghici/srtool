// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {

    int mul;
    mul = 8*6;
    assert mul == 48;
    mul = -8*6;
    assert mul == -48;
    mul = 8*-6;
    assert mul == -48;
    mul = -8*-6;
    assert mul == 48;
    mul = 8*6*2;
    assert mul == 96;
    
    int div;
    div = 48/6;
    assert div == 8;
    div = -48/6;
    assert div == -8;
    div = 48/-6;
    assert div == -8;
    div = -48/-6;
    assert div == 8;
    div = 48/6/2;
    assert div == 4;
    div = 48/0;
    assert div == 48;
    div = 0/48;
    assert div == 0;

    //mod
    assert (5%2) == 1;
    assert (5%-2) == 1;
    assert (-5%2) == -1;
    assert (-5%-2) == -1;
    assert (5%0) == 5;
    assert (0%2) == 0;

    //combined
    int a;
    a = 20/3*3;
    assert a == 18;
    a = 20*3/3;
    assert a == 20;
    a = 20%3*2/4;
    assert a == 1;
    a = 20%(3*2/4);
    assert a == 0;
    a = 5/2*2*5%3*4/4;
    assert a == 2;

    return 0;

}