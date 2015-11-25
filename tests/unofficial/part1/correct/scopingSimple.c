// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int blarp() {
    int x;                  //x0
    x = 4;                  //x1 = 4
    assert x == 4;

    {
        x = x + 1;          //x2 = x1 + 1
        assert x == 5;
        int x;              //x3
        x = 10;             //x4 = 10
        assert x == 10;
    }                       //x5 = x2

    x = x + 2;              //x6 = x5 +2
    assert x == 7;


    return 0;
}