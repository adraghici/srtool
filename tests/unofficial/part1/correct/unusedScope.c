// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int blarp() {

    int x;
    x = 3;
    assert x == 3;
    {
        int y;
        y = 4;
        assert y == 4;
        {
            int z;
            z = 2;
        }
    }
    assert x == 3;

    int a;
    if(a == 1){
        int zz;
        zz = 100;
    }

    return 0;
}