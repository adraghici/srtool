// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int blarp() {

    int x;
    x = 3;
    assert x == 3;
    {
        int x;
        x = 4;
        assert x == 4;

        {
            x = x + 1;
            assert x == 5;
            int x;
            x = 10;
            assert x == 10;
        }

        x = x + 2;
        //assert x == 6;
    }

    return 0;
}
