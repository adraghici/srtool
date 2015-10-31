// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(){
    int a;
    int x;
    x = 0;

    if(a==1){
        int x;
        x = 4;
        assert x == 4;
        if(a==2){
            int x;
            x = 5;
            assert x == 5;
        }
        assert x == 4;
    } else {
        int x;
        x = 6;
        assert x == 6;
    }

    assert x == 0;

    return 0;
}