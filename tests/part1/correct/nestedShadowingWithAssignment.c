// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(){
    int a;
    int x;
    x = 0;

    if(a==1){
        x = 1;
        int x;
        x = 4;
        if(a==2){
            x = 2;
            int x;
            x = 5;
        }
    } else {
        x = 3;
        int x;
        x = 6;
    }

    if(a==1){
        assert x == 1;
    } else {
        assert x == 3;
    }

    return 0;
}