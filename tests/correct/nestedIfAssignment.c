// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(){
    int x;
    x = 0;

    if(1==1){
        x = 1;
        if(2==2){
            x = 2;
        }
    } else {
        x = 3;
    }

    assert x == 2;

    return 0;
}