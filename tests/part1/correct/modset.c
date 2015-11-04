// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int a;
int b;
int c;

int foo(){

    int d;
    d = 2;
    b = b +1;
    if(a > 2){
        a = 2;
    }
    d = 4;

    return 0;
}