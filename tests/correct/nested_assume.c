// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {
    int a;
    int b;
    int c;
    int d;

    int q;
    int r;
    int x;
    int y;
    
    assume a >= b >= c >= q >= r >= x >= y > -2147483647;
    assume a <= b <= c <= q <= r <= x <= y < 2147483648;

    if(a > b){
        q = 13;
        assume r == 14;

        if(c >= d) {
            x = 2;
            if(c == d){
                assume y == 3;
            } else {
                assume y > 4;
            }
        }

        if(c <= d)
        {
            x = 1;
            if(c == d){
                assume y == 5;
            } else {
                assume y > 6;
            }
        }
    } else {
        x = 10;
        y = 11;
    }
    assert y > x;
    return 0;
}