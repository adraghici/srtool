// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int blarp() {

    int a;
    int b;
    int c;
    int d;
    int e;
    int f;
        
    assume a < b;
    assume b <= c;
    assume c > d;
    assume d > e;
    assume e <= f;

    int temp;

    temp = a;
    a = b;
    b = c;
    c = temp;

    temp = d;
    d = e;
    e = f;
    f = temp;

    assert b < c;
    assert c <= a;
    assert a < e;
    assert e > f;
    assert f >= d;

    assert b < a;
    assert b <= a;
    assert b < e;
    assert b <= e;
    assert e > d;
    assert e >= d;

    return e < e;
    
}
