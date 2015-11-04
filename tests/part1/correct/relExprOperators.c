// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo(){

    // Less Than
    int lt;
    lt = (5<6);
    assert lt == 1;
    lt = (6<5);
    assert lt == 0;
    lt = (5<6<2);
    assert lt == 1;
    lt = (5<6<-1);
    assert lt == 0;

    // Greater Than
    int gt;
    gt = (5>6);
    assert gt == 0;
    gt = (6>5);
    assert gt == 1;
    gt = (5>6>2);
    assert gt == 0;
    gt = (5>6>-1);
    assert gt == 1;
    
    // Less Than
    int lte;
    lte = (5<=6);
    assert lte == 1;
    lte = (6<=5);
    assert lte == 0;
    lte = (6<=6);
    assert lte == 1;
    lte = (5<=6<=2);
    assert lte == 1;
    lte = (5<=6<=-1);
    assert lte == 0;
    lte = (5<=6<=8);
    assert lte == 1;
    lte = (7<=6<=0);
    assert lte == 1;
    lte = (6<=7<=1);
    assert lte == 1;

    // Greater Than
    int gte;
    gte = (5>=6);
    assert gte == 0;
    gte = (6>=5);
    assert gte == 1;
    gte = (6>=6);
    assert gte == 1;
    gte = (5>=6>=2);
    assert gte == 0;
    gte = (5>=6>=-1);
    assert gte == 1;
    gte = (7>=6>=0);
    assert gte == 1;

    //Combined
    int a;
    a = 7>6 >= 1 < 0 >= -2;
    assert a == 1;

    return 1;
}