// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int func()
{
    int a;
    int b;
    int c;
    a = 10;
    b = 5;
    while(a > 0)
      invariant a >= 0,
      invariant b == 5
    {
        if(b == 5){
            c = 3;
        }

        while(c == 3)
          invariant c >= 3
        {
            c = 4;
        }
        a = a - 1;
    }
    b = 2;
    return 0;
}