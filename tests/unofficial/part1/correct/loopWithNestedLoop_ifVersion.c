// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int func()
{
    int a;
    int b;
    int c;
    a = 10;
    b = 5;
	assert a >= 0 && b == 5;
	havoc c;
	havoc a;
	assume a >= 0 && b == 5;
    if(a > 0)
    {
        if(b == 5){
            c = 3;
        }

        assert c >= 0;
        havoc c;
        assume c >= 0;

        if(c == 3)
        {
            c = 4;
            assert c >= 0;
            assume 0;
        }

        a = a - 1;
		assert a >= 0 && b == 5;
		assume 0;
    }
    b = 2;
    return 0;
}
