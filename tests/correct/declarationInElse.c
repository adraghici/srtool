// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"

int foo() {

    if( 1 == 1) {

    } else {

        int w;
        w = w;
        assert (w == w);
        w = w == w;
        assert (w == 1);
    }


    return 0;
}