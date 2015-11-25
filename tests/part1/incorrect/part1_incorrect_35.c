// RUN: %tool "%s" > "%t"
// RUN: %diff %INCORRECT "%t"

int foo()
  ensures 0 {
    int x;
    x = 4;
    return 0;
}
