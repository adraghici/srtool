// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int theproc(int a, int b)
  requires (a % 5) == 0,
  requires (b % 10) == 0,
  ensures ((a % \result) == 0),
  ensures ((b % \result) == 1)
{
  int x;
  x = 2;
  int done;
  done = 0;
  while(!done) {
    if((a % x) == 0) {
      if((b % x) == 0) {
        done = 1;
      }
    }
    if(!done) {
      x = x + 1;
    }
  }
  return x;
}
