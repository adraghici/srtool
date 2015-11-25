// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int theproc(int a, int b)
  requires (a % 5) == 0,
  requires (b % 15) == 0,
  requires a < 100000,
  requires b > a + 100,
  ensures a > 100 && b > 200 ? ((a % \result) == 0) : 1
{
  int x;
  x  = 2;
  if(a > 100) {
    int done;
    done = 0;
    while(!done) {
      if((a % x) == 0) {
	if((b % x) == 0) {
          done = 1;
	}
      }
      if(b > 200) {
        if(!done) {
          x = x + 1;
        }
      }
    }
  }
  return x;
}
