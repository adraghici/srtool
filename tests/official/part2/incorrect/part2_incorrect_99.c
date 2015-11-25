// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int x;
int y;

int theproc(int a)
  requires a <= 50 {

  x = 0;
  assume y == x;
  while(x < a) {
    x = x + 1;
    y = y + 2;
  }
  assert y == 3*x;
  return 0;
}
