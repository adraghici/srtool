// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int c; int d;

int theproc()
  requires c >= 0, requires d >= 0, requires c < 10, requires d < c,
  ensures \result <= 10*c {

  int result;
  result = 0;
  int i;
  i = 0;
  while(i < c) {
    int j;
    j = 0;
    while(j < d) {
      j = j + 1;
      result = result + 1;
    }
    i = i + 1;
  }
  return result;
}
