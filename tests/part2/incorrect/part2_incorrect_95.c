// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int theproc() {

  int a;
  a = 20;
  while(a < 25) {
    assume a != 19;
    assume a != 18;
    assume a != 17;
    a = a + 1;
  }
  assert a == 24;
  return 0;
}
