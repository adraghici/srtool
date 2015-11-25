// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int theproc() {
 
  int c;
  if(c < 0 && c >= -2147483647) {
    assert -c >= 0;
  }
  return 0;
}
