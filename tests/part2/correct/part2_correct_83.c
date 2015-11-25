// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int g;

int magic_number()
  ensures ((!\result) & (-1)) == -1
{
  while(1) invariant 1 {
      havoc g;
  }
  return 0;
}

int crazy() {
  int t;
  t = magic_number();
  assert 0;
  return 2;
}
