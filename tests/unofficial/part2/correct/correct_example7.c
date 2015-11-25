// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

// You may be surprised that this is correct

int foo()
candidate_requires 0
{
  int t;
  t = qox();
  return 0;
}

int bar()
candidate_requires 0 {
  int t;
  t = foo();
  return 0;
}

int baz()
candidate_requires 0 {
  int t;
  t = bar();
  return 0;
}

int qox()
candidate_requires 0 {
  int t;
  t = baz();
  return 0;
}
