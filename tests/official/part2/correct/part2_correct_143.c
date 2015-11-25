// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"


int main()
{
 int i;
 int iterations;
 i=0;
 
 // make iterations positive, but otherwise unconstrained
 assume(iterations > 0);
 
 while(i < iterations)
 {
  i = i + 1;
 }
 
 assert(i == iterations);
 
  return 0;
}

