// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"
int main()
{
 int i;
 int c;
 
 if(c)
 {
  i = 2;
 }
 else
 {
  i = 3;
 }
 
 if(c)
 {
  assert(i != 2);
 }
 else
 {
  assert(i != 3);
 }

  return 0;
}