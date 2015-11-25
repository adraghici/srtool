// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"
int main()
{
	assert(1+1 == 3);
  return 0;
}
