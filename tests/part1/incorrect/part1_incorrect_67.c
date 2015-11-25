// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"
int main()
{
	assert((2 | 3) == 1);
  return 0;
}
