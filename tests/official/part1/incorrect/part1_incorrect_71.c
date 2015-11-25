// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int main()
{
	assert((1 || 2) == 3);
  return 0;
}
