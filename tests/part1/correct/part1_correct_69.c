// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main()
{
	assert((10 ? 11 : 0) == 11);
  return 0;
}
