// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int main()
{
	assert(~1 == 0);
  return 0;
}
