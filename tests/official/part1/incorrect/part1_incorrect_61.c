// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int main()
{
	assert(!1 == -2);
  return 0;
}
