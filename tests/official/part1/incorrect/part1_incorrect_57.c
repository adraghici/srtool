// RUN: %tool "%s" > "%t" 
// RUN: %diff %INCORRECT "%t"

int main()
{
    int i;
	i = 1;
	i = i + 1;
	
	assert(i != 2);
  return 0;
}
