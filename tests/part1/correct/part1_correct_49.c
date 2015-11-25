// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"

int main(int a)
{
	int i;
	int j;
	
	i=1;
	j=a;
	
	i = i + 1;
	
	j = j + i;
	
	assert(j == a + 2);
  return 0;
}
