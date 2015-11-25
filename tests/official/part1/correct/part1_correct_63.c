// RUN: %tool "%s" > "%t" 
// RUN: %diff %CORRECT "%t"
int main()
{
    int i;
    int j;
    int p;
	i=1+9;
	j=2+8;
	
	p = (i == j);
	assert(p);
  return 0;
}
