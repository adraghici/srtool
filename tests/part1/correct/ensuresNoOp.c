int x;

int fun()
  ensures x == \old(x)
{
	return 1;
}
