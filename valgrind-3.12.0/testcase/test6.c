#include <stdio.h>

void main(void)
{
	int a, b, x;
	read(0, &a, sizeof(int)); 
	read(0, &b, sizeof(int)); 
	if( a > 1)
  	x  = a;
	else 
		x =  b;	
}
