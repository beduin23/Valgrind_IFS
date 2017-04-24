#include<stdio.h>

void func(int a) { 
  
}

int main () {

	int a;
	read(0, &a, sizeof(int));
  int (*fn) (int);
	fn = func;
	fn(a);
	

  return 0;

}
