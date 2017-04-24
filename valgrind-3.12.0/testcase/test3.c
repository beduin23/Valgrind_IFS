#include<stdio.h>

void input(int* var) { 
  read(0, var, sizeof(int));
}

int main () {

  int a, b, x, y, z;
  input(&a);
  input(&b);

  x = b * 3;
  y = x - a;
  z = x + y;

  return 0;

}
