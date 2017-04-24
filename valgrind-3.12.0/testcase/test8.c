#include<stdio.h>
int main() {

	FILE *file;
  char buf[100];
	file = fopen("a.txt", "rb");
	fseek(file, 0, SEEK_SET);
	fread(buf, 10, 1, file);
	fclose(file);
	
	return 0;

}
