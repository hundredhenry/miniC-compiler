extern int print_int(int X);
extern float print_float(float X);

int foo() {
  int x;
  int y;
  x = 2 + 3;
  y = 2;
  while (y > 0) {
    int x;
    x = 2;
    y = y - x;
  }
  print_int(x);
  return x;
}