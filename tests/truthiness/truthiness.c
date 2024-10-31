extern int print_int(int X);
extern float print_float(float X);

int foo() {
  float x;
  x = 5.0;
  if (x) {
    return 5;
  }
  return 0;
}