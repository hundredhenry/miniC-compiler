#include <cstdio>
#include <iostream>

// clang++ driver.cpp addition.ll -o add

#ifdef _WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

extern "C" DLLEXPORT int print_int(int X) {
  fprintf(stderr, "%d\n", X);
  return 0;
}

extern "C" DLLEXPORT float print_float(float X) {
  fprintf(stderr, "%f\n", X);
  return 0;
}

extern "C" {
bool widening_casts();
bool true_plus_true();
}

int main() {
  // Depending on `true+true`, this may fail - need to justify behaviour
  // in report.
  if (widening_casts() && true_plus_true())
    std::cout << "PASSED Result: " << std::endl;
  else
    std::cout << "FAILED Result: " << std::endl;
}