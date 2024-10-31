extern int print_int(int X);
extern float print_float(float X);

int nested_blocks(int x) {
  // i'm a massive fan of the formatting here thanks clang-format
  {
    {
      {
        {
          {
            {
              {
                {
                  {
                    {
                      { return x; }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

bool strange_assoc() {
  float lhs;
  float rhs_1;
  float rhs;
  lhs = 4.0 / (3.0 / 2.0) / 7.0;
  rhs_1 = 3.0 / 2.0;
  rhs = 4.0 / rhs_1 / 7.0;
  //    print_float(lhs);
  //    print_float(rhs);
  return lhs == rhs;
}

int void_param(void) { return 0; }

int example_scope() {
  int x;
  int y;
  x = 2 + 3;
  y = 2;
  while (y > 0) {
    int x;
    bool cond;
    cond = true;
    while (cond) {
      x = 17;
      cond = false;
    }
    x = 2;
    y = y - x;
  }
  return x;
}

int expr_stmt() {
  int x;
  x = 5;
  x;
  return 0;
}

int shadowing() {
  int nested_blocks;
  nested_blocks = 5;
  return nested_blocks(nested_blocks);
}

bool drive() {
  return (nested_blocks(5) != 5 || shadowing() != 5 || example_scope() != 5 ||
          !strange_assoc() || expr_stmt() != 0 || void_param() != 0);
}