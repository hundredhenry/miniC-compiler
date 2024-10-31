extern int print_int(int X);
extern float print_float(float X);

bool true_plus_true() { return true + true; }

bool widening_casts() {
  float bin_1;
  float bin_2;
  float bin_3;
  float bin_31;
  float bin_4;
  int bin_5;
  int bin_6;
  float bin_7;
  int bin_8;
  bool bin_9;
  float bin_1i;
  float bin_2i;
  float bin_3i;
  float bin_31i;
  float bin_4i;
  int bin_5i;
  int bin_6i;
  float bin_7i;
  int bin_8i;
  bool bin_9i;
  float assign_if;
  float assign_bf;
  int assign_bi;

  float f4;
  float f1;
  int i3;
  int i1;
  bool bf;
  bool bt;

  f4 = 4.0;
  f1 = 1.0;
  i3 = 3;
  i1 = 1;
  bf = false;
  bt = true;

  bin_1 = 4.0 + 1.0;
  bin_2 = 4.0 + 1;
  bin_3 = 4.0 + true;
  bin_31 = 4.0 + false;
  bin_4 = 3 + 1.0;
  bin_5 = 3 + 1;
  bin_6 = 3 + true;
  bin_7 = true + 1.0;
  bin_8 = true + 1;
  // This is minus to avoid ambiguity in meaning of true+true
  bin_9 = true - true;
  assign_if = 1;
  assign_bf = true;
  assign_bi = true;

  bin_1i = f4 + f1;
  bin_2i = f4 + i1;
  bin_3i = f4 + bt;
  bin_31i = f4 + bf;
  bin_4i = i3 + f1;
  bin_5i = i3 + i1;
  bin_6i = i3 + bt;
  bin_7i = bt + f1;
  bin_8i = bt + i1;
  bin_9i = bt - bt;

  print_float(bin_1);
  print_float(bin_2);
  print_float(bin_3);
  print_float(bin_31);
  print_float(bin_4);
  print_int(bin_5);
  print_int(bin_6);
  print_float(bin_7);
  print_int(bin_8);
  print_int(bin_9);

  return (
      (bin_1 == 5.0) && (bin_2 == 5.0) && (bin_3 == 5.0) && (bin_31 == 4.0) &&
      (bin_4 == 4.0) && (bin_5 == 4) && (bin_6 == 4) && (bin_7 == 2.0) &&
      (bin_8 == 2) && (bin_9 == false) && (bin_1i == 5.0) && (bin_2i == 5.0) &&
      (bin_3i == 5.0) && (bin_31i == 4.0) && (bin_4i == 4.0) && (bin_5i == 4) &&
      (bin_6i == 4) && (bin_7i == 2.0) && (bin_8i == 2) && (bin_9i == false) &&
      (assign_if == 1.0) && (assign_bf == 1.0) && (assign_bi == 1));
}