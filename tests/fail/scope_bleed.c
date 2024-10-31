int bar() {
    // x is not defined, but exists in dynamic scope of caller
    return x;  // should `x` be in scope from `foo`?
}

void foo() {
    int x;
    x = 4;
    bar();
}
