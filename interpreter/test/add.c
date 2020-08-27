
__attribute__((visibility("default")))

int add(int a, int b) {
      return a + b*b;
}

int add1(int a, int b) {
    if (b < 5)
      return add(a,5);
    else
      return a + b;
}

int add2(int a, int b) {
      return b*b;
}

int add3(int a, int b) {
    int tmp;
    if (b < 5) {
        tmp = a;
        a = b;
        b = tmp;
    }
    
    return a;
}

