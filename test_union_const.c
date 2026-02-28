union U {
  const int x;
  int y;
};

void foo() {
  union U u;
  u.y = 1;
  union U u2 = { .y = 2 };
  u = u2;
}
