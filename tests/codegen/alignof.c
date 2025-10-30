int main() {
    int a = _Alignof(int);
    int b = _Alignof(char);
    int c = _Alignof(short);
    int d = _Alignof(long);
    int e = _Alignof(long long);
    int f = _Alignof(float);
    int g = _Alignof(double);
    int h = _Alignof(int *);
    int i = _Alignof(int[10]);
    struct S {
        char c;
        int i;
    };
    int j = _Alignof(struct S);
    return a + b + c + d + e + f + g + h + i + j;
}
