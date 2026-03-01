typedef int my_type;

int main(void) {
    float my_type = 1.0f; // Shadows typedef in outer scope
    if (sizeof(my_type) != sizeof(float)) return 1;
    return 0;
}
