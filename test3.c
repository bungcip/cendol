typedef int my_type;
int main(void) {
    int my_type = 1;
    {
        my_type my_type_2 = 2; // this should fail because my_type is a variable in the outer scope
    }
}
