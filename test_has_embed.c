#if __has_embed("test_has_embed.c")
#error "has embed"
#endif
int main() {
    return 0;
}
