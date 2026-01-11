#define PASTE(a, b) a ## b
#define XPASTE(a, b) PASTE(a, b)
#define UNIQUE(name) XPASTE(name, __COUNTER__)
UNIQUE(var)
