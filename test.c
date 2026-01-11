#define PASTE(a, b) a ## b
#define UNIQUE(name) PASTE(name, __COUNTER__)
UNIQUE(var)
