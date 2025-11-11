int case_58()
{
	char * s;
	
	s = "abc" "def";
	if(s[0] != 'a') return 1;
	if(s[1] != 'b') return 2;
	if(s[2] != 'c') return 3;
	if(s[3] != 'd') return 4;
	if(s[4] != 'e') return 5;
	if(s[5] != 'f') return 6;
	if(s[6] != 0) return 7;
	
	return 0;
}

int
case_57()
{
	char a[16], b[16];
	
	if(sizeof(a) != sizeof(b))
		return 1;
	return 0;
}

struct T44;

struct T44 {
	int x;
};

int
case_44()
{
	struct T44 v;
	{ struct T44 { int z; }; }
	v.x = 2;
	if(v.x != 2)
		return 1;
	return 0;
}


struct { int a; int b; int c; } s_47 = {1, 2, 3};

int
case_47()
{
	if (s_47.a != 1)
		return 1;
	if (s_47.b != 2)
		return 2;
	if (s_47.c != 3)
		return 3;

	return 0;
}


typedef struct {
	int a;
	union {
		int b1;
		int b2;
	};
	struct { union { struct { int c; }; }; };
	struct {
		int d;
	};
} s_46;

int
case_46()
{
	s_46 v;
	
	v.a = 1;
	v.b1 = 2;
	v.c = 3;
	v.d = 4;
	
	if (v.a != 1)
		return 1;
	if (v.b1 != 2 && v.b2 != 2)
		return 2;
	if (v.c != 3)
		return 3;
	if (v.d != 4)
		return 4;
	
	return 0;
}


struct s_43 {
    int x;
    struct {
        int y;
        int z;
    } nest;
};

int
case_43() {
    struct s_43 v;
    v.x = 1;
    v.nest.y = 2;
    v.nest.z = 3;
    if (v.x + v.nest.y + v.nest.z != 6)
        return 1;
    return 0;
}



int
case_39()
{
	void *p;
	int x;
	
	x = 2;
	p = &x;
	
	if(*((int*)p) != 2)
		return 1;
	return 0;
}


int
hore_kkk()
{
	int x, *p;

	if (sizeof(0) < 2)
		return 1;
	if (sizeof 0 < 2)
		return 1;
	if (sizeof(char) < 1)
		return 1;
	if (sizeof(int) - 2 < 0)
		return 1;
	if (sizeof(&x) != sizeof p)
		return 1;
	return 0;
}


int
f()
{
	return 100;
}

int
panggil_f()
{
	if (f() > 1000)
		return 1;
	if (f() >= 1000)
		return 1;
	if (1000 < f())
		return 1;
	if (1000 <= f())
		return 1;
	if (1000 == f())
		return 1;
	if (100 != f())
		return 1;
	return 0;
}




long unsigned int strlen(char *);


int
hitunghuruf()
{
	char *p;
	
	p = "hello";
	return strlen(p) - 5;
}


int
majumundur()
{
	start:
		goto next;
		return 1;
	success:
		return 0;
	next:
	foo:
		goto success;
		return 1;
}

int
foo(int a, int b)
{
	return 2 + a - b;
}

int
main()
{
	struct { int x; int y; } s;
	
	s.x = 3;
	s.y = 5;

    int u = foo(1, 3);
	return s.y - s.x - 2 * u; 
}
