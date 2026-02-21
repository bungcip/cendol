typedef signed int int32_t;
typedef signed long int64_t;


int
main()
{
	int32_t x;
	int64_t l;

	x = 0;
	l = 0;

	x = ~x;
	if (x != 0xffffffff)
		return 1;

	l = ~l;
	if (l != 0xffffffffffffffff)
		return 2;


	return 0;
}
