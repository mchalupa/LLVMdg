void test_assert(int);
extern int glob;
extern int *glob_ptr(int *);

void foo2() {
        int x;
        test_assert(*glob_ptr(&x) == 3);
}

int main(void) {
        int x;
        *glob_ptr(&x) = 3;
        foo2();
	return 0;
}