build: src/ail.c src/scanner.c src/parser.c
	gcc -c -g -fPIC -Wall src/ail.c src/scanner.c src/parser.c -I src/
	gcc -shared -o ail.so ail.o scanner.o parser.o

src/scanner.c: src/scanner.re
	re2c -o src/scanner.c src/scanner.re

src/parser.c: src/parser.y src/lemon.c
	lemon -q src/parser.y
	cat src/lemon.c >> src/parser.c

buildtest: build tests.c
	gcc -c -g -Wall tests.c -I src/
	gcc tests.o ./ail.so -lyajl -lcunit -o tests

test: buildtest
	./tests

debugtest: buildtest
	gdb ./tests

install: build test
	@echo "****NOT IMPLEMENTED YET****"

clean:
	-@rm ./tests
	-@rm ./*.o
	-@rm ./*.so
	-@rm ./*.out
