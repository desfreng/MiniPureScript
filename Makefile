all: ppurse

ppurse:
	dune build bin/main.exe
	cp -f _build/default/bin/main.exe ppurse

clean:
	dune clean
	rm -f ppurse

parse_test: ppurse
	bash tests/test -v1 ../ppurse

typing_test: ppurse
	bash tests/test -v2 ../ppurse

exec_test: ppurse
	bash tests/test -v3 ../ppurse

test: ppurse
	bash tests/test -all ../ppurse

.PHONY: all clean ppurse
