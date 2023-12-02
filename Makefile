all: ppurse

ppurse:
	dune build bin/main.exe
	cp -f _build/default/bin/main.exe ppurse

clean:
	dune clean
	rm -f ppurse

parse_test: ppurse
	cd test-files && bash ./test -1 ../ppurse

typing_test: ppurse
	cd test-files && bash ./test -2 ../ppurse

exec_test: ppurse
	cd test-files && bash ./test -3 ../ppurse

test: ppurse
	cd test-files && bash ./test -all ../ppurse

.PHONY: all clean parse_test typing_test exec_test test
