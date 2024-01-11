all: ppurse
sources  := $(shell find . -regextype sed -regex "\./\(lib\|bin\)/.*\|\./dune-project")

ppurse: $(sources)
	dune build bin/main.exe
	cp -f _build/default/bin/main.exe ppurse

clean:
	dune clean
	rm -f ppurse

parsing_test: ppurse
	cd test-files && bash ./test -1 ../ppurse

typing_test: ppurse
	cd test-files && bash ./test -2 ../ppurse

exec_test: ppurse
	cd test-files && bash ./test -3 ../ppurse

test: ppurse
	cd test-files && bash ./test -all ../ppurse

spago-run: spago/src/Main.purs
	@bash -c "cd ./spago && spago -q build 2>&1 > /dev/null"
	@bash -c "cd ./spago && spago -q run" | tee spago/src/spago.out

ppurse-run: spago/src/Main.purs ppurse
	@./ppurse spago/src/Main.purs > /dev/null
	@gcc -g -z noexecstack -no-pie spago/src/Main.s -o spago/src/a.out
	@./spago/src/a.out | tee spago/src/ppurse.out

.PHONY: all clean parsing_test typing_test exec_test test
