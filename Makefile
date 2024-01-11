all: ppurse
sources  := $(shell find . -regextype sed -regex "\./\(lib\|bin\)/.*\|\./dune-project")

ppurse: $(sources)
	@dune build bin/main.exe
	@cp -f _build/default/bin/main.exe ppurse

clean:
	rm -rf ppurse _build
	rm -f "./test-files/**/*.s"
	rm -f "./spago/src/*.s"
	rm -f ./test-files/a.out

parsing-test: ppurse
	@cd test-files && bash ./test -1 ../ppurse

typing-test: ppurse
	@cd test-files && bash ./test -2 ../ppurse

exec-test: ppurse
	@cd test-files && bash ./test -3 ../ppurse

test: ppurse
	@cd test-files && bash ./test -all ../ppurse

spago-run: ./spago/src/Main.purs
	@bash -c "cd ./spago && spago -q build > /dev/null 2>&1"
	@bash -c "cd ./spago && spago -q run" | tee spago/src/spago.out

ppurse-run: ./spago/src/Main.purs ppurse
	@./ppurse --permissive spago/src/Main.purs > spago/src/Main.alloc
	@gcc -g -z noexecstack -no-pie spago/src/Main.s -o spago/src/a.out
	@./spago/src/a.out | tee spago/src/ppurse.out

diff:
	@$(MAKE) spago-run > /dev/null
	@$(MAKE) ppurse-run > /dev/null
	@diff spago/src/ppurse.out spago/src/spago.out

dev:
	dune build -w

new-test:
ifeq ($(name),)
	@echo "Missign test name. Please add 'name=(test name)'"
else
	@echo "Creating new test '$(name).purs'..."
	@cp ./spago/src/Main.purs "./test-files/exec/$(name).purs"
	@bash -c "cd ./spago && spago -q build > /dev/null 2>&1"
	@echo ""
	@echo "Spago output:"
	@bash -c "cd ./spago && spago -q run" | tee "./test-files/exec/$(name).out"
endif

.PHONY: all clean parsing-test typing-test exec-test test spago-run ppurse-run diff dev
