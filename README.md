# [Petit Purescript](https://github.com/desfreng/PetitPureScript)

This is my project for the [Compilation course](https://www.lri.fr/~filliatr/ens/compil/index.html) given by Jean-Christophe Filliâtre at the ENS in 2023.

The majority of the tests are those proposed at this address: https://www.lri.fr/~filliatr/ens/compil/projet/tests/

Use `make` to build the `ppurse` compiler, and `make clean` to clean the directory of all compiled files.

The following tests are available:
- Tests on parsing using the command `make parsing-test`.
- Semantic analysis tests using the command `make typing-test`.
- Code production tests using the command `make exec-test`.

To run all the test, you can use `make test`.

The following commands can be used to facilitate test development:
- To run `spago` on the file `Main.purs` in the `spago` directory use: `make spago-run`.
- To run `ppurse` on the same file as above use: `make ppurse-run`.
- To checks that `spago` and `ppurse` outputs the same, use `make diff`.
- To add the file `Main.purs` as a new test use `make new-test name=...`.

Happy Hacking!