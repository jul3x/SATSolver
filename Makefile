
.PHONY: all

all: sat-solver tester

tester: Tester.hs
	ghc -o tester Tester.hs

sat-solver: sat-solver.hs Parser.hs Utils.hs
	ghc -o sat-solver sat-solver.hs

clean:
	rm sat-solver tester *.hi *.o
