src/%.tab.c: src/%.y
	bison --output=$@ $< -v -Wall

src/lex.%.c: src/%.l
	flex --header-file=src/lex.$*.h -P $* --outfile=$@ $<

SRC = src/folAST.c src/cli.c src/topoSort.c src/proof.c src/formula.c

bin/proveMath: $(SRC) src/lex.fol.c src/fol.tab.c src/folAST.h src/formula.h src/proof.h
	mkdir -p bin
	gcc -g $(SRC) src/lex.fol.c src/fol.tab.c -o bin/proveMath

build: bin/proveMath

prove:
	bin/proveMath

clean:
	rm bin/* src/*~ src/lex.*.c src/*.tab.c src/*.tab.h
