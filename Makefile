COQFILES = $(wildcard src/*.v)

all: $(COQFILES:.v=.vo)

%.vo: %.v
	coqc -Q src FBF $<
