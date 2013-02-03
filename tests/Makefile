
TEST = $(wildcard *.txt)
RET  = $(TEST:.txt=.dummy)

all: $(RET)

.SUFFIXES: .dummy .txt
.IGNORE:

.txt.dummy:
	../yhorn.opt $<
