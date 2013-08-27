
PDF = $(wildcard *.pdf)
XBB  = $(PDF:.pdf=.xbb)

all: $(XBB)

clean:
	-rm -f *.xbb

.SUFFIXES: .xbb .pdf

.pdf.xbb:
	ebb -x $<
