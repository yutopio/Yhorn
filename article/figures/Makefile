
PDF = $(wildcard *.pdf)
RET = $(PDF:.pdf=.eps)

all: $(RET)

.SUFFIXES: .pdf .ps .eps

.pdf.ps:
	pdf2ps $<

.ps.eps:
	ps2eps $<
