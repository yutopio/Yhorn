
all: algo.pdf

clean:
	rm *.aux *.bbl *.dvi *.pdf *.log

.SUFFIXES: .tex .aux .bib .bbl .dvi .pdf
.SECONDARY:

%.dvi : %.tex

%.aux:
	latex $(basename $@)

%.bbl: %.aux biblio.bib
	bibtex $(basename $@)

.bbl.dvi:
	latex $(basename $<)
	touch $(basename $<).bbl

%.pdf: %.dvi %.tex biblio.bib
	pdflatex $(basename $<)
	touch $(basename $<).bbl
	touch $(basename $<).dvi
	touch $(basename $<).pdf
