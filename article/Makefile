
NAME = thesis

all: $(NAME).pdf

clean:
	-rm -f iscs-thesis.cls
	-rm -f *.aux *.bbl *.blg *.log *.out *.toc *.dvi *.pdf

.SUFFIXES: .tex .aux .bib .bbl .dvi .pdf
.SECONDARY:

iscs-thesis.cls: iscs-thesis.ins iscs-thesis.dtx
	platex iscs-thesis.ins

$(NAME).dvi: iscs-thesis.cls $(NAME).tex $(NAME).bbl
	platex $(NAME)

algo.dvi:
	platex algo

$(NAME).aux: $(NAME).tex
	(cd figures; make)
	platex $(NAME)

$(NAME).bbl: $(NAME).aux biblio.bib
	bibtex $(NAME)

$(NAME).pdf: $(NAME).dvi
	dvipdfmx $(NAME)
