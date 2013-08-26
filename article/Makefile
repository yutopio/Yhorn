
NAME = algo

all: $(NAME).pdf

clean:
	rm *.aux *.bbl *.dvi *.pdf *.log

.SUFFIXES: .tex .aux .bib .bbl .bb .dvi .pdf
.SECONDARY:

.pdf.bb:
	ebb $<

iscs-thesis.cls: iscs-thesis.ins iscs-thesis.dtx
	platex iscs-thesis.ins

$(NAME).dvi: iscs-thesis.cls $(NAME).tex $(NAME).bbl
	platex $(NAME)

algo.dvi:
	platex algo

$(NAME).aux: $(NAME).tex
	platex $(NAME)

$(NAME).bbl: $(NAME).aux biblio.bib
	bibtex $(NAME)

$(NAME).pdf: $(NAME).dvi
	dvipdfmx $(NAME)
