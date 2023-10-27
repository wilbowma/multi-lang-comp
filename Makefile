all: prisc2021-abstract.pdf

prisc2021-abstract.pdf: prisc2021-abstract.scrbl wilbowma.bib prisc-extra.tex
	scribble ++style prisc-extra.tex --pdf $<

wilbowma.bib: ~/workspace/org/bib.bib
	cp $< $@
