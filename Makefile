all: prisc2021-abstract.pdf

prisc2021-abstract.pdf: prisc2021-abstract.scrbl wilbowma.bib
	scribble ++style prisc-extra.tex --pdf $<

wilbowma.bib: ~/workspace/org/bib.bib
	cp $< $@
