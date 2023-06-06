paper.pdf: paper.tex references.bib
	pdflatex $< -o $@
	pdflatex $< -o $@
	bibtex paper
	pdflatex $< -o $@

paper.tex: paper.lhs
	lhs2TeX $< -o $@

.PHONY: clean
clean:
	rm -f *.pdf *.out *aux *bbl *blg *log *toc *.ptb *.tod *.fls *.fdb_latexmk *.lof

