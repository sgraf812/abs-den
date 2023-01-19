# -halt-on-error: Halts on first error, rather than prompting the user
PDFLATEX := pdflatex -halt-on-error

main: comp-trace.pdf

.PHONY: main quick watch clean

comp-trace.tex: *.lhs
	lhs2TeX --poly comp-trace.lhs > comp-trace.tex

comp-trace-ext.tex: *.lhs
	lhs2TeX --poly appendix.lhs >appendix.tex
	lhs2TeX --poly comp-trace.lhs | sed -e 's/^%\\appendixonly/\\appendixonly/g' > comp-trace-ext.tex

%.pdf: %.tex macros.tex references.bib
	$(PDFLATEX) $*
	bibtex $*
	$(PDFLATEX) $*
	$(PDFLATEX) $*

quick: comp-trace.tex macros.tex
	$(PDFLATEX) comp-trace
	$(PDFLATEX) comp-trace

watch:
	ls *.tex *.lhs | entr make quick

clean:
	git clean -fxd
