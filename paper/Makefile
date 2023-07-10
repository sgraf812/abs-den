# -halt-on-error: Halts on first error, rather than prompting the user
PDFLATEX := pdflatex -halt-on-error

main: comp-trace.pdf

.PHONY: main quick watch clean

comp-trace.pdf : macros.tex intro.tex problem.tex problem.tex vanilla.tex eventful.tex essence.tex abstractions.tex related-work.tex

comp-trace-ext.tex: *.tex
	cat comp-trace.tex | sed -e 's/^%\\extended/\\extended/g' > comp-trace-ext.tex

%.pdf: %.tex macros.tex references.bib
	$(PDFLATEX) $*
	bibtex $*
	$(PDFLATEX) $*
	$(PDFLATEX) $*

quick: comp-trace.tex macros.tex
	$(PDFLATEX) comp-trace
	$(PDFLATEX) comp-trace

quick-ext: comp-trace-ext.tex macros.tex
	$(PDFLATEX) comp-trace-ext
	$(PDFLATEX) comp-trace-ext

watch:
	ls *.tex | entr make quick

watch-ext:
	ls *.tex | entr make quick-ext

clean:
	git clean -fxd
