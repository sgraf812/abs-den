# -halt-on-error: Halts on first error, rather than prompting the user
PDFLATEX := pdflatex -halt-on-error

main: abs-den.pdf

.PHONY: main quick watch clean

abs-den.pdf : macros.tex intro.tex problem.tex problem.tex vanilla.tex eventful.tex essence.tex abstractions.tex related-work.tex

abs-den-ext.tex: *.tex
	cat abs-den.tex | sed -e 's/^%\\extended/\\extended/g' > abs-den-ext.tex

appendix.pdf: abs-den-ext.pdf
	nix run nixpkgs#pdftk -- abs-den-ext.pdf cat 28-end output appendix.pdf

supplemental.zip: appendix.pdf
	zip -j supplemental.zip appendix.pdf ../agda/*.agda

abs-den.tex: *.lhs
	LANG=C.UTF-8 lhs2TeX --poly -o $@ abs-den.lhs

abs-den.hs: *.lhs
	LANG=C.UTF-8 lhs2TeX --newcode -o $@ abs-den.lhs

%.pdf: %.tex macros.tex references.bib
	$(PDFLATEX) $*
	bibtex $*
	$(PDFLATEX) $*
	$(PDFLATEX) $*

quick: abs-den.tex macros.tex
	$(PDFLATEX) abs-den
	$(PDFLATEX) abs-den

quick-ext: abs-den-ext.tex macros.tex
	$(PDFLATEX) abs-den-ext
	$(PDFLATEX) abs-den-ext

test: *.lhs
	LANG=C.UTF-8 ghc -pgmL lhs2TeX -optL--pre -fno-code -W abs-den.lhs

watch:
	ls *.lhs *.tex | entr -n make quick

watch-ext:
	ls *.lhs *.tex | entr -n make quick-ext

watch-test:
	ls *.lhs | entr -n make test

clean:
	git clean -fxd
