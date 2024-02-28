# -halt-on-error: Halts on first error, rather than prompting the user
PDFLATEX := pdflatex -halt-on-error

main: abs-den.pdf

.PHONY: main quick watch clean

abs-den-ext.tex: abs-den.tex # this *inlines* the appendix.
	cat abs-den.tex | sed -e 's/^%\\extended/\\extended/g' > abs-den-ext.tex

appendix.pdf: abs-den.pdf
	nix run nixpkgs#pdftk -- abs-den.pdf cat 29-end output appendix.pdf

abs-den-main.pdf: abs-den.pdf
	nix run nixpkgs#pdftk -- abs-den.pdf cat 1-28 output abs-den-main.pdf

supplemental.zip: Interpreter.hs StaticAnalysis.hs Soundness.hs hs/*.hs ../agda/*.agda
	sh -c "cd ..; git archive -o paper/supplemental.zip --prefix=agda/ HEAD:agda"
	nix run nixpkgs#zip -- -j supplemental.zip Interpreter.hs StaticAnalysis.hs Soundness.hs ./hs/{Annotated,Exp,Order,Sergey14}.hs

abs-den.tex: *.lhs *.fmt
	LANG=C.UTF-8 lhs2TeX --poly -o $@ abs-den.lhs

%.hs: %.lhs *.fmt
	LANG=C.UTF-8 lhs2TeX --newcode -o $@ $*.lhs

%.pdf: %.tex macros.tex references.bib
	$(PDFLATEX) -draftmode $*
	bibtex $*
	$(PDFLATEX) -draftmode $*
	$(PDFLATEX) $*

once: abs-den.tex macros.tex
	$(PDFLATEX) abs-den

quick: abs-den.tex macros.tex
	$(PDFLATEX) -draftmode abs-den
	$(PDFLATEX) abs-den

quick-ext: abs-den-ext.tex macros.tex
	$(PDFLATEX) -draftmode abs-den-ext
	$(PDFLATEX) abs-den-ext

test: [A-Z]*.lhs
	LANG=C.UTF-8 ghc -ihs -pgmL lhs2TeX -optL--pre -fno-code -freverse-errors -W $?

watch:
	ls *.lhs *.tex | entr -n make quick

watch-ext:
	ls *.lhs *.tex | entr -n make quick-ext

watch-test:
	ls [A-Z]*.lhs | entr -n make test

submission: abs-den-main.pdf appendix.pdf supplemental.zip
	@grep '^\\documentclass\[acmsmall,review,anonymous\]{acmart}' abs-den.lhs # Test for submission mode

clean:
	git clean -fxd
