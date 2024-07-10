# -halt-on-error: Halts on first error, rather than prompting the user
PDFLATEX := pdflatex -halt-on-error

main: abs-den.pdf

.PHONY: main quick watch clean

supplement.zip: Interpreter.hs StaticAnalysis.hs Soundness.hs hs/*.hs ../agda/*.agda
	sh -c "cd ..; git archive -o paper/supplement.zip --prefix=agda/ HEAD:agda"
	nix run nixpkgs#zip -- -j supplement.zip Interpreter.hs StaticAnalysis.hs Soundness.hs ./hs/{Exp,Order}.hs

abs-den.tex: *.lhs *.fmt
	LANG=C.UTF-8 lhs2TeX --poly -o $@ abs-den.lhs

%.hs: %.lhs *.fmt
	LANG=C.UTF-8 lhs2TeX --newcode -o $@ $*.lhs

%.pdf: %.tex macros.tex references.bib
	$(PDFLATEX) -draftmode $*
	bibtex $*
	$(PDFLATEX) -draftmode $*
	$(PDFLATEX) $*

diagnostic: abs-den.tex macros.tex
	$(PDFLATEX) -draftmode abs-den | texlogfilter --no-box

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

submission: abs-den.pdf supplement.zip
	grep '^\\usepackage\[appendix=append,bibliography=common\]{apxproof}' abs-den.lhs # Test for correct apxproof settings
	grep '^\\documentclass\[acmsmall,review,anonymous\]{acmart}' abs-den.lhs # Test for submission mode

abs-den-appendix.pdf: abs-den.pdf
	nix run nixpkgs#pdftk -- abs-den.pdf cat 30-end output abs-den-appendix.pdf

abs-den-main.pdf: abs-den.pdf
	nix run nixpkgs#pdftk -- abs-den.pdf cat 1-29 output abs-den-main.pdf

popl-submission: abs-den-main.pdf abs-den-appendix.pdf supplement.zip
	grep '^\\usepackage\[appendix=append,bibliography=common,forwardlinking=no\]{apxproof}' abs-den.lhs # Test for correct apxproof settings
	grep '^\\documentclass\[acmsmall,review,anonymous\]{acmart}' abs-den.lhs # Test for submission mode

# For submission to arXiv
arxiv.zip: abs-den.tex macros.tex utf8-symbols.sty references.bib
	@rm -rf arxiv.zip
	@mkdir -p arxiv/
	@# We need to convince arxiv to use pdflatex
	echo "\pdfoutput=1" | cat - $< > arxiv/$<
	bibtex abs-den
	cp abs-den.bbl arxiv/
	cp macros.tex arxiv/
	cp utf8-symbols.sty arxiv/
	@# Also arxiv uses hypertex, which doesn't really work for us because we are using cleveref
	echo "nohypertex" > arxiv/00README.XXX
	cd arxiv && zip -r ../arxiv.zip .; cd ..
	@rm -rf arxiv

clean:
	git clean -fxd
