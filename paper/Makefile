default:
	pdflatex -shell-escape main-ppdp2025.tex

bib:
	bibtex main-ppdp2025

final:
	pdflatex -shell-escape main-ppdp2025.tex
	bibtex main-ppdp2025
	pdflatex -shell-escape main-ppdp2025.tex
	pdflatex -shell-escape main-ppdp2025.tex


add:
	git add Makefile *tex *sty main.bib

clean:
	rm -rf *.aux *.bbl *.blg *.log *.out *~ *bak *vtc *nix *lock _minted*
