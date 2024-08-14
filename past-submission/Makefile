default:
	pdflatex -shell-escape main-concur2024.tex

bib:
	bibtex main-concur2024

final:
	pdflatex -shell-escape main-concur2024.tex
	bibtex main-concur2024
	pdflatex -shell-escape main-concur2024.tex
	pdflatex -shell-escape main-concur2024.tex


add:
	git add Makefile *tex *sty main.bib

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *~ *bak
