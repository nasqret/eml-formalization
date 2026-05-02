.PHONY: all clean

all: REPORT.pdf

REPORT.pdf: REPORT.tex
	pdflatex -interaction=nonstopmode REPORT.tex
	pdflatex -interaction=nonstopmode REPORT.tex

clean:
	rm -f *.aux *.log *.out *.toc *.bbl *.blg *.fls *.fdb_latexmk *.synctex.gz
