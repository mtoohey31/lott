-include main.d
main.pdf: main.tex
	latexmk -f -pdf -file-line-error -interaction=nonstopmode -deps-out=main.d $<

clean:
	latexmk -c
	rm -f main.d main.pdf
