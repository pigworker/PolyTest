default : TLCAPoly.pdf

PolyTest.tex : PolyTest.lagda
	lhs2TeX --agda PolyTest.lagda > PolyTest.tex

PolyTest.aux : PolyTest.tex
	latex PolyTest

PolyTest.blg : PolyTest.aux Ornament.bib
	bibtex PolyTest

PolyTest.dvi : PolyTest.tex PolyTest.blg
	latex PolyTest
	latex PolyTest

PolyTest.pdf : PolyTest.dvi
	pdflatex PolyTest

TLCAPoly.tex : TLCAPoly.lagda
	lhs2TeX --agda TLCAPoly.lagda > TLCAPoly.tex

TLCAPoly.aux : TLCAPoly.tex
	pdflatex TLCAPoly

TLCAPoly.blg : TLCAPoly.aux Ornament.bib
	bibtex TLCAPoly

TLCAPoly.pdf : TLCAPoly.tex TLCAPoly.blg
	pdflatex TLCAPoly
