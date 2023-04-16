PAPERNAME = paper

CODE := $(shell find src -type f -name *.hs)
LHS := $(addprefix out/, $(CODE:.hs=.lhs))
OBJS := $(LHS:.lhs=.tex)
PAPER := $(wildcard paper/*.tex)

.PHONY: all clean out

all: out/${PAPERNAME}.pdf

out/${PAPERNAME}.pdf: out/${PAPERNAME}.tex
	TEXINPUTS=./out:${TEXINPUTS} latexmk -pdf -pdflatex="pdflatex --shell-escape" -jobname=out/${PAPERNAME} -bibtex $<

out/${PAPERNAME}.tex: paper/Main.tex $(PAPER) $(OBJS) | out
	cd paper && lhs2TeX -o ../out/paper.tex Main.tex

out/src/%.tex: out/src/%.lhs | $(LHS)
	lhs2TeX -o $@ $<

out/src/%.lhs: src/%.hs | out
	@mkdir -p $(@D)
	./hs-to-lhs.sh $<

.SECONDARY:

out:
	@mkdir -p out
	@mkdir -p out/src

clean:
	rm -rf out
