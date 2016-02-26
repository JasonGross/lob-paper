V = 0

Q_0 := @
Q_1 :=
Q = $(Q_$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = $(VECHO_$(V))

QECHO_0 := @true
QECHO_1 := @echo
QECHO = $(QECHO_$(V))

.PHONY: agda all latex dependencies clean clean-all update-templates

all: agda latex

#lob.agdai: agda.sty

#agda.sty:
#	wget -N "http://code.haskell.org/Agda/src/data/agda.sty"

update-templates::
	wget -N "http://www.sigplan.org/sites/default/files/sigplanconf.cls"
	wget -N "http://www.sigplan.org/sites/default/files/sigplanconf-template.tex"
	wget -N "http://www.sigplan.org/sites/default/files/sigplanconf-guide.pdf"

lob.agdai : %.agdai : %.lagda
	agda -i . --html $<

latex/lob.tex : latex/%.tex : %.lagda
	agda -i . --latex $<

lob.tex: latex/lob.tex
	cp -f latex/*.tex latex/*.sty ./

lob.pdf : %.pdf : %.tex
	$(Q)pdflatex -synctex=1 $<
	$(Q)bibtex ${<:.tex=.aux}
	$(Q)pdflatex -synctex=1 $<
	$(Q)pdflatex -synctex=1 $<

agda: lob.agdai

latex: lob.pdf

UNIS-LARGE = $(patsubst %,uni-%.def,$(shell seq 0 762))
UNIS = uni-global.def
INS_STY = ifmtarg.sty
DTX_STY =
DTX_INS_STY = filecontents.sty polytable.sty
SIMPLE_TEX = ifmtarg.tex
SIMPLE_DEPENDENCIES = ucs.sty xifthen.sty etoolbox.sty lazylist.sty
PRE_DEPENDENCIES = $(INS_STY:.sty=.ins) $(DTX_STY:.sty=.dtx)
DEPENDENCIES = $(DTX_INS_STY) $(INS_STY) $(DTX_STY) $(SIMPLE_DEPENDENCIES) $(SIMPLE_TEX) utf8x.def ucsencs.def $(UNIS) ifmtarg.sty

utf8x.def ucsencs.def:
	wget -N "http://mirrors.ctan.org/macros/latex/contrib/ucs/$@"

$(UNIS):
	wget -N "http://mirrors.ctan.org/macros/latex/contrib/ucs/data/$@"

ifmtarg.sty: ifmtarg.tex filecontents.sty

$(SIMPLE_TEX):
	wget -N "http://mirrors.ctan.org/macros/latex/contrib/$(@:.tex=)/$@"

$(INS_STY:.sty=.ins) $(DTX_INS_STY:.sty=.ins):
	wget -N "http://mirrors.ctan.org/macros/latex/contrib/$(@:.ins=)/$@"

$(INS_STY) : %.sty : %.ins
	latex $<

$(DTX_INS_STY) : %.sty : %.dtx

$(DTX_INS_STY) : %.sty : %.ins
	latex $<

$(DTX_STY:.sty=.dtx) $(DTX_INS_STY:.sty=.dtx):
	wget -N "http://mirrors.ctan.org/macros/latex/contrib/$(@:.dtx=)/$@"

$(DTX_STY) : %.sty : %.dtx
	tex $<

$(SIMPLE_DEPENDENCIES):
	wget -N "http://mirrors.ctan.org/macros/latex/contrib/$(@:.sty=)/$@"

dependencies:: $(DEPENDENCIES)

clean::
	$(VECHO) "RM *.AGDAI *.PDF *.LOG *.AUX *.SYNCTEX.GZ *.BBL *.BLG"
	$(Q)rm -f *.agdai *.pdf *.log *.aux *.synctex.gz *.bbl *.blg
	rm -rf html
	rm -rf latex
	rm -f agda.sty lob.tex

clean-all:: clean
	rm -f $(DEPENDENCIES) $(PRE_DEPENDENCIES)
