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

WGET ?= wget
OTHERFLAGS ?=

all: agda latex

#lob.agdai: agda.sty

#agda.sty:
#	$(WGET) -N "http://code.haskell.org/Agda/src/data/agda.sty"

update-templates::
	$(WGET) -N "http://www.sigplan.org/sites/default/files/sigplanconf.cls"
	$(WGET) -N "http://www.sigplan.org/sites/default/files/sigplanconf-template.tex"
	$(WGET) -N "http://www.sigplan.org/sites/default/files/sigplanconf-guide.pdf"

lob-appendix.agdai lob.agdai : %.agdai : %.lagda
	agda -i . --html $<

latex/lob-appendix.tex latex/lob.tex : latex/%.tex : %.lagda
	agda -i . --latex $<

lob.tex: latex/lob.tex latex/lob-appendix.tex
	cp -f latex/*.tex latex/*.sty ./

lob.pdf : %.pdf : %.tex
	$(Q)pdflatex -synctex=1 $(OTHERFLAGS) $<
#	$(Q)bibtex ${<:.tex=.aux}
	$(Q)pdflatex -synctex=1 $(OTHERFLAGS) $<
	$(Q)pdflatex -synctex=1 $(OTHERFLAGS) $<

agda: lob.agdai lob-appendix.agdai

latex: lob.pdf

UNIS-LARGE = $(patsubst %,uni-%.def,$(shell seq 0 762))
UNIS = uni-global.def
INS_STY = ifmtarg.sty
DTX_STY =
DTX_INS_STY = filecontents.sty polytable.sty xcolor.sty
SIMPLE_TEX = ifmtarg.tex
SIMPLE_DEPENDENCIES = ucs.sty xifthen.sty etoolbox.sty lazylist.sty
ZIPS = tipa.zip
PRE_DEPENDENCIES = $(INS_STY:.sty=.ins) $(DTX_STY:.sty=.dtx) $(ZIPS) tipa/ boxchar.sty codelist.sty exaccent.sty extraipa.sty tipaman.sty tipaman.tex tipaman0.tex tipaman1.tex tipaman2.tex tipaman3.tex tipaman4.tex tipx.sty tone.sty vowel.sty vowel.tex
DEPENDENCIES = $(DTX_INS_STY) $(INS_STY) $(DTX_STY) $(SIMPLE_DEPENDENCIES) $(SIMPLE_TEX) utf8x.def ucsencs.def $(UNIS) ifmtarg.sty uni-34.def uni-33.def uni-3.def uni-32.def uni-37.def uni-35.def uni-0.def uni-32.def tipa.sty

tipa.sty: tipa.zip
	unzip $< && (find $(<:.zip=) -name "*.sty" -o -name "*.tex" -o -name "*.map" -o -name "*.afm" -o -name "*.enc" -o -name "*.mf" -o -name "*.pfm" -o -name "*.pro" -o -name "*.tfm" -o -name "*.pfb" -o -name "*.fd" -o -name "*.def" | xargs mv -t ./)

tipa.zip:
	$(WGET) -N "http://mirrors.ctan.org/fonts/$(@:.zip=)/$@"

utf8x.def ucsencs.def:
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/ucs/$@"

$(UNIS) $(UNIS-LARGE):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/ucs/data/$@"

ifmtarg.sty: ifmtarg.tex filecontents.sty

$(SIMPLE_TEX):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/$(@:.tex=)/$@"

$(INS_STY:.sty=.ins) $(DTX_INS_STY:.sty=.ins):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/$(@:.ins=)/$@"

$(INS_STY) : %.sty : %.ins
	latex $<

$(DTX_INS_STY) : %.sty : %.dtx

$(DTX_INS_STY) : %.sty : %.ins
	latex $<

$(DTX_STY:.sty=.dtx) $(DTX_INS_STY:.sty=.dtx):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/$(@:.dtx=)/$@"

$(DTX_STY) : %.sty : %.dtx
	tex $<

$(SIMPLE_DEPENDENCIES):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/$(@:.sty=)/$@"

dependencies:: $(DEPENDENCIES)

clean::
	$(VECHO) "RM *.AGDAI *.PDF *.LOG *.AUX *.SYNCTEX.GZ *.BBL *.BLG"
	$(Q)rm -f *.agdai *.pdf *.log *.aux *.synctex.gz *.bbl *.blg
	rm -rf html
	rm -rf latex
	rm -f agda.sty lob.tex

clean-all:: clean
	$(VECHO) "RM *.PFM *.MF *.TFM *.PFB *.MAP *.DEF *.FD *.PRO *.LOX"
	$(Q)rm -f *.pfm *.mf *.tfm *.pfb *.map *.def *.fd *.pro *.lox
	rm -rf $(DEPENDENCIES) $(PRE_DEPENDENCIES)
