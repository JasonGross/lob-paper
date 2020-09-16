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

.PHONY: agda all latex dependencies clean clean-all update-templates supplemental check-no-stage dist-check supplemental-check dist-check-supplemental-nonymous dist-check-supplemental-anonymous dist-check-supplemental-nonymous-make dist-check-supplemental-anonymous-make dist-check-make update-icfp make-and-update-icfp spellcheck

WGET ?= wget
OTHERFLAGS ?=

all: agda latex

#lob.agdai: agda.sty

#agda.sty:
#	$(WGET) -N "http://code.haskell.org/Agda/src/data/agda.sty"

AGDA = lob-build-quine lob common prisoners-dilemma-lob fair-bot-self-cooperates

update-templates::
	$(WGET) -N "http://www.sigplan.org/sites/default/files/sigplanconf.cls"
	$(WGET) -N "http://www.sigplan.org/sites/default/files/sigplanconf-template.tex"
	$(WGET) -N "http://www.sigplan.org/sites/default/files/sigplanconf-guide.pdf"

$(AGDA:=.agdai) : %.agdai : %.lagda
	agda -i . --html $<

$(patsubst %,latex/%.tex,$(AGDA)) : latex/%.tex : %.lagda
	agda -i . --latex $<

lob.tex: $(patsubst %,latex/%.tex,$(AGDA))
	cp -f latex/*.tex latex/*.sty ./

lob.pdf lob-preprint.pdf: lob.tex fair-bot-self-cooperates.tex $(wildcard lob.bib authorinfo.tex header.tex acknowledgments.tex)

lob.pdf lob-preprint.pdf : %.pdf : %.tex
	$(Q)pdflatex -enable-write18 -synctex=1 $(OTHERFLAGS) $<
	$(Q)bibtex ${<:.tex=.aux}
	$(Q)pdflatex -enable-write18 -synctex=1 -interaction=nonstopmode $(OTHERFLAGS) $< 2>/dev/null >/dev/null
	$(Q)pdflatex -enable-write18 -synctex=1 $(OTHERFLAGS) $<

agda: $(AGDA:=.agdai)

latex: lob.pdf lob-preprint.pdf

check-no-stage::
	@git diff --cached --exit-code || ( \
	echo "ERROR: Staged but uncommitted changes"; \
	git diff --cached; \
	exit 1; \
	)

supplemental:: check-no-stage
	cp .gitattributes.anonymous .gitattributes && git add .gitattributes && git commit -m "TEMP COMMIT FOR supplemental TARGET"
	git archive --format zip -o supplemental-anonymous.zip HEAD
	git reset HEAD^ && cp .gitattributes.nonymous .gitattributes && git add .gitattributes
	git archive --format zip -o supplemental-nonymous.zip HEAD

supplemental-test: supplemental

update-icfp::
	"/cygdrive/d/Program Files/AutoHotkey/AutoHotkey.exe" update-icfp-submission.ahk

make-and-update-icfp:: lob.pdf lob-preprint.pdf supplemental
	$(MAKE) update-icfp

dist-check:: dist-check-supplemental-nonymous dist-check-supplemental-anonymous

dist-check-make:: dist-check-supplemental-nonymous-make dist-check-supplemental-anonymous-make

dist-check-supplemental-anonymous:: supplemental-test latex
	rm -rf supplemental-anonymous
	unzip supplemental-anonymous.zip -d supplemental-anonymous
	$(MAKE) dist-check-supplemental-anonymous-make

dist-check-supplemental-anonymous-make::
	$(MAKE) -C supplemental-anonymous dependencies && $(MAKE) -C supplemental-anonymous

dist-check-supplemental-nonymous:: supplemental-test latex
	rm -rf supplemental-nonymous
	unzip supplemental-nonymous.zip -d supplemental-nonymous
	$(MAKE) dist-check-supplemental-nonymous-make

dist-check-supplemental-nonymous-make::
	$(MAKE) -C supplemental-nonymous dependencies && $(MAKE) -C supplemental-nonymous

spellcheck::
	for i in $(shell git ls-files "*.lagda" "*.tex" "*.md"); do aspell --mode=tex --personal=./lob-dict.txt check $$i; done

UNIS-LARGE = $(patsubst %,uni-%.def,$(shell seq 0 762))
UNIS = uni-global.def
INS_STY = ifmtarg.sty
DTX_STY = accsupp.sty
ALL_DTX_STY = $(DTX_STY)
DTX_LATEX_STY =
ALL_DTX_LATEX_STY = stmaryrd.sty $(DTX_LATEX_STY)
DTX_INS_STY = filecontents.sty polytable.sty xcolor.sty minted.sty ifplatform.sty fvextra.sty
SIMPLE_TEX = ifmtarg.tex
SIMPLE_DEPENDENCIES = ucs.sty xifthen.sty etoolbox.sty lazylist.sty lineno.sty upquote.sty logreq.sty slashbox.sty
SIMPLE_DEFS = logreq.def
GENERIC_STY = xstring.sty
GENERIC_TEX = xstring.tex
SIMPLE_CONTRIB_ZIPS = biblatex.zip cmap.zip mmap.zip
CONTRIB_ZIPS = $(SIMPLE_CONTRIB_ZIPS)
SIMPLE_ZIPS = tipa.zip $(SIMPLE_CONTRIB_ZIPS)
SIMPLE_DTX_ZIPS = stmaryrd.zip
ZIPS = $(SIMPLE_ZIPS) $(SIMPLE_DTX_ZIPS)
IFTEX_STY := ifetex.sty ifluatex.sty ifpdf.sty iftex.sty iftex.tex ifvtex.sty ifxetex.sty
HOBSUB_STY := hobsub-generic.sty hobsub-hyperref.sty hobsub.sty
OBERDIEK_DTX_STY =
PRE_DEPENDENCIES = $(INS_STY:.sty=.ins) $(ALL_DTX_STY:.sty=.dtx) $(ALL_DTX_LATEX_STY:.sty=.dtx) $(ZIPS) $(ZIPS:.zip=/) boxchar.sty codelist.sty exaccent.sty extraipa.sty tipaman.sty tipaman.tex tipaman0.tex tipaman1.tex tipaman2.tex tipaman3.tex tipaman4.tex tipx.sty tone.sty vowel.sty vowel.tex $(OBERDIEK_DTX_STY:.sty=.dtx)
DEPENDENCIES = $(GENERIC_STY) $(GENERIC_TEX) $(DTX_INS_STY) $(INS_STY) $(ALL_DTX_STY) $(ALL_DTX_LATEX_STY) $(SIMPLE_DEPENDENCIES) $(SIMPLE_TEX) $(SIMPLE_DEFS) utf8x.def ucsencs.def $(UNIS) ifmtarg.sty uni-34.def uni-33.def uni-3.def uni-32.def uni-37.def uni-35.def uni-0.def uni-32.def uni-39.def tipa.sty biblatex.sty uni-29.def uni-37.def uni-2.def uni-3.def cmap.sty mmap.sty $(OBERDIEK_DTX_STY) $(IFTEX_STY) $(HOBSUB_STY)

FIND_ARGS = -name "*.sty" -o -name "*.tex" -o -name "*.map" -o -name "*.afm" -o -name "*.enc" -o -name "*.mf" -o -name "*.pfm" -o -name "*.pro" -o -name "*.tfm" -o -name "*.pfb" -o -name "*.fd" -o -name "*.def" -o -name "*.csf" -o -name "*.bst" -o -name "*.cfg" -o -name "*.cbx" -o -name "*.bbx" -o -name "*.lbx" -o -name "*.dtx" -o -name "*.ins" -o -name "*.600pk" -o -name "*.cmap" -o -name "*.drv"

$(SIMPLE_ZIPS:.zip=.sty) : %.sty : %.zip
	unzip $< && (find $(<:.zip=) $(FIND_ARGS) | xargs touch && find $(<:.zip=) $(FIND_ARGS) | xargs mv -t ./)

$(SIMPLE_DTX_ZIPS:.zip=.dtx) : %.dtx : %.zip
	unzip $< && (find $(<:.zip=) $(FIND_ARGS) | xargs touch && find $(<:.zip=) $(FIND_ARGS) | xargs mv -t ./)

$(OBERDIEK_DTX_STY:.sty=.dtx):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/oberdiek/$@"

tipa.zip:
	$(WGET) -N "http://mirrors.ctan.org/fonts/$(@:.zip=)/$@"

stmaryrd.zip:
	$(WGET) -N "http://mirrors.ctan.org/fonts/$@"

$(CONTRIB_ZIPS):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/$@"

utf8x.def ucsencs.def:
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/ucs/$@"

$(GENERIC_STY):
	$(WGET) -N "http://mirrors.ctan.org/macros/generic/$(@:.sty=)/$@"

$(GENERIC_TEX):
	$(WGET) -N "http://mirrors.ctan.org/macros/generic/$(@:.tex=)/$@"

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

$(ALL_DTX_STY) $(OBERDIEK_DTX_STY) : %.sty : %.dtx
	tex $<

$(ALL_DTX_LATEX_STY) : %.sty : %.dtx
	latex $<

$(IFTEX_STY):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/iftex/$@"

$(HOBSUB_STY):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/hobsub/$@"

$(SIMPLE_DEPENDENCIES):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/$(@:.sty=)/$@"

$(SIMPLE_DEFS):
	$(WGET) -N "http://mirrors.ctan.org/macros/latex/contrib/$(@:.def=)/$@"

dependencies:: $(DEPENDENCIES)

clean::
	$(VECHO) "RM *.AGDAI *.PDF *.LOG *.AUX *.SYNCTEX.GZ *.BBL *.BLG"
	$(Q)rm -f *.agdai *.pdf *.log *.aux *.synctex.gz *.bbl *.blg
	rm -rf html
	rm -rf latex
	rm -f agda.sty lob.tex

clean-all:: clean
	$(VECHO) "RM *.PFM *.MF *.TFM *.PFB *.MAP *.DEF *.FD *.PRO *.LOX *.CSF *.BST *.CFG *.CBX *.BBX *.LBX *.600PK *.CMAP *.DRV"
	$(Q)rm -f *.pfm *.mf *.tfm *.pfb *.map *.def *.fd *.pro *.lox *.csf *.bst *.cfg *.cbx *.bbx *.lbx *.600pk *.cmap *.drv
	rm -rf $(DEPENDENCIES) $(PRE_DEPENDENCIES)
