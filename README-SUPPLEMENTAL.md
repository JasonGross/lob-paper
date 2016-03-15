# Lӧb's Theorem: A functional pearl of dependently typed quining

The source code for the main paper is in [`lob.lagda`](lob.lagda),
which imports [`common.lagda`](common.lagda) (basic definitions,
included in the appendix) and
[`prisoners-dilemma-lob.lagda`](prisoners-dilemma-lob.lagda) (the
encoding used for the prisoner's dilemma section, also included in the
appendix).  The supplemental code for the section on removing the
quine constructor, which is the bulk of the code not included in the
paper itself, is in [`lob-build-quine.lagda`](lob-build-quine.lagda),
which imports [`lob.lagda`](lob.lagda).  The default Makefile target
builds all Agda, HTML, and PDF files.

This code is known to build with Agda version 2.4.2.5.  The pdf is
known to build with the addition of pdfTeX version
3.1415926-2.5-1.40.14 (TeX Live 2013/Debian) and Pygments version
2.1.1.  The target `make dependencies` should fetch all `.sty` files
not included in the standard TeX Live distribution which are required
to build the pdf.
