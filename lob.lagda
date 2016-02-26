 \documentclass[preprint]{sigplanconf}

 \usepackage{agda}

 % The following packages are needed because unicode
 % is translated (using the next set of packages) to
 % latex commands. You may need more packages if you
 % use more unicode characters:

 \usepackage{amssymb}
 \usepackage{hyperref}
 % \usepackage{bbm}
 % \usepackage[greek,english]{babel}

 % This handles the translation of unicode to latex:

 \usepackage{ucs}
 \usepackage[utf8x]{inputenc}
 % \usepackage{autofe}

 % Some characters that are not automatically defined
 % (you figure out by the latex compilation errors you get),
 % and you need to define:

 \DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
 \DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
 \DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}

 % Add more as you need them (shouldn’t happen often).

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\conferenceinfo{ICFP '16}{September 19--21, 2016, Nara, Japan}
\copyrightyear{2016}
%\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
%\copyrightdoi{nnnnnnn.nnnnnnn}

% Uncomment the publication rights you want to use.
%\publicationrights{transferred}
\publicationrights{licensed}     % this is the default
%\publicationrights{author-pays}

%\titlebanner{banner above paper title}        % These are ignored unless
%\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{L\"ob's Theorem}
\subtitle{A functional pearl of dependently typed quining}

\authorinfo{Name1}
           {Affiliation1}
           {Email1}
\authorinfo{Name2\and Name3}
           {Affiliation2/3}
           {Email2/3}

\maketitle

 \AgdaHide{
  \begin{code}
 module lob where
  \end{code}
}

\begin{abstract}
This is the text of the abstract.
\end{abstract}

\begin{quotation}
\noindent \textit{If P's answer is `Bad!', Q will suddenly stop. \\
But otherwise, Q will go back to the top, \\
and start off again, looping endlessly back, \\
till the universe dies and turns frozen and black.}
\end{quotation}
\begin{flushright}
Excerpt from \emph{Scooping the Loop Snooper}, by Geoffrey K.~Pullum (\url{http://www.lel.ed.ac.uk/~gpullum/loopsnoop.html}\cite{})
\end{flushright}

\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
\terms
Agda, Lob, quine, self-reference

\keywords
Agda, Lob, quine, self-reference

\section{Introduction}

The text of the paper begins here.


 \begin{code}

 \end{code}

\appendix
\section{Appendix Title}

This is the text of the appendix, if you need one.

\acks

Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}

% The bibliography should be embedded for final submission.

\begin{thebibliography}{}
\softraggedright

\bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
P. Q. Smith, and X. Y. Jones. ...reference text...

\end{thebibliography}


 \end{document}
