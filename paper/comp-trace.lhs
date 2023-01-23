% -*- mode: LaTeX -*-
%% For double-blind review submission, w/o CCS and ACM Reference (max submission space)
%\documentclass[acmsmall,review,anonymous,natbib=false]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For double-blind review submission, w/ CCS and ACM Reference
%\documentclass[acmsmall,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission, w/o CCS and ACM Reference (max submission space)
\documentclass[acmsmall,review]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For single-blind review submission, w/ CCS and ACM Reference
%\documentclass[acmsmall,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission, w/ required CCS and ACM Reference
%\documentclass[acmsmall,screen]{acmart}\settopmatter{}

%\documentclass[acmsmall,review,anonymous]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}

\let\Bbbk\undefined % https://github.com/kosmikus/lhs2tex/issues/82
%include custom.fmt

%% Journal information
%%
\setcopyright{rightsretained}
\acmPrice{}
\acmDOI{10.1145/1111111}
\acmYear{2024}
\copyrightyear{2024}
\acmSubmissionID{popl24main-p11-p}
\acmJournal{PACMPL}
\acmVolume{1}
\acmNumber{POPL}
\acmArticle{1}
\acmMonth{1}

%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
%% Citation style
%% Note: author/year citations are required for papers published as an
%% issue of PACMPL.
\citestyle{acmauthoryear}   %% For author/year citations

%%%%%%%
%\usepackage{multirow}
%\usepackage{footmisc}
%\usepackage{enumitem}
%\usepackage{stmaryrd}
%\usepackage{mathrsfs}
\usepackage{amsmath,latexsym,amssymb,amsthm}
\usepackage{upgreek}
\usepackage{color}
\usepackage{url}
\usepackage{galois}
%\usepackage{scalerel}
%\usepackage[svgnames]{xcolor}
%\usepackage[all]{xy}
%\usepackage{graphicx}
%\usepackage{stackengine}
\usepackage{cleveref}
\usepackage{xspace}
\usepackage{mathpartir}
\usepackage{tikz}
\usepackage{mathbbol}
%\usepackage{eucal}
%\usepackage{wasysym} % \currency
%\usetikzlibrary{cd} % commutative diagrams
%\usetikzlibrary{decorations.pathmorphing}
%\usepackage{bibentry} % \nobibliography below
\usepackage[T1]{fontenc} % https://tex.stackexchange.com/a/181119

\usepackage{utf8-symbols}
\input{macros}

% Tables should have the caption above
\floatstyle{plaintop}
\restylefloat{table}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\title{A Compositional Trace Semantics for Lambda Calculus}
\subtitle{}

\author{Sebastian Graf}
\affiliation{%
  \institution{Karlsruhe Institute of Technology}
  \city{Karlsruhe}
  \country{Germany}
}
\email{sgraf1337@@gmail.com}

\author{Simon Peyton Jones}
\affiliation{%
  \institution{Epic Games}
  \city{Cambridge}
  \country{UK}
}
\email{simon.peytonjones@@gmail.com}

% Some conditional build stuff for handling the Appendix

\newif\ifmain
\newif\ifappendix

% Builds only the main paper by default.
\maintrue
\appendixfalse
% But we provide a switch to build the Appendix only.
\def\appendixonly{\mainfalse{}\appendixtrue{}}

% .. so that you can comment out the following line to build the Appendix only
% This is done by the `make appendix` target.
%\appendixonly

% Same thing for an extended version that includes the Appendix
\def\extended{\maintrue{}\appendixtrue{}}
%\extended

\ifmain

\begin{abstract}
\end{abstract}

%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
   <concept>
       <concept_id>10011007.10011006.10011041</concept_id>
       <concept_desc>Software and its engineering~Compilers</concept_desc>
       <concept_significance>500</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011073</concept_id>
       <concept_desc>Software and its engineering~Software maintenance tools</concept_desc>
       <concept_significance>300</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011008.10011024.10011035</concept_id>
       <concept_desc>Software and its engineering~Procedures, functions and subroutines</concept_desc>
       <concept_significance>100</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011008.10011024.10011032</concept_id>
       <concept_desc>Software and its engineering~Constraints</concept_desc>
       <concept_significance>300</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011008.10011009.10011012</concept_id>
       <concept_desc>Software and its engineering~Functional languages</concept_desc>
       <concept_significance>300</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011008.10011009.10011021</concept_id>
       <concept_desc>Software and its engineering~Multiparadigm languages</concept_desc>
       <concept_significance>300</concept_significance>
       </concept>
 </ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~Compilers}
\ccsdesc[300]{Software and its engineering~Software maintenance tools}
\ccsdesc[100]{Software and its engineering~Procedures, functions and subroutines}
\ccsdesc[300]{Software and its engineering~Constraints}
\ccsdesc[300]{Software and its engineering~Functional languages}
\ccsdesc[300]{Software and its engineering~Multiparadigm languages}
%% End of generated code

%% Keywords
%% comma separated list
\keywords{Programming language semantics}  %% \keywords are mandatory in final camera-ready submission

\maketitle

%include semantics.lhs

\nocite{*}

\clearpage
\bibliography{references}

\fi % \ifmain

% Appendix
\ifappendix
\appendix
\section{Appendix}\label{sec:appendix}
\input{appendix}
\fi % \ifappendix

\end{document}
