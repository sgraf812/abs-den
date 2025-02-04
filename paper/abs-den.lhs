% -*- mode: LaTeX -*-

%% For double-blind review submission, w/o CCS and ACM Reference (max submission space)
%\documentclass[acmsmall,review,anonymous,natbib=false]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For double-blind review submission, w/ CCS and ACM Reference
%\documentclass[acmsmall,review,anonymous]{acmart}\settopmatter{printfolios=true}
%% For single-blind review submission, w/o CCS and ACM Reference (max submission space)
%\documentclass[acmsmall,review,anonymous]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%% For single-blind review submission, w/ CCS and ACM Reference
%\documentclass[acmsmall,review]{acmart}\settopmatter{printfolios=true}
%% For final camera-ready submission, w/ required CCS and ACM Reference
%\documentclass[acmsmall,screen]{acmart}\settopmatter{}

% https://github.com/borisveytsman/acmart/issues/406#issuecomment-667180341
\PassOptionsToPackage{prologue,dvipsnames}{xcolor}

%\documentclass[acmsmall,review]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
\documentclass[acmsmall,review,anonymous]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}

%% Journal information
%%
\setcopyright{rightsretained}
\acmDOI{10.1145/1111111}
\acmYear{2025}
\copyrightyear{2025}
%\acmSubmissionID{popl24main-p11-p}
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

\usepackage[appendix=append,bibliography=common,forwardlinking=yes]{apxproof}
%\renewcommand{\appendixprelim}{\clearpage\onecolumn\appendix\section*{Start of Appendix}} % Clearly mark the begin of the Appendix inserted by apxproof
\renewcommand{\appendixsectionformat}[2]{Appendix for Section~#1\ (#2)}

%\usepackage{array} % \newcolumntype
\usepackage{enumitem} % label=(\alph*)
\usepackage{ifdraft}
\usepackage[nameinlink]{cleveref}
\usepackage{xspace}
\usepackage{url}
\usepackage{varwidth}
\usepackage{galois}
%\usepackage{hsyl-listing} % listing style, hsyl-style
%\usepackage{scalerel}
%\usepackage[all]{xy}
\usepackage{relsize} % relscale
\usepackage{xfp} % fpeval
%\usepackage{stackengine}
\usepackage{mathtools} % xhookrightarrow
\usepackage{trimclip} % clipbox
\usepackage{mathpartir} % inference rules
\usepackage{subcaption}
\usepackage{witharrows}
\usepackage{mathbbol} % \bbcolon and \bbquestionmark
%\usepackage{stmaryrd} % \lightning
%\usepackage{tikz}
%\usetikzlibrary{cd} % commutative diagrams
%\usetikzlibrary{calc}
%\usetikzlibrary{fit}
%\usetikzlibrary{patterns}
%\usetikzlibrary{matrix}
%\usetikzlibrary{decorations.pathreplacing}
%\usetikzlibrary{decorations.pathmorphing}
%\usetikzlibrary{profiler}
%\usepackage{placeins} % flush floats with \FloatBarrier
\usepackage[T1]{fontenc} % https://tex.stackexchange.com/a/181119

\usepackage{utf8-symbols}
\input{macros}
\settoggle{hidetodos}{true}

%\usepackage[mark]{gitinfo2}

%include custom.fmt
\newcommand{\kwcolor}[1]{{\color{BlueViolet} #1}}
\newcommand{\varcolor}[1]{{\color{Sepia} #1}}
\newcommand{\concolor}[1]{{\color{OliveGreen} #1}}
\newcommand{\keyword}[1]{\kwcolor{\mathbf{#1}}}
\newcommand{\varid}[1]{\varcolor{\mathit{#1}}}
\newcommand{\conid}[1]{\concolor{\mathsf{#1}}}
%\newcommand{\tick}{\text{\textquoteright}}
\newcommand{\package}[1]{\textsf{#1}}
\renewcommand{\commentbegin}{\ensuremath{\;\Lbag\ }}
\renewcommand{\commentend}{\ensuremath{\Rbag\;}}

%\pgfprofilenewforenvironment{hscode}

% Tables should have the caption above
\floatstyle{plaintop}
\restylefloat{table}

\begin{document}

%\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\title{Abstracting Denotational Interpreters}
\subtitle{A Design Pattern for Sound, Compositional and Higher-order Static Program Analysis}

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

\author{Sven Keidel}
\affiliation{%
  \institution{TU Darmstadt}
  \city{Darmstadt}
  \country{Germany}
}
\email{sven.keidel@@tu-darmstadt.de}

\begin{abstract}
  We explore \emph{denotational interpreters}:
  denotational semantics that produce coinductive traces of a corresponding
  abstract machine.
  By parameterising our denotational interpreter over the semantic domain
  and then varying it, we recover \emph{dynamic semantics} with different
  evaluation strategies as well as \emph{summary-based static analyses} such as type
  analysis, all from the same generic interpreter.
  Among our contributions is the first denotational semantics for call-by-need
  that is provably bisimilar to the corresponding abstract machine.
  The generated traces lend themselves well to describe \emph{operational properties}
  such as how often a variable is evaluated, and hence enable static analyses
  abstracting these operational properties.
  Since static analysis and dynamic semantics share the same generic interpreter
  definition, soundness proofs via abstract interpretation decompose into
  (1) showing small abstraction laws about the abstract domain and
  (2) establishing a logical relation that can be shared per semantics, where
  (1) is considerably simpler than (2).
\end{abstract}

%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
   <concept>
       <concept_id>10011007.10011006.10011039.10011311</concept_id>
       <concept_desc>Software and its engineering~Semantics</concept_desc>
       <concept_significance>500</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10010940.10010992.10010998.10011000</concept_id>
       <concept_desc>Software and its engineering~Automated static analysis</concept_desc>
       <concept_significance>500</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011041</concept_id>
       <concept_desc>Software and its engineering~Compilers</concept_desc>
       <concept_significance>300</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011008.10011024.10011035</concept_id>
       <concept_desc>Software and its engineering~Procedures, functions and subroutines</concept_desc>
       <concept_significance>300</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011008.10011009.10011012</concept_id>
       <concept_desc>Software and its engineering~Functional languages</concept_desc>
       <concept_significance>100</concept_significance>
       </concept>
   <concept>
       <concept_id>10011007.10011006.10011073</concept_id>
       <concept_desc>Software and its engineering~Software maintenance tools</concept_desc>
       <concept_significance>100</concept_significance>
       </concept>
 </ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~Semantics}
\ccsdesc[500]{Software and its engineering~Automated static analysis}
\ccsdesc[300]{Software and its engineering~Compilers}
\ccsdesc[300]{Software and its engineering~Procedures, functions and subroutines}
\ccsdesc[100]{Software and its engineering~Functional languages}
\ccsdesc[100]{Software and its engineering~Software maintenance tools}
%% End of generated code

%% Keywords
%% comma separated list
\keywords{Programming language semantics, Abstract Interpretation, Static Program Analysis}  %% \keywords are mandatory in final camera-ready submission

\maketitle

%include Introduction.lhs
%include Problem.lhs
%include OpSem.lhs
%include Interpreter.lhs
%include Adequacy.lhs
%include StaticAnalysis.lhs
%include Soundness.lhs
%include RelatedWork.lhs

%\begin{acks}
%We would like to thank the anonymous POPL reviewers for their feedback.
%, as well as Jonathan Brachthäuser, Joachim Breitner, András Kovács, Bohdan
%Liesnikov, Anthony Travers and Sebastian Ullrich.
%\end{acks}

\clearpage
\bibliography{references}

\end{document}
