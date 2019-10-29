%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Recommended by the ACM ppl
\usepackage{booktabs}
\usepackage{subfigure}
\usepackage{wrapfig}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Our packages
\usepackage{amsmath}
\usepackage{xcolor}
\usepackage{booktabs}
\usepackage{qtree}

\usepackage{graphicx}
\usepackage{tikz}
\usepackage{pgfplots}
\usetikzlibrary{positioning}
\usetikzlibrary{calc}
\usetikzlibrary{plotmarks}

%% Cleveref must be the last loaded package
%% since it modifies the cross-ref system.
\usepackage{cleveref}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Our defs

%% More space between rows
\newcommand{\ra}[1]{\renewcommand{\arraystretch}{#1}}

%% Logistic Stuff

\definecolor{C1}{RGB}{0,153,204}
\definecolor{C2}{RGB}{89,0,179}

\newcounter{commentctr}[section]
\setcounter{commentctr}{0}
\renewcommand{\thecommentctr}{%
\arabic{section}.\arabic{commentctr}}

\newcommand{\warnme}[1]{%
{\color{red} \textbf{$[$} #1 \textbf{$]$}}}

\newcommand{\TODO}[1]{%
 {\color{purple} \textbf{$[$ TODO: } #1 \textbf{$]$}}
}

\newcommand{\tmp}[1]{%
{\color{gray} \textit{#1} }}

\newenvironment{temp}{\bgroup \color{gray} \textit}{\egroup}

\newcommand{\victor}[2][nolabel]{%
 {\color{C2} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Victor: } #2 \textbf{$]$}}%
}
\newcommand{\msm}[2][nolabel]{%
 {\color{C2} \refstepcounter{commentctr}\label{#1} \textbf{$[$ (\thecommentctr) Mark: } #2 \textbf{$]$}}%
}

%% LaTeX stuff

\newenvironment{myhs}{\vspace{0.10cm}\par\noindent\begin{minipage}{\textwidth}\small}{\end{minipage}\vspace{0.10cm}}

\def\dotminus{\mathbin{\ooalign{\hss\raise1ex\hbox{.}\hss\cr
  \mathsurround=0pt$-$}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% lhs2TeX Formatting Rules
%%
%% Comment out to use lhs2TeX default formatting.
%%
%include stylish.lhs
%%

% Easy to typeset Haskell types using the 
% commands from stylish.lhs (if it's defined!)
\newcommand{\HT}[1]{\ifdefined\HSCon\HSCon{#1}\else#1\fi}
\newcommand{\HS}[1]{\ifdefined\HSSym\HSSym{#1}\else#1\fi}
\newcommand{\HV}[1]{\ifdefined\HSVar\HSVar{#1}\else#1\fi}

%% Here's a number of handy commands for adding dashes to words
%% The proper construction was sugested by Guy Steele, thanks Guy!
\newcommand{\textdash}{-{\hskip-0.3em}-}
\newcommand{\wdw}[2]{\hbox{\it #1\textdash{}#2}}
\newcommand{\wdwdw}[3]{\hbox{\it #1\textdash{}#2\textdash{}#3}}
\newcommand{\wdwdwdw}[4]{\hbox{\it #1\textdash{}#2\textdash{}#3\textdash{}#4}}

%%% Datatype Promotion
%format (P (a)) = "\HS{''}" a
%% Special case for promoting (:)
%format PCons   = "\HS{''\!\!:}"

%%% Usefull Notation
%format dots    = "\HS{\dots}"
%format forall  = "\HS{\forall}"
%format lambda  = "\HS{\lambda}"
%format dot     = "\HS{.}"
%format ^=      = "\HS{\bumpeq}"
