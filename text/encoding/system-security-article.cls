\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{system-security-article}[2026/01/10 System Security Article Template]

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{extarticle}}
\ProcessOptions\relax
\LoadClass[a4paper,11pt]{extarticle}

\RequirePackage{fontspec}
\RequirePackage{polyglossia}
\setdefaultlanguage{english}
\setotherlanguage{ukrainian}

\setmainfont{LinLibertine_R.otf}[
    BoldFont=LinLibertine_RB.otf,
    ItalicFont=LinLibertine_RI.otf,
    BoldItalicFont=LinLibertine_RBI.otf,
    Ligatures=TeX,
    Scale=1.0
]
\setsansfont{LinBiolinum_R.otf}[
    BoldFont=LinBiolinum_RB.otf,
    ItalicFont=LinBiolinum_RI.otf,
    BoldItalicFont=LinBiolinum_RBO.otf
]
\setmonofont{DejaVuSansMono.ttf}[
    BoldFont=DejaVuSansMono-Bold.ttf,
    ItalicFont=DejaVuSansMono-Oblique.ttf,
    BoldItalicFont=DejaVuSansMono-BoldOblique.ttf,
    Scale=0.9
]

\RequirePackage{amsmath,amssymb,amsthm}
\RequirePackage{unicode-math}
\RequirePackage{mathtools}
\RequirePackage{extarrows}

\RequirePackage[
    a4paper,
    top=20mm,
    bottom=20mm,
    left=20mm,
    right=20mm,
    includehead,
    headheight=14pt,
    headsep=8mm
]{geometry}

\RequirePackage{indentfirst}
\setlength{\parindent}{1em}
\setlength{\parskip}{0.5em}

\RequirePackage{graphicx}
\RequirePackage{float}
\RequirePackage[dvipsnames,table]{xcolor}
\RequirePackage{tabularx}
\RequirePackage{booktabs}
\RequirePackage[labelfont=bf,labelsep=period]{caption}
\counterwithin{figure}{section}
\counterwithin{table}{section}

\RequirePackage[inline,shortlabels]{enumitem}
\setlist{topsep=3pt,itemsep=2pt,parsep=0pt,partopsep=0pt}

\RequirePackage{hyperref}
\hypersetup{
    colorlinks=true,
    linkcolor=NavyBlue!80!black,
    citecolor=Maroon!80!black,
    urlcolor=RoyalBlue!80!black,
    pdflang=en
}
\RequirePackage[nameinlink,capitalise]{cleveref}

\RequirePackage[
    backend=biber,
    style=ieee,
    sorting=none,
    maxbibnames=99,
    giveninits=true
]{biblatex}

\RequirePackage{fancyhdr}
\pagestyle{fancy}
\fancyhf{}
\renewcommand{\headrulewidth}{0.4pt}
\renewcommand{\footrulewidth}{0pt}
\fancyhead[L]{\nouppercase{\leftmark}}
\fancyhead[R]{\thepage}
\fancypagestyle{plain}{
    \fancyhf{}
    \fancyfoot[C]{\thepage}
    \renewcommand{\headrulewidth}{0pt}
}

\RequirePackage{titlesec}
\titleformat{\section}
    {\normalfont\Large\bfseries}
    {\thesection}{1em}{}
\titlespacing*{\section}{0pt}{18pt}{10pt}

\titleformat{\subsection}
    {\normalfont\large\bfseries}
    {\thesubsection}{1em}{}
\titlespacing*{\subsection}{0pt}{14pt}{8pt}

\titleformat{\subsubsection}
    {\normalfont\normalsize\bfseries}
    {\thesubsubsection}{1em}{}
\titlespacing*{\subsubsection}{0pt}{10pt}{6pt}

\RequirePackage{tikz}
\RequirePackage{tikz-cd}
\usetikzlibrary{positioning,arrows.meta,shapes,calc,backgrounds}

\RequirePackage{listings}
\definecolor{codebg}{RGB}{248,248,248}
\definecolor{codegreen}{rgb}{0,0.5,0}
\definecolor{codegray}{rgb}{0.5,0.5,0.5}
\definecolor{codepurple}{rgb}{0.58,0,0.82}
\lstset{
    backgroundcolor=\color{codebg},
    basicstyle=\ttfamily\small,
    numbers=left,
    numberstyle=\tiny\color{codegray},
    keywordstyle=\bfseries\color{NavyBlue},
    commentstyle=\color{codegreen},
    stringstyle=\color{codepurple},
    breaklines=true,
    frame=single,
    framerule=0.5pt,
    rulecolor=\color{codegray!50},
    captionpos=b,
    tabsize=2,
    showstringspaces=false,
    escapeinside={<@}{@>}
}

\RequirePackage[ruled,linesnumbered]{algorithm2e}
\SetKwInput{KwInput}{Input}
\SetKwInput{KwOutput}{Output}
\SetKwInput{KwReturn}{Return}
\SetKwComment{Comment}{$\triangleright$\ }{}

\RequirePackage[most]{tcolorbox}

\newtheoremstyle{sysecstyle}
    {6pt}
    {6pt}
    {\normalfont}
    {}
    {\bfseries}
    {.}
    {0.5em}
    {}
\theoremstyle{sysecstyle}
\newtheorem{definition}{Definition}[section]
\newtheorem{theorem}[definition]{Theorem}
\newtheorem{lemma}[definition]{Lemma}
\newtheorem{proposition}[definition]{Proposition}
\newtheorem{corollary}[definition]{Corollary}
\newtheorem{example}{Example}[section]
\newtheorem*{remark}{Remark}

\makeatletter
\renewenvironment{proof}[1][\proofname]{
    \par\pushQED{\qed}{\normalfont\bfseries\topsep6\p@\@plus6\p@\relax #1\@addpunct{.} }
}{\popQED\endtrivlist\@endpefalse}
\makeatother

\newcommand{\titlefont}{\normalfont\bfseries\fontsize{20}{24}\selectfont}
\newcommand{\authorfont}{\normalfont\fontsize{12}{14}\selectfont}
\newcommand{\datefont}{\normalfont\itshape\fontsize{11}{13}\selectfont}
\newcommand{\abstractfont}{\linespread{1.1}\fontsize{10}{12}\selectfont}
\newcommand{\keywordsfont}{\itshape\fontsize{10}{12}\selectfont}

\renewenvironment{abstract}{%
    \begin{center}
    \textbf{\abstractname}
    \end{center}
    \begin{quote}\abstractfont
}{%
    \end{quote}
}

\newcommand{\keywords}[1]{%
    \vspace{0.5em}
    \noindent\textbf{Keywords:} {\keywordsfont #1}\par
}

\newcommand{\TODO}[1]{\textcolor{red}{\textbf{[TODO: #1]}}}
\newcommand{\CITE}{\textcolor{red}{\textbf{[CITE]}}}
\newcommand{\remind}[1]{\textcolor{red}{\textbf{#1}}}

\crefname{algocf}{alg.}{algs.}
\Crefname{algocf}{Algorithm}{Algorithms}
\crefname{example}{ex.}{exs.}
\Crefname{example}{Example}{Examples}

\newtcolorbox{infobox}[1][]{
    colback=NavyBlue!5,
    colframe=NavyBlue!50!black,
    fonttitle=\bfseries,
    title=#1,
    boxrule=0.5pt,
    arc=2pt,
    left=6pt, right=6pt, top=4pt, bottom=4pt,
    before skip=10pt, after skip=10pt
}

\newtcolorbox{warnbox}[1][]{
    colback=Orange!8,
    colframe=Orange!70!black,
    fonttitle=\bfseries,
    title=#1,
    boxrule=0.5pt,
    arc=2pt,
    left=6pt, right=6pt, top=4pt, bottom=4pt,
    before skip=10pt, after skip=10pt
}

\newenvironment{secgame}[2]{%
    \begin{tcolorbox}[
        colback=white,
        colframe=black,
        fonttitle=\bfseries,
        title={Game #1: #2},
        boxrule=0.8pt,
        arc=0pt,
        left=8pt, right=8pt, top=4pt, bottom=4pt
    ]
}{%
    \end{tcolorbox}
}

\newenvironment{protocol}[1]{%
    \begin{tcolorbox}[
        colback=Gray!5,
        colframe=Gray!70!black,
        fonttitle=\bfseries,
        title={Protocol: #1},
        boxrule=0.8pt,
        arc=0pt,
        left=8pt, right=8pt, top=4pt, bottom=4pt
    ]
}{%
    \end{tcolorbox}
}
