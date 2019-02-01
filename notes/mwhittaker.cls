\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{mwhittaker}
\LoadClass[12pt]{article}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\RequirePackage[compact]{titlesec}
\RequirePackage[letterpaper,margin=1in]{geometry}
\RequirePackage{fancyhdr}
\RequirePackage{lastpage}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Header and Footer
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Title
\newcommand{\TITLE}{}
\renewcommand{\title}[1]{\renewcommand{\TITLE}{#1}}

% Date
\newcommand{\DATE}{\today}
\renewcommand{\date}[1]{\renewcommand{\DATE}{#1}}

% Author
\newcommand{\AUTHOR}{ }
\renewcommand{\author}[1]{\renewcommand{\AUTHOR}{#1}}

% Format header and Footer
\renewcommand{\lhead}[2][L]{\fancyhead[#1]{\footnotesize{#2}}}
\renewcommand{\chead}[2][C]{\fancyhead[#1]{\footnotesize{#2}}}
\renewcommand{\rhead}[2][R]{\fancyhead[#1]{\footnotesize{#2}}}
\renewcommand{\lfoot}[2][L]{\fancyfoot[#1]{\footnotesize{#2}}}
\renewcommand{\cfoot}[2][C]{\fancyfoot[#1]{\footnotesize{#2}}}
\renewcommand{\rfoot}[2][R]{\fancyfoot[#1]{\footnotesize{#2}}}
\renewcommand{\headrulewidth}{0pt}
\renewcommand{\footrulewidth}{0pt}
\pagestyle{fancy}
\lhead{}
\chead{}
\rhead{}
\lfoot{}
\cfoot{\thepage{} of \pageref{LastPage}}
\rfoot{}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Title
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\renewcommand\maketitle{
  \begin{center}
    {\Large \textbf{\TITLE}}\\
    \textit{\DATE}\\
  \end{center}
}
