\documentclass{llncs}

% TODO: Mention justDoIt and djinn

\begin{document}
\title{Synthesis of Linear Functional Programs}

\author{Rodrigo Mesquita \and Bernardo Toninho}

\institute{Nova School of Science and Technology}

\maketitle

\begin{abstract}
Type-driven program synthesis concerns itself with generating programs that
satisfy a given type-based specification. In synthesis, the main challenges are
understanding user intent and finding candidate solutions satisfying the
specification in the vast space of valid programs in a reasonable amount of
time.

In this work, we explore how linear types allow for precise specifications
suitable for synthesis, and present a framework for synthesis with linear types
that, through the Curry-Howard correspondence, leverages existing proof-search
techniques for Linear Logic to efficiently find programs satisfying the given
specifications.

We implement the synthesis framework for a standalone language named
\textsc{SILI} which supports classical linear types extended with recursive
algebraic data types, parametric polymorphism and basic refinements, and as a
GHC type-hole plugin that synthesises expressions for Haskell program holes,
using the recently introduced linear types feature -- and show it can generate
more precise solutions, faster than existing alternatives.

% Linear types allow programmers to give more precise and expressive
% specifications of their programs in the form of type signatures.

% Linear types add expressiveness to existing type systems by requiring that
% linear resources be used exactly once. Linear types are becoming part of more
% mainstream languages, such as Haskell, allowing programmers to enforce complex
% resource management policies at the type level
\end{abstract}

\end{document}

