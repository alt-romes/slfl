\documentclass{llncs}

\usepackage[dvipsnames]{xcolor}
\usepackage{xcolor}
\usepackage{xargs}
\usepackage{fancyvrb}
\usepackage{cmll}
\usepackage{mathpartir}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{hyperref}
\usepackage{multirow}
\usepackage{verbatim}
\newenvironment{code}{\footnotesize\verbatim}{\endverbatim\normalsize}

\newcommand{\lolli}{\multimap}
\newcommand{\tensor}{\otimes}
\newcommand{\one}{\mathbf{1}}
\newcommand{\bang}{{!}}
\newcommand{\mypara}[1]{\paragraph{\textbf{#1}.}}

\newcommand{\llet}[2]{\mathsf{let}\ #1\ \mathsf{in}\ #2}

\newcommand{\synname}{\textsc{SILI}}
\def\Rho{P}
\newcommand{\te}[1]{\textrm{\emph{#1}}}

%%%%%%%%%%%%%%  Color-related things   %%%%%%%%%%%%%%

%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format ⊸ = "\lolli "

\newcommand{\myFor}[2]{\For{$#1$}{$#2$}}
\newcommand{\id}[1]{\textsf{\textsl{#1}}}

\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}

%%%%%%%%%%%%  End of Color-related things   %%%%%%%%%%%%


\begin{document}
\title{Synthesis of Linear Functional Programs}

\author{Rodrigo Mesquita \and Bernardo Toninho}

\institute{Nova School of Science and Technology}

\maketitle

% TODO: Mention justDoIt and djinn

\begin{abstract}
Type-driven program synthesis concerns itself with generating programs that
satisfy a given type-based specification.
One of the key challenges of program synthesis lies in finding candidate
solutions that adhere to both the specification and the user's intent in an
actionable amount of time.
%
% In synthesis, the main challenges are
% understanding user intent and finding candidate solutions satisfying the
% specification in the vast space of valid programs in a reasonable amount of
% time.
%
In this work, we explore how linear types allow for precise specifications
suitable for synthesis, and present a framework for synthesis with linear types
that, through the Curry-Howard correspondence, leverages existing proof-search
techniques for Linear Logic to efficiently find programs satisfying the given
specifications.

We implement the synthesis framework both as a standalone language which
supports classical linear types extended with recursive algebraic data types,
parametric polymorphism and basic refinements; and as a GHC type-hole plugin
that synthesises expressions for Haskell program holes, using the recently
introduced linear types feature -- showing it can generate precise solutions,
faster than existing alternatives.

% Linear types allow programmers to give more precise and expressive
% specifications of their programs in the form of type signatures.

% Linear types add expressiveness to existing type systems by requiring that
% linear resources be used exactly once. Linear types are becoming part of more
% mainstream languages, such as Haskell, allowing programmers to enforce complex
% resource management policies at the type level
\end{abstract}

\section{Introduction}

Program synthesis is the automated or semi-automated process of deriving a
program, i.e.~generating code, from a high-level specification. Synthesis can be
seen as a means to improve programmer productivity and program correctness
(e.g. through suggestion and autocompletion).
%
Specifications can take many forms such as natural
language~\cite{chen2021evaluating}, examples~\cite{DBLP:conf/popl/FrankleOWZ16}
or rich types such as polymorphic refinement
types~\cite{DBLP:conf/pldi/PolikarpovaKS16} or graded
types~\cite{DBLP:conf/lopstr/HughesO20}. Regardless of the specification kind,
program synthesis must deal with two main inherent sources of complexity --
searching over the space of valid programs, and interpreting user intent.

% Cuttable
% Synthesis is said to be \emph{type-driven} when it uses types as a form of program
% specification and produces an expression whose type matches the specification.
% %
\emph{Type-driven} synthesis leverages rich types to make specifications more
expressive and prune the valid programs search space, while maintaining a
``familiar'' specification interface (types) for the user.
%
Richer type systems allow for more precise types, which can statically eliminate
various kinds of logical errors by making certain invalid program states
ill-typed (e.g.,~a ``null aware'' type system will ensure at compile-time that
you cannot dereference a null-pointer).
%
For instance, the type $\mathsf{Int} \rightarrow \mathsf{Int} \rightarrow
\mathsf{Int}$, viewed as a specification, is extremely imprecise (there are an
infinite number of functions that instance this type/satisfy this
specification).  However, the richer type $(x{:}\mathsf{Int}) \rightarrow
(y{:}\mathsf{Int}) \rightarrow \{z{:}\mathsf{Int} \mid z = x+y\}$ precisely
specifies a function that adds its two arguments. 

The focus of our work is type-driven synthesis where specifications take the
form of \emph{linear types}.
%
Linear types constrain resource usage in programs by \emph{statically} limiting
the number of times certain resources can be used during their lifetime; in
particular, linear resources must be used \emph{exactly once}. Linearity allows us
to concisely describe interesting functions, since we can easily specify which
arguments must be used linearly in the body of a function. For example, given the
type of the linear map function, |map :: (a ⊸ b) -> [a] ⊸ [b]|,
since the list of $a$s must be used exactly once to produce a list of $b$s,
which can only be done by applying the function to each element, the synthesis
framework will generate code implementing map as expected:
\begin{code}
map f ls = case ls of
  [] -> []
  x:xs -> f x:map f xs
\end{code}

With linear types, the correct handling of resources can be enforced
statically, allowing us to, e.g., ensure a file handle is released exactly once, or
provide a safe interface to manipulate mutable arrays. This last example is
used in Linear Haskell~\cite{} -- they provide an
implementation of |array :: Int -> [(Int,a)] -> Array a| using the following API:
\begin{code}
newMArray :: Int -> (MArray a ⊸ Ur b) ⊸ b
write :: MArray a ⊸ (Int,a) -> MArray a
read :: MArray a ⊸ Int -> (MArray a, Ur b)
freeze :: MArray a ⊸ Ur (Array a)
\end{code}
This doubles as the flagship example of our synthesis framework: we're able to
synthesize the exact implementation given in Linear Haskell from the above API plus |foldl|
and the |array| type specification, generating the program (\emph{in 0.1s}):
\begin{code}
array size pairs = newMArray size (\ma -> freeze (foldl write ma pairs))
\end{code}

%
% TODO: Bad
% They can be applied to resource-aware programming such as concurrent programming
% (e.g. session types for message passing
% concurrency~\cite{DBLP:journals/mscs/CairesPT16}), memory-management
% (e.g.~Rust's ownership types), safely updating-in-place mutable
% structures~\cite{Bernardy_2018}, enforcing protocols for external \textsc{api}s~\cite{Bernardy_2018}, to name a few.

%\mypara{Contributions}
Despite their long-known potential
\cite{Wadler90lineartypes,DBLP:journals/mscs/CairesPT16,Bernardy_2018} and
strong proof-theoretic foundations
\cite{10.1093/logcom/2.3.297,DBLP:conf/cade/ChaudhuriP05,DBLP:journals/tcs/CervesatoHP00},
synthesis with linear types combined with other advanced typing features has
generally been overlooked in the literature. Our contributions are:
\begin{itemize}
\item We introduce linear types as specifications suitable for synthesis both
in their expressiveness and conciseness, by example.
\item We present a framework for synthesis of linear types from specifications
based on classical linear types extended with recursive algebraic data types,
parametric polymorphism and refinements, leveraging established
bottom-up proof-search techniques for linear logic through the Curry-Howard isomorphism,
such as focusing~\cite{} and linear resource management~\cite{}.
\item We present two implementations of our synthesis framework, one as a GHC
plugin that synthesizes expressions for Linear Haskell~\cite{} program holes,
the other in a standalone language with the same features the synthesis process
supports, and benchmark them against similar synthesis that doesn't leverage
linearity.
\end{itemize}

% We first introduce linear types as specifications and outline the synthesis
% process, leveraging linearity, by example (\S~\ref{sec:overview}).
% %
% We then discuss the formal system driving the synthesis
% (\S~\ref{sec:formal_system})
% %
% and describe the architecture of our framework
% named \synname, examining technical details and key implementation challenges
% (\S~\ref{sec:architecture}). Finally, we evaluate our work through
% expressiveness and performance benchmarks (\S~\ref{sec:evaluation}) and discuss
% related work (\S~\ref{sec:related}).  Appendix~\ref{sec:background} covers
% background concepts such as \emph{linear logic} and \emph{sequent calculus}.
% Appendix~\ref{sec:final_system} presents the final set of inference rules.
% Appendix~\ref{sec:examples} lists concrete examples of synthesis with \synname.

\section{Synthesis from Linear Types}\label{sec:overview}

% TODO: Better to separate completely the implementation talk from the
% synthesis framework talk.

% TODO: I don't like the phrasing
% The \synname\ synthesizer combines linear types with recursion,
% parametric polymorphism, recursive algebraic data types, and
% refinement types. The synthesizer is built on top of a system of proof-search for
% linear logic. Proof search relates to program synthesis via the Curry-Howard
% correspondence~\cite{curry:34,howard:80,DBLP:journals/cacm/Wadler15}, which states that \emph{propositions in a logic} are
% \emph{types}, and their \emph{proofs} are well-typed
% \emph{programs} -- finding a proof of a proposition is finding a program with
% that type.

Linear types make for more precise specifications than simple types
because information on which resources must necessarily be used is
encoded in the type. For instance the type $\mathsf{Int} \lolli
\mathsf{Int} \lolli \mathsf{Int}$ denotes a function that \emph{must}
use its two integer arguments to produce an integer.
Their preciseness also affects the search space:
all programs where a linear resource is used non-linearly (i.e. not
\emph{exactly once}) are ill-typed. With linearity built into the
synthesis process, usage of a linear proposition more than once is not
considered, and unused propositions are identified during synthesis,
constraining the space of valid programs.

The core of the synthesis is a \emph{sound} and \emph{complete} system
consisting of \emph{bottom-up} proof-search in propositional linear
logic based on \emph{focusing}~\cite{}. Our approach, being grounded
by propositions-as-types, ensures that all synthesized programs
(i.e.~proofs) are well-typed \emph{by construction} (i.e.~if the
synthesis procedure produces a program, then the program intrinsically
satisfies its specification). Moreover, we can leverage the modularity
of the proof-search based approach along two axes: first, since proof
search need not construct only closed proofs, we can effectively
synthesize program sub-expressions (i.e.~synthesis based on typed
holes); secondly, the framework is amenable to extensions to the core
propositional language, allowing for the introduction of a richer type
structure while preserving the correctness of programs by
construction.



\end{document}

