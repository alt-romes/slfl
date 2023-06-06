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
\usepackage{wrapfig}
\newenvironment{code}{\footnotesize\verbatim}{\endverbatim\normalsize}

\newcommand{\lolli}{\multimap}
\newcommand{\tensor}{\otimes}
\newcommand{\one}{\mathbf{1}}
\newcommand{\bang}{{!}}
\newcommand{\mypara}[1]{\paragraph{\textbf{#1}.}}
\newcommand{\bararound}[1]{\mid\!#1\!\mid}

\newcommand{\llet}[2]{\mathsf{let}\ #1\ \mathsf{in}\ #2}

\newcommand{\synname}{\textsc{SILI}}
\def\Rho{P}
\newcommand{\te}[1]{\textrm{\emph{#1}}}

%%%%%%%%%%%%%%  Color-related things   %%%%%%%%%%%%%%

%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format ⊸ = "\lolli "
%format mid = "\mid"

\newcommand{\myFor}[2]{\For{$#1$}{$#2$}}
\newcommand{\id}[1]{\textsf{\textsl{#1}}}

\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}

%%%%%%%%%%%%  End of Color-related things   %%%%%%%%%%%%


\begin{document}
\title{Functional Program Synthesis from Linear Types}

\author{Rodrigo Mesquita \and Bernardo Toninho}

\institute{Nova School of Science and Technology}

\maketitle

% TODO: Mention justDoIt and djinn

\begin{abstract}
Type-driven program synthesis concerns itself with generating programs that
satisfy a given type-based specification. One of the key challenges of program
synthesis lies in finding candidate solutions that adhere to both the
specification and the user's intent in an actionable amount of time.
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
% Richer type systems allow for more precise types, which can statically
% eliminate various kinds of logical errors by making certain invalid program
% states ill-typed, e.g.,~a ``null aware'' type system will ensure at
% compile-time that you cannot dereference a null-pointer.
%
For instance, the type $\mathsf{Int} \rightarrow \mathsf{Int} \rightarrow
\mathsf{Int}$ can be viewed as a specification, but there are an infinite
number of functions that instance this type/satisfy this specification -- it is
extremely imprecise. On the other hand, the richer type $(x{:}\mathsf{Int})
\rightarrow (y{:}\mathsf{Int}) \rightarrow \{z{:}\mathsf{Int} \mid z = x+y\}$
precisely specifies a function that adds its two arguments.

% The focus of our work is type-driven synthesis where specifications take the
% form of \emph{linear types}.
%
Linear types are a form of richer types that constrains resource usage in
programs by \emph{statically} limiting the number of times certain resources
can be used during their lifetime; in particular, linear resources must be used
\emph{exactly once}. Linearity allows us to concisely describe interesting
functions, since we can easily specify which arguments must be used linearly in
the body of a function. For example, the type of the linear map function,
|map :: (a ⊸ b) -> [a] ⊸ [b]|, specifies a function that must consume the list of $a$s exactly once
to produce a list of $b$s, which can only be done by applying the function to
each element.
% 
A linear type aware type-driven synthesizer might take the |map| type as a specification to unambiguously produce
%
\begin{code}
map f ls = case ls of
  [] -> []
  x:xs -> f x:map f xs
\end{code}
%

It isn't clear, however, how such a synthesizer should operate. Iterating over all possible programs, for instance, ???
However, how can it do so, while being efficient? How to write?
% TODO: Bad
% They can be applied to resource-aware programming such as concurrent programming
% (e.g. session types for message passing
% concurrency~\cite{DBLP:journals/mscs/CairesPT16}), memory-management
% (e.g.~Rust's ownership types), safely updating-in-place mutable
% structures~\cite{Bernardy_2018}, enforcing protocols for external \textsc{api}s~\cite{Bernardy_2018}, to name a few.

%\mypara{Contributions}
Synthesis with linear types combined with other advanced typing features has
generally been overlooked in the literature, despite their long-known potential
\cite{Wadler90lineartypes,DBLP:journals/mscs/CairesPT16,Bernardy_2018} and
strong proof-theoretic foundations
\cite{10.1093/logcom/2.3.297,DBLP:conf/cade/ChaudhuriP05,DBLP:journals/tcs/CervesatoHP00},
%
In this work we aim to bridge this gap -- our contributions are:
\begin{itemize}

\item We introduce linear types as specifications suitable for synthesis both
in their expressiveness and conciseness, by example.

\item We present a framework for synthesis of linear types
(\S~\ref{sec:formal_system}) from specifications based on classical linear
types extended with recursive algebraic data types, parametric polymorphism and
refinements, leveraging established proof-search techniques for linear logic
through the Curry-Howard isomorphism. Specifically, the core of the synthesis
is a \emph{sound} and \emph{complete} system consisting of \emph{bottom-up}
proof-search in propositional linear logic through \emph{focusing}~\cite{}. Our
approach, being grounded in propositions-as-types, ensures that all synthesized
programs (i.e.~proofs) are well-typed \emph{by construction} (i.e.~if the
synthesis procedure produces a program, then the program intrinsically
satisfies its specification).

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


\section{Synthesis is Proof Search}\label{sec:overview}

 Furthermore, their preciseness
also affects the search space: all programs where a linear resource is used
non-linearly %(i.e. not exactly once)
are ill-typed. With linearity built into the synthesis process, usage of a
linear proposition more than once is not considered, and unused propositions
are identified during synthesis, constraining the space of valid programs.

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

% TODO: No... Como abrir esta secção?
% Linear types make for more precise specifications than simple types
% because information on which resources must necessarily be used is
% encoded in the type. For instance the type $\mathsf{Int} \lolli
% \mathsf{Int} \lolli \mathsf{Int}$ denotes a function that \emph{must}
% use its two integer arguments to produce an integer.
% Their preciseness also affects the search space:
% all programs where a linear resource is used non-linearly (i.e. not
% \emph{exactly once}) are ill-typed. With linearity built into the
% synthesis process, usage of a linear proposition more than once is not
% considered, and unused propositions are identified during synthesis,
% constraining the space of valid programs.

% Moreover, we can leverage the modularity
% of the proof-search based approach along two axes: first, since proof
% search need not construct only closed proofs, we can effectively
% synthesize program sub-expressions (i.e.~synthesis based on typed
% holes); secondly, the framework is amenable to extensions to the core
% propositional language, allowing for the introduction of a richer type
% structure while preserving the correctness of programs by
% construction.

% Program synthesis from linear types with polymorphism, recursive
% algebraic data types, and refinements, is essentially new in the synthesis 
% literature. Despite the substantial amount of research on linear logic and
% proof-search upon which we base our core synthesizer, formal guidelines for
% richer types and their intrinsic challenges (such as infinite
% recursion) must be developed.

In this section we formalize the techniques that guide synthesis from our more
expressive specifications, alongside the already well defined rules that model
the core of the synthesizer, putting together a \emph{sound} set of inference
rules that characterizes our framework for linear synthesis of recursive
programs from specifications with the select richer types, and describes the
system in enough detail for the synthesizer to be reproducible by a
theory-driven implementation.
%
We note that a \emph{sound} set of rules guarantees we cannot synthesize
incorrect programs; and that the valid programs derivable through them
reflect the subjective trade-offs we committed to.

\mypara{Core Rules} The system comprises of proof search in
(intuitionistic) linear logic sequent calculus, based on a system of
resource management~\cite{DBLP:journals/tcs/CervesatoHP00,DBLP:journals/tcs/LiangM09}
and focusing.

The core language is a simply-typed linear $\lambda$-calculus with linear
functions ($\lolli$), additive ($\with$) and multiplicative
($\tensor$) pairs
(denoting alternative \emph{vs} simultaneous occurrence of resources),
multiplicative unit (\textbf{1}), additive sums ($\oplus$)
and the exponential modality ($\bang$) (to internalize unrestricted
use of variables). The syntax of terms $(M,N)$ and types $(\tau, \sigma)$ is given below:
\[
  \begin{array}{lclcc}
    M,N & ::= & u, v & \quad & \\
        & \mid & \lambda x.M \mid M\, N & & (\lolli) \\
        & \mid & M \with N\ \vert\ \mathsf{fst}\ M\ \vert\
                 \mathsf{snd}\ M && (\with) \\
        & \mid & M \tensor N\ \vert\ \llet{u\tensor v = M}{N} && (\tensor)\\
        & \mid & \star\ \vert\ \llet{\star = M}{N} && (\one) \\
        & \mid & \mathsf{inl}\ M\ \vert\ \mathsf{inr}\ M\ \vert\ (\mathsf{case}\
    M\ \mathsf{of\ inl}\ u \Rightarrow N_1\ \vert\ \mathsf{inr}\ v \Rightarrow
                 N_2) && (\oplus)\\
        & \mid & \bang M\ \vert\ \llet{\bang u = M}{N} && (\bang)\\[0,5em]
    \tau, \sigma & ::= & a\ \vert\ \tau \lolli \sigma\ \vert\ \tau \with \sigma\
    \vert\ \tau \tensor \sigma\ \vert\ \mathbf{1}\ \vert\ \tau \oplus \sigma\ \vert\ \bang \tau
  \end{array}
\]


In intuitionistic sequent calculi, each connective has a so-called \emph{left}
and a \emph{right} rule, which effectively define how to decompose an ambient
assumption of a given proposition and how to prove a certain proposition is
true, respectively.  Andreoli's \emph{focusing} for linear logic~\cite{10.1093/logcom/2.3.297} 
is a technique to remove non-essential nondeterminism from
proof-search by structuring the application of so-called invertible and
non-invertible inference rules. Andreoli observed that the connectives of linear
logic can be divided into two categories, dubbed synchronous and asynchronous.
Asynchronous connectives are those whose right rules are \emph{invertible}, i.e.
they can be applied eagerly during proof search without losing provability and
so the order in which these rules are applied is irrelevant, and whose left
rules are not invertible. Synchronous connectives are dual. The asynchronous
connectives are $\lolli$ and $\with$ and the synchronous are
$\tensor,\textbf{1},\oplus,\bang$.

Given this separation, focusing divides proof search into two
phases: %
the inversion phase ($\Uparrow$), in which we apply \emph{all}
invertible rules eagerly, and the focusing phase ($\Downarrow$), in
which we decide a proposition to focus on, and then apply
non-invertible rules, staying \emph{in focus} until we reach an
asynchronous (i.e. invertible proposition), the proof is complete, or
no rules are applicable, in which case the proof must \emph{backtrack}
to the state at which the focusing phase began.  As such, with
focusing, the linear sequent calculus judgment 
$\Gamma; \Delta \vdash A$, meaning that $A$ is derivable from the linear
assumptions in $\Delta$ and unrestricted assumptions in $\Gamma$,
is split into four judgments, grouped into the two phases ($\Uparrow,
\Downarrow$).
%
For the invertible phase, an \emph{inversion} 
context $\Omega$ holds propositions that result from
decomposing connectives.
% (propositions we'll later try to invert,
% moving them to the linear context ($\Delta$) when we fail to).
The right inversion and left inversion judgments are written
$\Gamma; \Delta; \Omega \vdash A \Uparrow$ and $\Gamma; \Delta;
\Omega \Uparrow\ \vdash A$, respectively, where the $\Uparrow$
indicates the connective or context being inverted.
For the focusing phase (i.e.~all non-invertible rules can apply), 
the proposition under focus can be the goal or 
one in $\Gamma$ or $\Delta$. The right focus judgment is written 
$\Gamma;\Delta \vdash A \Downarrow$ and the left focus judgment is
written $\Gamma;\Delta; B\Downarrow\ \vdash A$, where $\Downarrow$
indicates the proposition under focus.

To handle the context splitting required to prove subgoals, we augment the
judgments above using Hodas and Miller's resource management technique where a pair of
input/output linear contexts is used to propagate the yet unused linear
resources across subgoals; e.g. the left inversion judment is written
$\Gamma; \Delta/\Delta'; \Omega \Uparrow\ \nolinebreak\vdash A$ where $\Delta$ is the input
linear context and $\Delta'$ is the output one.


Putting together linear logic and linear lambda calculus through the Curry-Howard correspondence, resource
management, and focusing, we get the following core formal system
(inspired by~\cite{DBLP:conf/cade/ChaudhuriP05,fpnotes}) -- in which the
rule $\lolli$R is read: to synthesize a program of type $A \lolli B$ while inverting
right (the $\Uparrow$ on the goal), with unrestricted context $\Gamma$, linear
context $\Delta$, and inversion context $\Omega$, synthesize a program of type $B$ with
an additional hypothesis of type $A$ named $x$ in the $\Omega$ context,
resulting in the program $M$ and output linear
context $\Delta'$ that cannot contain the added hypothesis $x{:}A$. Finally, the
resulting program is $\lambda x . M$ and the output linear context is
$\Delta'$.

We start with right invertible rules, which decompose the goal proposition until it's synchronous.
%
\begin{mathpar}

    % -o R
    \infer*[right=($\lolli R$)]
    {\Gamma ; \Delta/\Delta' ; \Omega, x{:}A \vdash M : B \Uparrow \and x
    \notin \Delta'}
    {\Gamma ; \Delta/\Delta' ; \Omega \vdash \lambda x . M : A
    \lolli B \Uparrow}

\and

    % & R
    \infer*[right=($\with R$)]
    {\Gamma ; \Delta/ \Delta' ; \Omega \vdash M : A \Uparrow \and \Gamma ;
    \Delta/ \Delta'' ; \Omega \vdash N : B \Uparrow \and \Delta' = \Delta''}
    {\Gamma ; \Delta/\Delta' ; \Omega \vdash  (M \with N) : A
    \with B \Uparrow}

\end{mathpar}

When we reach a non-invertible proposition on the right, we start inverting the
$\Omega$ context. The rule to transition to inversion on the left is:
%
\begin{mathpar}
    \infer*[right=($\Uparrow$R)]
    {\Gamma ; \Delta/ \Delta' ; \Omega \Uparrow\ \vdash C \and C\ \textrm{not
    right asynchronous}}
    {\Gamma ; \Delta/\Delta' ; \Omega \vdash C \Uparrow}
\end{mathpar}

We follow with left invertible rules for asynchronous connectives, which
decompose asynchronous propositions in $\Omega$.
\[
  \begin{array}{c}

    \infer*[right=($\tensor L$)]
    {\Gamma ; \Delta/ \Delta' ; \Omega, y{:}A, z{:}B \Uparrow\ \vdash M : C
    \and y,z \notin \Delta'}
    {\Gamma ; \Delta/\Delta' ; \Omega, x{:}A \tensor B \Uparrow\ \vdash\
    \textrm{let}\ y \tensor z = x\ \textrm{in}\ M : C}\\[0.5em]
    \infer*[right=($1 L$)]
    {\Gamma ; \Delta/ \Delta' ; \Omega \Uparrow\ \vdash M : C}
    {\Gamma ; \Delta/\Delta' ; \Omega, x{:}1 \Uparrow\ \vdash\ \textrm{let}\
    \star =
    x\ \textrm{in}\ M : C}\\[0.5em]
    \mprset{flushleft}
    \infer*[right=($\oplus L$)]
    {
    \Gamma ; \Delta/ \Delta' ; \Omega, y{:}A \Uparrow\ \vdash M : C \and
    y \notin \Delta' \\
    \Gamma ; \Delta/ \Delta'' ; \Omega, z{:}B \Uparrow\ \vdash N : C \\
    z \notin \Delta'' \\
    \Delta' = \Delta''
    }
    {\Gamma ; \Delta/\Delta' ; \Omega, x{:}A \oplus B \Uparrow\ \vdash\
    \textrm{case}\ x\ \textrm{of}\ \textrm{inl}\ y \rightarrow M\ \mid\
    \textrm{inr}\ z \rightarrow N : C}
    \\[0.5em]
    \infer*[right=($\bang L$)]
    {\Gamma, y{:}A ; \Delta/ \Delta' ; \Omega \Uparrow\ \vdash M : C}
    {\Gamma ; \Delta/\Delta' ; \Omega, x{:}\bang A \Uparrow\ \vdash\
    \textrm{let}\ \bang y = x\ \textrm{in}\ M : C}
\end{array}
\]

When we find a synchronous (i.e. non-invertible) proposition in $\Omega$,
we simply move it to the linear context $\Delta$, and keep inverting on the left:
\begin{mathpar}
    \infer*[right=($\Uparrow$L)]
    {\Gamma; \Delta, A/\Delta'; \Omega \Uparrow\ \vdash C \and A\ 
    \textrm{not left asynchronous}}
    {\Gamma; \Delta/\Delta'; \Omega, A \Uparrow\ \vdash C}
\end{mathpar}

After inverting all the asynchronous propositions in $\Omega$ we'll reach a state
where there are no more propositions to invert ($\Gamma'; \Delta'; \cdot
\Uparrow\ \vdash C$). At this point, we want to \emph{focus} on a proposition.
The focus object will be: the proposition on the right (the
goal), a proposition from the linear $\Delta$ context, or a proposition from the
unrestricted $\Gamma$ context. For these options we have three \emph{decision}
rules:
\[
  \begin{array}{c}
    \infer*[right=(decideR)]
    {\Gamma; \Delta/\Delta' \vdash C \Downarrow \and C\ \textrm{not atomic}}
    {\Gamma; \Delta/\Delta';\cdot \Uparrow\ \vdash C}\\[0.5em]
    \infer*[right=(decideL)]
    {\Gamma; \Delta/\Delta' ; A \Downarrow\ \vdash C}
    {\Gamma; \Delta, A/\Delta';\cdot \Uparrow\ \vdash C}
\qquad
    \infer*[right=(decideL!)]
    {\Gamma, A; \Delta/\Delta' ; A \Downarrow\ \vdash C}
    {\Gamma, A; \Delta/\Delta';\cdot \Uparrow\ \vdash C}
  \end{array}
  \]

The decision rules are followed by either left or right focus rules.
To illustrate, consider the $\lolli$L left focus rule. The rule
states that to produce a program of type $C$ while left focused on
the function $x$ of type $A\lolli B$, we first check that we can produce a
program of type $C$ by using $B$. If this succeeds in producing some
program $M$, this means that we can apply $x$ to solve our
goal. We now synthesize a program $N$ of type $A$, switching to the
right inversion judgment ($\Uparrow$). To construct the overall
program, we replace in $M$ all occurrences of variable $y$ with the
application $x\,N$. The remaining left rules follow a similar
pattern. The right focus rules are read similarly to right inversion ones,
albeit the goal and sub-goals are under focus (except for $\bang R$).
%
\begin{mathpar}
      \infer*[right=($\lolli L$)]
    {\Gamma; \Delta/\Delta'; y{:}B \Downarrow\ \vdash M : C \and \Gamma;
    \Delta'/\Delta''; \cdot \vdash N : A \Uparrow}
    {\Gamma; \Delta/\Delta''; x{:}A \lolli B \Downarrow\ \vdash M\{(x\,N)/y\} : C}
\and
    \infer*[right=($\with L_1$)]
    {\Gamma; \Delta/\Delta'; y{:}A \Downarrow\ \vdash M : C}
    {\Gamma; \Delta/\Delta'; x{:}A \with B \Downarrow\ \vdash M\{(\textrm{fst}\ x)/y\} : C}
\and
    \infer*[right=($\with L_2$)]
    {\Gamma; \Delta/\Delta'; y{:}B \Downarrow\ \vdash M : C}
    {\Gamma; \Delta/\Delta'; x{:}A \with B \Downarrow\ \vdash
      M\{(\textrm{snd}\ x)/y\} : C}
    \and
    \infer*[right=($\tensor R$)]
    {\Gamma; \Delta/\Delta' \vdash M : A \Downarrow \and \Gamma ; \Delta'/\Delta'' \vdash N
    : B \Downarrow}
    {\Gamma; \Delta/\Delta'' \vdash (M \tensor N) : A \tensor B \Downarrow}
\and
    \infer*[right=($1 R$)]
    { }
    {\Gamma; \Delta/\Delta \vdash \star : \textbf{1} \Downarrow}
\and
    \infer*[right=($\oplus R_1$)]
    {\Gamma; \Delta/\Delta' \vdash M : A \Downarrow}
    {\Gamma; \Delta/\Delta' \vdash\ \textrm{inl}\ M : A \oplus B \Downarrow}
\and
    \infer*[right=($\oplus R_2$)]
    {\Gamma; \Delta/\Delta' \vdash M : B \Downarrow}
    {\Gamma; \Delta/\Delta' \vdash\ \textrm{inr}\ M : A \oplus B \Downarrow}
\and
    \infer*[right=($\bang R$)]
    {\Gamma; \Delta/\Delta'; \cdot \vdash M : A \Uparrow \and \Delta = \Delta'}
    {\Gamma; \Delta/\Delta \vdash \bang M : \bang A \Downarrow}
\end{mathpar}
%
Eventually, the focus proposition will no longer be synchronous, i.e. it's
atomic or asynchronous. If we're left focused on an atomic proposition we either
instantiate the goal or fail. Otherwise the left focus is asynchronous and we
can start inverting it. If we're right focused on a proposition that isn't right
synchronous, we switch to inversion as well. Three rules model these conditions:
%
\[
\begin{array}{c}
    \infer*[right=(init)]
    {  }
    {\Gamma; \Delta/\Delta'; x{:}A \Downarrow\ \vdash x : A}
    \qquad
     \infer*[right=($\Downarrow R$)]
    {\Gamma; \Delta/\Delta'; \cdot \vdash A \Uparrow}
    {\Gamma; \Delta/\Delta' \vdash A \Downarrow}\\[0.5em]
    \infer*[right=($\Downarrow L$)]
    {\Gamma; \Delta/\Delta'; A \Uparrow\ \vdash C \and A\ \textrm{not atomic and not left synchronous}}
    {\Gamma; \Delta/\Delta'; A \Downarrow\ \vdash C}

\end{array}
\]
The rules written above together make the core of our synthesizer. Next, we'll
present new rules that align and build on top of these to synthesize recursive
programs from more expressive (richer) types.

\mypara{Algebraic Data Types} In its simplest form, an algebraic data type (ADT)
is a tagged sum of any type, i.e. a named type that can be instantiated by one of many
tags (or constructors) that take some value of  a fixed type, which might
be, e.g., a product type ($A \tensor B$), or unit ($1$), in practice allowing
for constructors with an arbitrary number of parameters. In the \synname\
language, the programmer can define custom ADTs; as an example, we show the
definition of an ADT which holds zero, one, or two
values of type $A$, using the syntax: |data Container
= None 1 mid One A mid Two (A * A)|. The grammar is extended as (where $C$ is an ADT
constructor and $T$ is an ADT):
\[
\begin{array}{lclc}
    M,N & ::= & \dots\ \vert\ \emph{C}_n\ M\ \vert\ (\mathsf{case}\ M\ \mathsf{of}\ \dots\ \vert\ \emph{C}_n\ u \Rightarrow N) \\
    \tau, \sigma & ::= & \dots\ \vert\ T \\
 %    $ADT$ & $\ ::=\ $ & (\textsf{data} $\langle\emph{name}\rangle$\ $=$\ $\emph{Cons}_1\ \tau$\
% $\vert$\ $\dots$\ $\vert$\ $\emph{Cons}_n\ \tau$) \\
\end{array}
\]

The semantics of ADTs relate to those of the plus ($\oplus$) type -- both are
additive disjunctions.  To construct a value of an ADT we must use one of its
constructors, similar to the way $\oplus$ requires only proof of either the left
or right type it consists of. Analogously, we can deconstruct a value of an ADT
via pattern matching on its constructors, where all branches of the pattern
match must have the same type -- akin to the left rule for the $\oplus$
connective. In effect, the inference rules for a simple ADT are a generalized
form of the $\oplus$ rules.  Therefore, there's one left rule for ADTs, and an
arbitrary number of right rules, one for each constructor, where ADT $T$ and
its constructors stand for any ADT defined as |data T = C1 X1 mid C2 X2 mid ... mid Cn Xn|:
%
\begin{mathpar}
    \infer*[right=(adtR)]
    {\Gamma; \Delta/\Delta' \vdash M : X_n \Downarrow}
    {\Gamma; \Delta/\Delta' \vdash\ C_n \ M : T \Downarrow}
\and
    \mprset{flushleft}
    \infer*[right=(adtL)]
    {
        \Gamma ; \Delta/ \Delta'_1 ; \Omega, y_1{:}X_1 \Uparrow\ \vdash M_1 : C
        \and
        y_1 \notin \Delta'_1
        \\
        \Gamma ; \Delta/ \Delta'_2 ; \Omega, y_2{:}X_2 \Uparrow\ \vdash M_2 : C
        \\
        y_2 \notin \Delta'_2
        \\\\
        \\ \dots
        \\
        \Gamma ; \Delta/ \Delta'_n ; \Omega, y_n{:}X_n \Uparrow\ \vdash M_n : C
        \\
        y_n \notin \Delta'_n
        \\
        \Delta'_1 = \Delta'_2 = \dots = \Delta'_n
    }
    {\Gamma ; \Delta/\Delta'_1 ; \Omega, x{:}T \Uparrow\
    \vdash\ \textrm{case}\ x\ \textrm{of}\ \dots\ \mid\ C_n\ y_n
    \rightarrow M_n : C}
\end{mathpar}

% repetition does not legitimize :p

A more general formulation of ADTs says an ADT can be recursive (or
"inductively defined"), meaning constructors can take as arguments
values of the type they are defining. This change has
a significant impact in the synthesis process. Take, for instance, the ADT
defined as |data T = C1 T|, the synthesis goal
$T \lolli C$, and part of its derivation:
%
{\small
\begin{mathpar}
    \infer*[right=($\Uparrow R$)]
    {
        \infer*[right=(adtL)]
        {
            \infer*[right=(adtL)]
            {\dots}
            {\Gamma; \Delta/\Delta'; \Omega, y{:}T \Uparrow\ \vdash \textrm{case}\ y\ 
            \textrm{of}\ C_1\ z \rightarrow \dots : C}
        }
        {\Gamma; \Delta/\Delta'; \Omega, x{:}T \Uparrow\ \vdash \textrm{case}\ x\ 
        \textrm{of}\ C_1\ y \rightarrow \dots : C}
    }
    {\Gamma; \Delta/\Delta'; \Omega, x{:}T \vdash \dots : C
    \Uparrow}
\end{mathpar}}
%
Using our current system, we are to apply an infinite number of times
(\textsc{adtL}), never closing the proof. Symmetrically, the
derivation for goal $T$ is also infinite.
%
{\small
\begin{mathpar}
    \infer*[left=(adtR)]
    {
        \infer*[left=(adtR)]
        {
            \infer*[left=(adtR)]
            {\dots}
            {\Gamma; \Delta/\Delta'; \Omega \vdash C_1 \dots : T \Downarrow}
        }
        {\Gamma; \Delta/\Delta'; \Omega \vdash C_1 \dots : T \Downarrow}
    }
    {\Gamma; \Delta/\Delta'; \Omega \vdash C_1 \dots : T \Downarrow}
\end{mathpar}}
%
To account for this situation, we impede the decomposition of an ADT in subsequent
proofs of its branches, and, symmetrically, don't allow construction of an
ADT when trying to synthesize an argument for its constructor.
%
%
For this, we need two more contexts, $\Rho_C$
for constraints on construction and $\Rho_D$ for constraints on
deconstruction. Together, they hold a list of ADTs that cannot be constructed or
deconstructed at a given point in the proof. For convenience, they are represented by a single $\Rho$ if
unused. All non-ADT rules trivially propagate these. The ADT rules
are then extended as follows, where $\Rho'_C = \Rho_C,T$ if $T$ is
recursive and $\Rho'_C = \Rho_C$ otherwise ($\Rho'_D$ is dual):
%
%TODO: ... we can actually instance ADTs that take no arguments even if they are restricted

\begin{mathpar}
    \infer*[right=(adtR)]
    {(\Rho_C'; \Rho_D) ; \Gamma; \Delta/\Delta' \vdash M : X_n \Downarrow \and
    T \notin \Rho_C}
    {(\Rho_C; \Rho_D);\Gamma; \Delta/\Delta' \vdash\ C_n \ M : T \Downarrow}
\and
    \mprset{flushleft}
    \infer*[right=(adtL)]
    {
        T \notin \Rho_D
        \and
        \Delta'_1 = \dots = \Delta'_n 
        \\
        (\Rho_C; \Rho'_D);\Gamma ; \Delta/ \Delta'_1 ; \Omega, y_1{:}X_1 \Uparrow\ \vdash M_1 : C
        \and
        y_1 \notin \Delta'_1
        \\\\
        \\ \dots
        \\\\
        (\Rho_C; \Rho'_D);\Gamma ; \Delta/ \Delta'_n ; \Omega, y_n{:}X_n \Uparrow\ \vdash M_n : C
        \and
        y_n \notin \Delta'_n
    }
    {(\Rho_C; \Rho_D); \Gamma ; \Delta/\Delta'_1 ; \Omega, x{:}T \Uparrow\
    \vdash\ \textrm{case}\ x\ \textrm{of}\ \dots\ \mid\ C_n\ y_n
    \rightarrow M_n : C}
\end{mathpar}
% where
% \begin{mathpar}
%     \Rho'_C = \textrm{\textbf{if}}\ T\ \textrm{is recursive \textbf{then}}\ \Rho_C,
%     T\ \textrm{\textbf{else}}\ \Rho_C

%     \Rho'_D = \textrm{likewise}
% \end{mathpar}

These modifications prevent the infinite derivations in the scenarios
described above. However, they also greatly limit the space of
derivable programs, leaving the synthesizer effectively unable to
synthesize from specifications with recursive types. To prevent this,
we add three rules to complement the restrictions on construction
and destruction of recursive types.
%
First, since we can't deconstruct some ADTs any further because of a restriction,
but must utilize all propositions linearly in some way, all propositions in $\Omega$ whose
deconstruction is restricted are to be moved to the linear context $\Delta$.
%
Second, without any additional rules, an ADT in the linear context
will loop back to the inversion context, jumping back and forth
between the two contexts; instead, when focusing on an ADT, we should
either instantiate the goal (provided they're the same type), or switch
to inversion if and only if its decomposition isn't restricted. The
three following rules ensure this:

\begin{mathpar}
    \infer*[right=(adt$\Uparrow$L)]
    {
        (\Rho_C; \Rho_D);\Gamma; \Delta, x{:}T/\Delta'; \Omega \Uparrow\ \vdash M : C
        \and
        T \in \Rho_D
    }
    {(\Rho_C; \Rho_D);\Gamma; \Delta/\Delta'; \Omega, x{:}T \Uparrow\ \vdash M : C}
    \and
    \infer*[right=(adt-init)]
    {  }
    {\Rho; \Gamma; \Delta/\Delta'; x{:}T \Downarrow\ \vdash x : T}
    \and
    \infer*[right=(adt$\Downarrow$L)]
    {(\Rho_C; \Rho_D); \Gamma; \Delta/\Delta'; x{:}T \Uparrow\ \vdash M :
    T \and T \notin \Rho_D}
    {(\Rho_C; \Rho_D); \Gamma; \Delta/\Delta'; x{:}T \Downarrow\ \vdash M : T}
\end{mathpar}
% TODO: Adicionar regra que diz que se for ADT Rec -o A então a construção de
% ADT Rec é logo restrita?? parece que acelera minimamente mas não arranjo um
% exemplo em que seja crucial. pode ser uma coisa que tenha ficado para resolver
% uma coisa antiga que ficou resolvida mais tarde com outra modificação e então
% é agora inutil. Talvez seja demais adicionar à regra
%
Altogether, the rules above ensure that a recursive ADT will be deconstructed
once, and that subsequent equal ADTs will only be useable from the linear
context -- essentially forcing them to be used to instantiate another proposition,
which will typically be an argument for the recursive call.


\mypara{Recursion} The main idea behind synthesis of recursive
programs is the labeling of the main goal and the addition of its
type, under that name, to the unrestricted context. That is, to
synthesize a recursive function of type $A \lolli B$ named \emph{f},
the initial judgment can be written as
\begin{mathpar}
    \infer
    {\dots}
    {\Gamma, f{:}A \lolli B; \Delta/\Delta'; \Omega \vdash M :
    A \lolli B \Uparrow}
\end{mathpar}
and, by definition, all subsequent inference rules will have
($f{:}A \lolli B$) in the $\Gamma$ context too.
We can also force the usage of the recursive call by adding it not only to the
unrestricted context, but to the linear one as well.
%
However, we must restrict immediate uses of the recursive call since
otherwise every goal would have a trivial proof (a non-terminating
function that just calls itself), shadowing relevant solutions.
Instead, our framework allows the use of recursion only after having
deconstructed a recursive ADT via the following invariant: the
recursive hypothesis can only be used in \emph{recursive branches of
  ADT deconstruction}, i.e. the recursive call should only take
``smaller'', recursive, hypothesis as arguments. To illustrate, in any
recursive function with a list argument (whose type is defined as
|data List = Nil mid Cons (A * List)|), recursive
calls are only allowed when considering a judgment of the form
$\textrm {List} \vdash C$, i.e.~when a list value is available to
produce the goal $C$, and only in the \emph{Cons}
branch. Furthermore, we also forbid the usage of the recursive function when
synthesizing arguments to use it.
% TODO : não sei se precisa de melhor explicação mas foi uma coisa que fiz para
% não gerar um programa recursivo.
% (TODO: rewrite? O bold é meio estranho não?)


\mypara{Polymorphic Types} A polymorphic specification is a type of form
$\forall \overline{\alpha}.\ \tau$ where $\overline{\alpha}$ is a set of
variables that stand for any (non-polymorphic) type in $\tau$. Such a type is
also called a \emph{scheme}.  Synthesis of a scheme comprises of turning it into
a non-quantified type, and then treating its type variables uniformly.  First,
type variables are considered \emph{atomic types}, then, we instantiate the
bound variables of the scheme as described by the Hindley-Milner inference
method's~\cite{DBLP:journals/jcss/Milner78,10.2307/1995158} instantiation rule (put simply, generate fresh names
for each bound type variable); e.g. the scheme $\forall \alpha.\ \alpha \lolli
\alpha$ could be instantiated to $\alpha0 \lolli \alpha0$. We add a rule for
this, where $\forall \overline{\alpha}.\ \tau \sqsubseteq \tau'$ indicates type
$\tau'$ is an \emph{instantiation} of type scheme $\forall \overline{\alpha}.\
\tau$:
%
\begin{mathpar}
    \infer*[right=($\forall R$)]
    { \Rho; \Gamma; \Delta/\Delta'; \Omega \vdash \tau' \Uparrow \and \forall
    \overline{\alpha}.\ \tau
    \sqsubseteq \tau'}
    {\Rho; \Gamma; \Delta/\Delta'; \Omega \vdash \forall \overline{\alpha}.\
    \tau \Uparrow}
\end{mathpar}
%
As such, the construction of a derivation in which the only rule that can derive
an atom is the \textsc{init} rule corresponds to the synthesis of a program
where some expressions are treated agnostically (nothing constrains their type),
i.e.~a polymorphic program. The simplest example is the polymorphic function
\emph{id} of type $\forall \alpha .\ \alpha \lolli \alpha$. The program
synthesized from that specification is $\lambda x . x$, a lambda abstraction
that does not constrain the type of its parameter $x$ in any way.

The main challenge of polymorphism in synthesis is the usage of schemes from the
unrestricted context.  To begin with, $\Gamma$ now holds both (monomorphic)
types and schemes. Consequently, after the rule \textsc{decideLeft!} is applied,
we are left-focused on either a type or a scheme. Since left focus on a type is
already well defined, we need only specify how to focus on a scheme.
%
Our algorithm instantiates bound type variables of the focused scheme with fresh
\emph{existential} type variables, and the instantiated type becomes the left
focus. Inspired by the Hindley-Milner system, we also generate inference
constraints on the existential type variables (postponing the decision of what
type it should be to be used in the proof), and collect them in a new
constraints context $\Theta$ that is propagated across derivation branches the
same way the linear context is (by having an input and output context
($\Theta/\Theta'$)).  In contrast to Hindley-Milner's inference, everytime a
constraint is added it is solved against all other constraints -- a branch of
the proof search is desired to fail as soon as possible.
%TODO: Como fazer? \todo{O que significa $?\alpha$ ? Não foi explicado -- no
%Hindley-Milner nao ha propriamente o problema de misturar variaveis
%existenciais com universais}
Note that we instantiate the scheme with \emph{existential} type variables
($?\alpha$) rather than just type variables ($\alpha$) since the latter
represent universal types during synthesis, and the former represent a concrete
instance of a scheme, that might induce constraints on other type variables.
Additionally, we require that all existential type variables are assigned a
type. These concepts are formalized with the following rules, where $\forall
\overline{\alpha}.\ \tau \sqsubseteq_E \tau'$ means type $\tau'$
is an \emph{existential instantiation} of scheme $\forall \overline{\alpha}.\ \tau$,
$\textrm{ftv}_E(\tau')$ is the set of free \emph{existential} type variables in
type $\tau'$, $?\alpha \mapsto \tau_x$ is a mapping from \emph{existential} type
$?\alpha$ to type $\tau_x$, and $\textsc{unify}(c, \Theta)$ indicates wether
constrain $c$ can be unified with those in $\Theta$:

\begin{mathpar}
    \infer*[right=($\forall L$)]
    {
        \Theta/\Theta'; \Rho; \Gamma; \Delta/\Delta'; \tau' \Downarrow\ \vdash C
        \\
        \forall \overline{\alpha}.\ \tau \sqsubseteq_E \tau'
        \\
        \textrm{ftv}_E(\tau') \cap \{ ?\alpha\ \vert\ (?\alpha \mapsto \tau_x) \in \Theta'\} = \emptyset
    }
    {\Theta/\Theta'; \Rho; \Gamma; \Delta/\Delta'; \forall \overline{\alpha}.\ \tau \Downarrow\ \vdash C}
    \and
    \infer*[right=($?L$)]
    {\textsc{unify}(?\alpha
    \mapsto C, \Theta)}
    {\Theta/\Theta, ?\alpha \mapsto C ; \Rho; \Gamma; \Delta/\Delta';
    x{:}?\alpha \Downarrow\ \vdash x : C}
    \and
    \infer*[right=($\Downarrow ?L$)]
    {\textsc{unify}(?\alpha
    \mapsto A, \Theta)}
    {\Theta/\Theta, ?\alpha \mapsto A ; \Rho; \Gamma; \Delta/\Delta';
    x{:}A \Downarrow\ \vdash x : ?\alpha}
\end{mathpar}


\mypara{Further Challenges} We now consider two more sources of infinite
recursion in the synthesis process. The first is the use of an unrestricted
function to synthesize a term of type $\tau$ that in turn will require a term of
the same type $\tau$. An example is the sub-goal judgment $(a \lolli
b \lolli b); (a \lolli b \lolli b) \Downarrow\ \vdash b$ that
appears while synthesizing \emph{foldr} -- we apply ($\lolli$L)
until we can use \textsc{init} ($b \Downarrow\ \vdash b$), and then we must
synthesize an argument of type $b$. Without any additional restrictions, we
may become again left focused on $(a \lolli b \lolli b)$, and again require $b$,
and on and on. The solution will be to disallow the usage of the same function
to synthesize the same goal a second time further down in the derivation.

The other situation occurs when using an unrestricted polymorphic function that
requires synthesis of a term with an existential type when the goal is an
existential type. In contrast to the previous problem, the type of the goal and
of the argument that will cause the loop won't match exactly, since instantiated
bound variables are always fresh. For example, for $\forall \alpha,\beta .\
\alpha\lolli\beta\lolli\beta;?\alpha\lolli?\beta\lolli?\beta \Downarrow\ \vdash\
?\sigma$, we'll unify $?\beta$ with $?\sigma$, and then require a term of type
$?\beta$ (not $?\sigma$). We want to forbid the usage of the \emph{same}
function to attain \emph{any} existential goal, provided that function might
create existential sub-goals (i.e. it's polymorphic). However, we noticed that,
even though for most tried problems this ``same function'' approach worked,
context-heavy problems such as \emph{array} (seen in \S~\ref{sec:overview})
wouldn't terminate in a reasonable amount of time.
%
% In fact, with $n$ polymorphic functions in the unrestricted context, the
% complexity of searching for a program of any existential type $?\alpha$, while
% restricting solely the used function, is $O(n!)$~\ref{exemplo_apendice?}.
%
As such, we'll instead define that, given an existential\footnote{a type 
is existential when any of its components is an existential type variable} goal $C$,
we can only ``decide left!'' on a proposition $A$ if, altogether, 
the amount of times we've ``decided left!'' on an polymorphic function to produce
an existential goal is less than a \emph{constant ``existential depth''} $d_e$
(which controls a \emph{depth} aspect of the synthesis process).
%
% This approach reduces the complexity of our proof-search algorithm for
% existential types to $O(\tfrac{n!}{d_e!}) = O(n^{d_e})$.

Extending the restrictions context ($\Rho$) with restrictions on using the
unrestricted context ($\Rho_{L!}$), we modify \textsc{decideLeft!} to formalize
the two previous paragraphs, where $\textsc{isExist}(C)$ is true if $C$ is an
existential type, $\textsc{isPoly}(f)$ is true if $f$ is universally
quantified (i.e. $f$ has form $\forall\overline{\alpha} f'$), and
$\Rho_{L!}' = \Rho_{L!},(A, C)$ if $A$ is a function and $\Rho_{L!}' =
\Rho_{L!}$ otherwise:
%
\begin{mathpar}
    \mprset{flushleft}
    \infer*[right=(decideL!)]
    {
    (A, C) \notin \Rho_{L!}
    \\
    \textsc{isExist}(C) \Rightarrow \bararound{\{u\ \mid\ (f,u)\in\Rho_{L!},\textsc{isPoly}(f),\textsc{isExist}(u)\}} < d_e
    \\
    \Theta/\Theta';(\Rho_C,\Rho_D,\Rho_{L!}');\Gamma, A; \Delta/\Delta' ; A
    \Downarrow\ \vdash C
    }
    {\Theta/\Theta';(\Rho_C,\Rho_D,\Rho_{L!});\Gamma, A; \Delta/\Delta';\cdot \Uparrow\ \vdash C}
    \\
\end{mathpar}

\mypara{Polymorphic ADTs} To allow type parameters and the use of universally quantified type
variables in ADT constructors, we must guarantee that the
\textsc{adt-init} rule can unify the type parameters and that when constructing or
destructing an ADT, type variables in constructor parameters are substituted by
the actual type (i.e. to construct |List Int| with
|data List a = Cons (a * List a)|, we wouldn't try to synthesize |(a * List a)|,
but rather |(Int * List Int)|). To unify $T_{\overline\alpha}$ with $T_{\overline\beta}$,
the sets of type parameters $\overline\alpha$ and $\overline\beta$ must satisfy $\bararound{\overline\alpha} = \bararound{\overline\beta}$
together with $\forall i\ 0 \leq i \land i < \bararound{\overline\alpha} \land
\textsc{unify}(\overline\alpha_i \mapsto \overline\beta_i)$. The constructor
type substitution needn't be explicit in the rule:
\begin{mathpar}
    \infer*[right=(adt-init)]
    {\textsc{unify}(T_{\overline\alpha} \mapsto T_{\overline\beta}, \Theta)}
    {\Theta/\Theta,T_{\overline\alpha} \mapsto T_{\overline\beta},\Rho; \Gamma; \Delta/\Delta'; x{:}T_{\overline\alpha} \Downarrow\ \vdash x :
    T_{\overline\beta}}
\end{mathpar}

\mypara{Refinement Types} Refinement types are types with a predicate (a non-existing predicate is the same as it
being \emph{true}); dependent types are functions with
refinement types in which the argument type is labeled and said label can be used in the predicates
of the return type (e.g. $(x : \mathsf{Int}) \lolli \{y : \mathsf{Int}\ \vert\ y = x\}$ specifies a function that
takes an Int and returns an Int of equal value). We extend
the types syntax with our refinement types:
\[
\begin{tabular}{lclc}
    $\tau$ & $\ ::=\ $ & $ \dots \vert\  (x:\tau) \lolli \sigma\ \vert\  \{x:\tau\ \vert\ P\}$ \\
    $P$ & $\ ::=\ $ & $P = P\ \vert\ P \neq P\ \vert\ P \vee P\ \vert\ P \wedge
    P\ \vert\ P \Rightarrow P\ \vert\ n = n\ \vert\ n \neq n$ \\
    & & $\vert\ n \leq n\ \vert\ n \geq n\ \vert\ n < n\ \vert\ n > n\ \vert\
    true\ \vert\ false\ \vert\ x$ \\
    $n$ & $\ ::=\ $ & $n * n\ \vert\ n + n\ \vert\ n - n\ \vert\
    \langle\emph{natural}\rangle\ \vert\ x$
    \\
\end{tabular}
\]
The addition of refinement types to the synthesizer doesn't
interfere with the rest of the process. We define the following right and
left rule, to synthesize or consume in synthesis a refinement type, where
$\textsc{getModel}(p)$ is a call to an SMT solver that returns a model of an
uninterpreted function that satisfies
$\forall_{a,b,\dots,n}\ h_{a} \Rightarrow h_{b} \Rightarrow \dots
\Rightarrow h_{n} \Rightarrow p$, where $n$ is the refinement type label
and $h_{n}$ its predicate, with $a,\dots,n$ standing for the label of every refinement type
in the propositional contexts;
and $\textsc{sat}(p_{a} \Rightarrow p_{b})$ is a call to an SMT solver that
determines universal satisfiability of the implication between predicates (the
left focused proposition subtypes the goal).
\begin{mathpar}
    \infer*[right=(refR)]
    { \textsc{getModel}(p) = M }
    {\Theta/\Theta';\Rho;\Gamma;\Delta/\Delta' \vdash M : \{a : A\ \vert\
    p\}\Uparrow }
    \and
    \infer*[right=(refL)]
    { \textsc{sat}(p_{a} \Rightarrow p_{b}) }
    {\Theta/\Theta';\Rho;\Gamma;\Delta/\Delta'; x{:}(\{a : A\ \vert\
    p_{a}\})\Downarrow\ \vdash x : \{b : A\ \vert\ p_{b}\} }
\end{mathpar}


\mypara{Fast path} To speed up the process and get a cleaner %and sometimes more correct
output, we add a rule that lets us ``skip some rules'' if left focused on a
$\bang$-ed proposition, and the goal is $\bang$-ed:
\begin{mathpar}
    \infer*[right=($\bang\Downarrow$L)]
    { \Theta/\Theta';\Rho;\Gamma;\Delta; x{:}A\Downarrow\ \vdash M : C}
    {\Theta/\Theta';\Rho;\Gamma;\Delta; x{:}\bang A\Downarrow\ \vdash M : \bang C}
\end{mathpar}

\section{Results}

In practice, linear types can enforce the correct handling of resources,
allowing us to, e.g., ensure a file handle is released exactly once, or provide
a safe interface to manipulate mutable arrays. This last example is used in
Linear Haskell~\cite{} -- they provide an implementation of |array :: Int ->
[(Int,a)] -> Array a| using mutable arrays through the functions:
%
\begin{code}
newMArray :: Int -> (MArray a ⊸ Ur b) ⊸ b
write :: MArray a ⊸ (Int,a) -> MArray a
read :: MArray a ⊸ Int -> (MArray a, Ur b)
freeze :: MArray a ⊸ Ur (Array a)
\end{code}
%
This doubles as the flagship example of our synthesis framework and illustrates
the preciseness of linear types -- we're able to synthesize the exact
implementation given in Linear Haskell from the above function signatures and
the |array| type goal in a hundred miliseconds:
\begin{code}
array size pairs = newMArray size (\ma -> freeze (foldl write ma pairs))
\end{code}

\bibliographystyle{splncs04}
\bibliography{references}

\end{document}

