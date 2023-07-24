\documentclass[runningheads]{llncs}

\usepackage[dvipsnames]{xcolor}
\usepackage{xcolor}
\usepackage{todonotes}
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
Type-driven program synthesis is concerned with automatic generation of programs that
satisfy a given specification, formulated as a type. One of the key challenges of program
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
techniques for Linear Logic to efficiently find type-correct programs.

We implement the synthesis framework both as a standalone language which
supports classical linear types extended with recursive algebraic data types,
parametric polymorphism and basic refinements; and as a GHC type-hole plugin
that synthesises expressions for Haskell program holes, using the recently
introduced linear types feature -- showing it can generate precise solutions,
% faster than existing alternatives.
remarkably fast.

% Linear types allow programmers to give more precise and expressive
% specifications of their programs in the form of type signatures.

% Linear types add expressiveness to existing type systems by requiring that
% linear resources be used exactly once. Linear types are becoming part of more
% mainstream languages, such as Haskell, allowing programmers to enforce complex
% resource management policies at the type level
\end{abstract}

\keywords{
program synthesis,
linear logic,
propositions-as-types,
proof theory
}

\

\section{Introduction}

Program synthesis is the automated or semi-automated process of deriving a
program, i.e.~generating code, from some (high-level) specification. Synthesis can be
seen as a means to improve programmer productivity and program correctness
(e.g. through suggestion and autocompletion).
%
Specifications can take many forms such as natural
language~\cite{chen2021evaluating}, examples~\cite{DBLP:conf/popl/FrankleOWZ16}
or rich types such as polymorphic refinement
types~\cite{DBLP:conf/pldi/PolikarpovaKS16} or graded
types~\cite{DBLP:conf/lopstr/HughesO20}. Regardless of the specification form,
program synthesis must address two main sources of complexity --
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
extremely imprecise. On the other hand, the refinement type $(x{:}\mathsf{Int})
\rightarrow (y{:}\mathsf{Int}) \rightarrow \{z{:}\mathsf{Int} \mid z = x+y\}$
precisely specifies a function that adds its two arguments.

% The focus of our work is type-driven synthesis where specifications take the
% form of \emph{linear types}.
%
Linear types are another form of rich types that constrains resource usage in
programs by \emph{statically} limiting the number of times certain resources
can be used during their lifetime; in particular, linear resources must be used
\emph{exactly once}. Linearity allows us to concisely describe interesting
functions, since we can easily specify which arguments must be used
exactly once in
the body of a function. For example, the type of the linear map
function (using Haskell syntax),
|map :: (a ⊸ b) -> [a] ⊸ [b]|, specifies a function that, given a
\emph{linear} function from |a| to |b|, must consume the list of |as| exactly once
to produce a list of |bs|, which can only be done by applying the function to
each element.
% 
A linearity-aware program synthesizer can take the |map| type
as a specification to unambiguously produce:
% \vspace{-0.5cm}
\begin{code}
map f ls = case ls of
  [] -> []
  (x:xs) -> f x:map f xs
\end{code}
% \vspace{-0.5cm}
% whereas a non-linear synthesizer instantiation of the unrestricted |map| goal.
Another example is the more challenging |array :: Int -> [(Int,a)] -> Array a|
goal taken from Linear Haskell~\cite{Bernardy_2018}, which is implemented in terms
of a linear interface to mutable arrays. Remarkably, that linear interface is
also precise enough that our framework is capable of synthesizing the correct
implementation (\S~\ref{sec:evaluation}).

However, it is not at all obvious how to automate such a synthesis
procedure in a general setting where functions can make use of
recursion, algebraic data types and pattern matching. 
%
For instance, any naive approach that simply iterates over all
possible programs (of which there are infinitely many) and checks them against the given specification
(i.e.,~type-checking) would be very unlikely to find a function that
matches the user intent in a reasonable time frame. 

% TODO: Bad
% They can be applied to resource-aware programming such as concurrent programming
% (e.g. session types for message passing
% concurrency~\cite{DBLP:journals/mscs/CairesPT16}), memory-management
% (e.g.~Rust's ownership types), safely updating-in-place mutable
% structures~\cite{Bernardy_2018}, enforcing protocols for external \textsc{api}s~\cite{Bernardy_2018}, to name a few.

%\mypara{Contributions}
Synthesis with linear types, combined with other advanced typing features, has
generally been overlooked in the literature, despite their long-known potential
\cite{Wadler90lineartypes,DBLP:journals/mscs/CairesPT16,Bernardy_2018} and
strong proof-theoretic foundations
\cite{10.1093/logcom/2.3.297,DBLP:conf/cade/ChaudhuriP05,DBLP:journals/tcs/CervesatoHP00}.
%
One aspect that makes linear types particularly appealing from the
point of view of program synthesis is how linearity 
can affect the search space of valid programs: all programs where a linear resource is used
non-linearly (i.e. not exactly once)
are ill-typed and can be discarded. With linearity built into the synthesis process, usage of a
linear variable more than once is not considered, and unused variables
are identified during synthesis, constraining the space of valid programs.
%

In this work we explore type-based synthesis of
functional programs using linear types under the lens of the
Curry-Howard correspondence. Notably, we employ techniques from
linear logic \emph{proof search} as a 
mechanism for program synthesis, leveraging the proofs-as-programs
connection between linearly
typed functional programs and linear logic proofs. 
%
Our contributions are as follows:
\begin{itemize}



\item We present a framework for synthesis of functional programs
(\S~\ref{sec:core}) from specifications based on linear
types, leveraging established proof-search techniques for linear logic
under the lens of the Curry-Howard isomorphism.
Specifically, the core of the synthesis procedure
is a \emph{sound} and \emph{complete} system consisting of \emph{bottom-up}
proof-search in propositional linear logic, using a technique called \emph{focusing}~\cite{10.1093/logcom/2.3.297}. Our
approach, being grounded in propositions-as-types, ensures that all synthesized
programs (i.e.~proofs) are well-typed \emph{by construction} (i.e.~if the
synthesis procedure produces a program, then the program intrinsically
satisfies its specification).

\item  We extend the core synthesis framework and language
with algebraic data types, recursive functions, parametric polymorphism and
type refinements. These extra-logical extensions require us to abandon
completeness and to develop techniques to effectively explore the
search space in the presence of recursion (\S~\ref{sec:extension}).

%\item We argue that linear types are suitable specifications for synthesis both
%in their expressiveness and conciseness, by example.

% If we remove the footnote a part of the paragraph moves up
\item We present two implementations of our synthesis framework~\cite{ghc-linear-synthesis-plugin,slfl}, %\footnote{https://github.com/alt-romes/\{ghc-linear-synthesis-plugin,slfl\}},
one as a GHC plugin that synthesizes expressions for Linear
Haskell~\cite{Bernardy_2018} program holes, the other in a standalone language
with the same features the synthesis process supports, and benchmark them on
diverse synthesis goals (\S~\ref{sec:evaluation}).
% , |array :: Int -> [(Int,a)] -> Array a|.

% against similar synthesis that doesn't leverage linearity.

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


\section{Synthesis as Proof Search}\label{sec:core_synthesis}

The Curry-Howard correspondence~\cite{DBLP:journals/cacm/Wadler15}
describes the fundamental connection 
between logic and programming languages: propositions are types, and proofs are
programs. Under this lens, we can view \emph{bottom-up} proof-search
as \emph{program synthesis} -- starting from a goal proposition $A$,
finding a proof of $A$ \emph{is exactly} the process of generating a
program of type $A$.

Typically, the Curry-Howard correspondence is developed between so-called
systems of natural deduction and core functional languages such as
the $\lambda$-calculus, where logical rules have a direct, one-to-one,
mapping to typing rules.
%
However, even though proofs in natural deduction can be
interpreted as programs, a natural deduction proof system does not
directly describe an algorithm for proof search.
%
An example that highlights this is the \emph{modus ponens} rule from
intuitionistic logic (below on the left) and its analogous
\emph{function application} typing rule
from the simply-typed $\lambda$-calculus (below on the right):
%
\begin{mathpar}
\infer*[right=(mp)]
{\Gamma \vdash \alpha \rightarrow \beta \and \Gamma \vdash \alpha}
{\Gamma \vdash \beta}
\and
\infer*[right=($\rightarrow$\! E)]
{\Gamma \vdash M : \alpha \rightarrow \beta \and \Gamma \vdash N : \alpha}
{\Gamma \vdash M~N : \beta}
\end{mathpar}
%
If we interpret the rules \emph{bottom-up} we can see the modus ponens
rule as ``to find a
proof of $\beta$ under assumptions $\Gamma$, find a proof of $\alpha \rightarrow
\beta$ and a proof of $\alpha$ with the same assumptions, for some $\alpha$''. However, an
algorithm based on these rules would have to invent an
$\alpha$ for which the proof can be completed, with no obvious
relation between $\alpha$ and the goal $\beta$. In
essence, inference rules in natural deduction are ill-suited for bottom-up
proof-search since not all rules have an algorithmic bottom-up
reading.
%
A more suitable candidate for bottom-up proof search system is
the equivalent \emph{sequent calculus} in which all inference rules can
be naturally read in a bottom-up manner. The corresponding
implication elimination (or \emph{function application})
rule is instead:
%
\begin{mathpar}
  \infer*[right=($\rightarrow L$)]
  {\Gamma, f{:}\alpha\rightarrow\beta, x{:}\beta \vdash M : \tau \and \Gamma, f{:}\alpha\rightarrow\beta \vdash N : \alpha}
  {\Gamma, f{:}\alpha\rightarrow\beta \vdash M[f~N/x] : \tau}
\end{mathpar}
%
which can be understood \emph{bottom-up}, through the lens of synthesis
this time, as ``to synthesize an expression of type $\tau$ when
$f{:}\alpha\rightarrow\beta$ is in the context, synthesize an argument
$N$ of type $\alpha$, and an expression $M{:}\tau$ assuming $x{:}\beta$ in the context -- then
replace occurrences of $x$ by $f~N$ in $M$''.
%
Nevertheless, a sequent calculus is still not completely suited for
proof search due to non-determinism in selecting which rules to apply
(e.g.~if multiple function types are available in the context, which should we attempt to
use?).

Andreoli's focusing~\cite{10.1093/logcom/2.3.297} % for linear logic
is a technique that further disciplines (linear logic) proof-search by
reformulating the rules of the
sequent calculus. Focusing reduces the
non-determinism inherent to proof search by leveraging
the fact that the \emph{order} in which certain rules are applied does not affect the outcome
of the search, and by identifying the non-determinism in the search
process that pertains to true unknowns (i.e., rules whose application
modifies what can be subsequently proved) -- marking precisely the branches of the search
space that may need to be revisited (i.e.,~backtracked to).
%
A \emph{focused sequent calculus} can hence be effectively read
as a procedure for proof search for (a significant fragment of) linear logic that
turns out to be both \emph{sound} and \emph{complete} -- a sequent
is provable if and only if it is derivable in the focused
system.
% Following the Curry-Howard correspondence,
% Hence, through focusing, we can derive a procedure for program synthesis for the
% linear $\lambda$-calculus from type-based specifications,
% exploring the logical~\cite{DBLP:journals/tcs/Girard87} origins of linear types.
%

Our core synthesis framework thus comprises of a reading of
focused proof search in (intuitionistic) linear logic, where proofs
are seen as programs in a linearly-typed $\lambda$ calculus.
In linear logic, propositions are interpreted as resources that are
\emph{consumed} during the inference process. 
Where in standard propositional logic we are able to use an assumption as many
times as we want, in linear logic every resource (i.e., every assumption) must
be used \emph{exactly once}, or \emph{linearly}. In the remainder of
this work we will move interchangeably from linear propositions to
linear \emph{types}. As an example, consider the typing rules for the
linear function ($\lolli$), the linear counterpart to the standard function type;
linear product ($\tensor$), related to the standard product
type; and linear variables:
\begin{mathpar}
{\small
\infer[($\lolli$\! R)]
{\Delta, x{:}A \vdash M : B}
{ \Delta \vdash \lambda x. M : A\lolli B}
\and
\infer[($\tensor$ \! R)]
{\Delta_1 \vdash M : A \and \Delta_2 \vdash N : B}
{\Delta_1, \Delta_2 \vdash (M,N) : A \tensor B}
\and
\infer[(var)]
{ \, }
{x : A \vdash x : A}
}
\end{mathpar}
The rules define the judgment $\Delta \vdash M : A$, stating that term
$M$ has type $A$ using linear variables in $\Delta$. Rule {\sc
  ($\lolli$\! R)} explicates that to type a $\lambda$-abstraction
$\lambda x. M$ with type
$A\lolli B$, the body $M$ must use $x$ exactly once with type $A$ to
produce $B$. Note how the variable rule enforces the exact usage since
no other ambient variables are allowed. This is also observed in the
{\sc ($\tensor$ \! R)} rule, which states that to type the linear pair
$(M,N)$ with $A\tensor B$, the available resources must be split in
two regions ($\Delta_1$ and $\Delta_2$), one that is used in $M$ and
the other, disjointly, in $N$ (the logical rules can be obtained by
omitting the terms).
Unlike in standard propositional logic, where assumptions can be
weakened and contracted (i.e., discarded and duplicated) and so can
simply be maintained globally as they are introduced in a derivation,
in linear logic assumptions cannot be weakened or contracted and thus
a system of resource
management~\cite{DBLP:journals/tcs/CervesatoHP00,DBLP:journals/tcs/LiangM09}
is combined with focusing in order to algorithmically track linear
resource usage. 

% TODO: Acho que talvez faça mais sentido falar disto noutro sítio, está out-of-place
% Não estou a imaginar como começar a falar de linear types/logic
% Linear logic~\cite{DBLP:journals/tcs/Girard87} can be seen as a resource-aware logic, where propositions

% %
% % TODO Não gosto deste paragrafo em geral
% Linear types are analogous to linear logic connectives, through the
% Curry-Howard isomorphism. 
% %
% Note how we have a new context $\Delta$ threading the linear resources...

% \begin{itemize}
% \item Curry-Howard tens uma correspondencia um para um entre regras
%   logicas e regras tipos.
% \item Neste sentido, um programa pode ser visto como uma representacao
%   compacta de uma prova de uma proposicao logica.
% \item Portanto encontrar programas e o mesmo que encontrar provas.
% \item Tipicamente, a correspondencia CH desenvolve-se entre sistemas
%   logicos ditos de deducao natural ou calculo de sequentes e linguagens funcionais (calculo
%   lambda)
% \item bottom up!
% \item Contudo, um sistema de deducao natural nao descreve por si so um
%   algoritmo para proof search. Exemplo de porque e que e dificil em
%   geral.
% \item Calculos de sequentes sao um passo nessa direccao (subformula
%   property), mas mesmo assim ha muito nao determinismo.
% \item Literatura de ``proof search'' neste contexto passa por
%   focusing, que e uma reformulacao das regras logicas do calculo de
%   sequencia de forma a isolar o nao determinismo.
% \end{itemize}


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

We now present in detail the techniques that make up our synthesis
framework based on linear types.  We first introduce 
the core of the synthesizer (\S~\ref{sec:core}) which is a more or
less direct interpretation of focusing as proof search; which we
soundly extend (\S~\ref{sec:extension}) with extra-logical but
programming-centric features such as general recursion and abstract
data types (necessarily abandoning completeness).
%
We note that a \emph{sound} set of rules guarantees cannot synthesize
ill-typed programs; and that the valid programs derivable through them
reflect the subjective trade-offs we committed to in order to produce
an effective synthesizer.

\subsection{Core Language}\label{sec:core}

\mypara{Core Rules} The core language of our framework is
a simply-typed linear $\lambda$-calculus with linear functions ($\lolli$),
additive ($\with$) and multiplicative ($\tensor$) pairs (denoting alternative
and simultaneous occurrence of resources, respectively), multiplicative unit
(\textbf{1}), additive sums ($\oplus$) and the exponential modality ($\bang$),
which internalizes unrestricted use of variables. The syntax of terms $(M,N)$ and
types $(\tau, \sigma)$ is given below (we highlight the type for which
the terms in a given line form the introduction and elimination forms, respectively):
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
true, respectively. In a \emph{focused} sequent calculus
we further identify so-called invertible and
non-invertible inference rules. Andreoli~\cite{10.1093/logcom/2.3.297}
observed that the connectives of linear 
logic can be divided into two categories, dubbed synchronous and
asynchronous.
%
Asynchronous connectives are those whose right rules are
\emph{invertible}, i.e.
they can be applied eagerly during proof search without altering provability (and
so the order in which these rules are applied is irrelevant) and whose left
rules are not invertible. Synchronous connectives are dual. The asynchronous
connectives are $\lolli$ and $\with$ and the synchronous ones are
$\tensor,\textbf{1},\oplus,\bang$.

Given this separation, focusing divides proof search into two alternating
phases: %
the inversion phase, in which we apply \emph{all}
invertible rules eagerly, and the focusing phase, in
which we decide a proposition to \emph{focus} on, and then apply
non-invertible rules, staying \emph{in focus} until we reach an
asynchronous/invertible proposition, the proof is complete, or
no rules are applicable, in which case the proof must \emph{backtrack}
to the state at which the focusing phase began.
%
As such, with
focusing, the linear sequent calculus judgment 
$\Gamma; \Delta \vdash M : A$, meaning that $M:A$ is derivable from the linear
assumptions in $\Delta$ and non-linear assumptions in $\Gamma$,
is split into four judgments, grouped into the two phases.

For the invertible phase, a
context $\Omega$ holds propositions that result from
decomposing connectives.
% (propositions we'll later try to invert,
% moving them to the linear context ($\Delta$) when we fail to).
The right inversion and left inversion judgments are written
$\Gamma; \Delta; \Omega \vdash M : A \Uparrow$ and $\Gamma; \Delta;
\Omega \Uparrow\ \vdash M : A$, where the $\Uparrow$
indicates the connective or context being inverted.
For the focusing phase (all non-invertible rules can apply), 
the proposition under focus can be the goal or 
one in $\Gamma$ or $\Delta$. The right focus judgment is written 
$\Gamma;\Delta \vdash M : A \Downarrow$ and the left focus judgment
$\Gamma;\Delta; B\Downarrow\ \vdash M: A$, where $\Downarrow$
indicates the proposition under focus.

As alluded in the previous section, to handle the context splitting required to prove subgoals, we augment the
judgments above using Hodas and Miller's resource management
technique~\cite{DBLP:journals/tcs/CervesatoHP00,DBLP:journals/tcs/LiangM09}
where a pair of
input/output linear contexts is used to propagate the yet unused linear
resources across subgoals; e.g. the left inversion judgment is written
$\Gamma; \Delta/\Delta'; \Omega \Uparrow\ \nolinebreak\vdash M : A$ where $\Delta$ is the input
linear context and $\Delta'$ is the output one. 


Combining linear logic (i.e., the linear lambda calculus through the Curry-Howard correspondence), resource
management, and focusing, we obtain the following core formal system\footnote{For
the sake of brevity, we've omitted some rules such as those for the additive
pair and disjunction.}
% \todo{The complete system can be found in Appendix~\ref{app:final_system}.}
(inspired by~\cite{DBLP:conf/cade/ChaudhuriP05,fpnotes}) -- in which the
rule $\lolli$R is read: to synthesize a program of type $A \lolli B$ while inverting
right (the $\Uparrow$ on the goal), with unrestricted context $\Gamma$, linear
context $\Delta$, and inversion context $\Omega$, assume $x{:}A$ in $\Omega$ to
synthesize a program $M$ of type $B$, and return $\lambda x. M$.
%
We begin with right invertible rules, which decompose the goal until
it becomes a synchronous proposition:
% (note the condition on rule ($\with R$) which forces both subterms to use the same linear variables):
%
\begin{mathpar}
{\small
    % -o R
    \infer*[right=($\lolli R$)]
    {\Gamma ; \Delta/\Delta' ; \Omega, x{:}A \vdash M : B \Uparrow \and x
    \notin \Delta'}
    {\Gamma ; \Delta/\Delta' ; \Omega \vdash \lambda x . M : A
    \lolli B \Uparrow}
}
%  \and
%{\small
%    % & R
%    \infer*[right=($\with R$)]
%    {\Gamma ; \Delta/ \Delta' ; \Omega \vdash M : A \Uparrow \and \Gamma ;
%    \Delta/ \Delta'' ; \Omega \vdash N : B \Uparrow \and \Delta' = \Delta''}
%    {\Gamma ; \Delta/\Delta' ; \Omega \vdash  (M \with N) : A
%    \with B \Uparrow}
%}
\end{mathpar}
%
When we reach a non-invertible proposition on the right, we start inverting the
$\Omega$ context. The rule to transition to inversion on the left is:
%
\begin{mathpar}
  {\small
    \infer*[right=($\Uparrow$R)]
    {\Gamma ; \Delta/ \Delta' ; \Omega \Uparrow\ \vdash M : C \and C\ \textrm{not
    right asynchronous}}
{\Gamma ; \Delta/\Delta' ; \Omega \vdash M : C \Uparrow}
}
\end{mathpar}
%
We then apply left invertible rules for asynchronous connectives, which
decompose asynchronous propositions in $\Omega$:
%
\[
  \begin{array}{c}

    \infer*[right=($\tensor L$)]
    {\Gamma ; \Delta/ \Delta' ; \Omega, y{:}A, z{:}B \Uparrow\ \vdash M : C
    \and y,z \notin \Delta'}
    {\Gamma ; \Delta/\Delta' ; \Omega, x{:}A \tensor B \Uparrow\ \vdash\
    \textrm{let}\ y \tensor z = x\ \textrm{in}\ M : C}\\[0.5em]
    %\infer*[right=($1 L$)]
    %{\Gamma ; \Delta/ \Delta' ; \Omega \Uparrow\ \vdash M : C}
    %{\Gamma ; \Delta/\Delta' ; \Omega, x{:}1 \Uparrow\ \vdash\ \textrm{let}\
    %\star =
    %x\ \textrm{in}\ M : C}\\[0.5em]
    %\mprset{flushleft}
    %\infer*[right=($\oplus L$)]
    %{
    %\Gamma ; \Delta/ \Delta' ; \Omega, y{:}A \Uparrow\ \vdash M : C \and
    %y \notin \Delta' \\
    %\Gamma ; \Delta/ \Delta'' ; \Omega, z{:}B \Uparrow\ \vdash N : C \\
    %z \notin \Delta'' \\
    %\Delta' = \Delta''
    %}
    %{\Gamma ; \Delta/\Delta' ; \Omega, x{:}A \oplus B \Uparrow\ \vdash\
    %\textrm{case}\ x\ \textrm{of}\ \textrm{inl}\ y \rightarrow M\ \mid\
    %\textrm{inr}\ z \rightarrow N : C}
    %\\[0.5em]
    \infer*[right=($\bang L$)]
    {\Gamma, y{:}A ; \Delta/ \Delta' ; \Omega \Uparrow\ \vdash M : C}
    {\Gamma ; \Delta/\Delta' ; \Omega, x{:}\bang A \Uparrow\ \vdash\
    \textrm{let}\ \bang y = x\ \textrm{in}\ M : C}
\end{array}
\]
%
When we find a synchronous (i.e. non-invertible) proposition in $\Omega$,
we simply move it to the linear context $\Delta$, and keep inverting on the left:
\begin{mathpar}
  {\small
    \infer*[right=($\Uparrow$L)]
    {\Gamma; \Delta, x:A/\Delta'; \Omega \Uparrow\ \vdash M : C \and A\ 
    \textrm{not left asynchronous}}
  {\Gamma; \Delta/\Delta'; \Omega, x:A \Uparrow\ \vdash M : C}
  }
\end{mathpar}
%
After inverting all the asynchronous propositions in $\Omega$ we reach a state
where there are no more propositions to invert ($\Gamma'; \Delta'; \cdot
\Uparrow\ \vdash C$). At this point, we want to \emph{focus} on a proposition.
The focus object will be: the proposition on the right (the
goal), a proposition from the linear $\Delta$ context, or a proposition from the
unrestricted $\Gamma$ context. For these options we have three \emph{decision}
rules:
%

\vspace{-0.5cm}
{\small\[
  \begin{array}{c}
    \infer*[right=(decideR)]
    {\Gamma; \Delta/\Delta' \vdash M: C \Downarrow \and C\ \textrm{not atomic}}
    {\Gamma; \Delta/\Delta';\cdot \Uparrow\ \vdash M: C}\\[0.5em]
    \infer*[right=(decideL)]
    {\Gamma; \Delta/\Delta' ; x:A \Downarrow\ \vdash M :C}
    {\Gamma; \Delta, x:A/\Delta';\cdot \Uparrow\ \vdash M: C}
\qquad
    \infer*[right=(decideL!)]
    {\Gamma, A; \Delta/\Delta' ; A \Downarrow\ \vdash M: C}
    {\Gamma, A; \Delta/\Delta';\cdot \Uparrow\ \vdash M: C}
  \end{array}
\]}

%
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

\vspace{-0.5cm}
\begin{mathpar}
  {\small
      \infer*[right=($\lolli L$)]
    {\Gamma; \Delta/\Delta'; y{:}B \Downarrow\ \vdash M : C \and \Gamma;
    \Delta'/\Delta''; \cdot \vdash N : A \Uparrow}
    {\Gamma; \Delta/\Delta''; x{:}A \lolli B \Downarrow\ \vdash M\{(x\,N)/y\} : C}}
%\and
%    \infer*[right=($\with L_1$)]
%    {\Gamma; \Delta/\Delta'; y{:}A \Downarrow\ \vdash M : C}
%    {\Gamma; \Delta/\Delta'; x{:}A \with B \Downarrow\ \vdash M\{(\textrm{fst}\ x)/y\} : C}
%\and
%    \infer*[right=($\with L_2$)]
%    {\Gamma; \Delta/\Delta'; y{:}B \Downarrow\ \vdash M : C}
%    {\Gamma; \Delta/\Delta'; x{:}A \with B \Downarrow\ \vdash
%      M\{(\textrm{snd}\ x)/y\} : C}
\and
   {\small \infer*[right=($\tensor R$)]
    {\Gamma; \Delta/\Delta' \vdash M : A \Downarrow \and \Gamma ; \Delta'/\Delta'' \vdash N
    : B \Downarrow}
    {\Gamma; \Delta/\Delta'' \vdash (M \tensor N) : A \tensor B \Downarrow}
\and
    \infer*[right=($1 R$)]
    { }
    {\Gamma; \Delta/\Delta \vdash \star : \textbf{1} \Downarrow}}
%\and
%    \infer*[right=($\oplus R_1$)]
%    {\Gamma; \Delta/\Delta' \vdash M : A \Downarrow}
%    {\Gamma; \Delta/\Delta' \vdash\ \textrm{inl}\ M : A \oplus B \Downarrow}
%\and
%    \infer*[right=($\oplus R_2$)]
%    {\Gamma; \Delta/\Delta' \vdash M : B \Downarrow}
%    {\Gamma; \Delta/\Delta' \vdash\ \textrm{inr}\ M : A \oplus B \Downarrow}
%\and
%    \infer*[right=($\bang R$)]
%    {\Gamma; \Delta/\Delta'; \cdot \vdash M : A \Uparrow \and \Delta = \Delta'}
%    {\Gamma; \Delta/\Delta \vdash \bang M : \bang A \Downarrow}
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
    {\Gamma; \Delta/\Delta'; \cdot \vdash M :A \Uparrow}
    {\Gamma; \Delta/\Delta' \vdash M :A \Downarrow}\\[0.5em]
    \infer*[right=($\Downarrow L$)]
    {\Gamma; \Delta/\Delta'; x:A \Uparrow\ \vdash M : C \and A\ \textrm{not atomic and not left synchronous}}
    {\Gamma; \Delta/\Delta'; x:A \Downarrow\ \vdash M : C}

\end{array}
\]
%
The rules presented above make the core of our synthesizer. As a proof
system, focusing is both sound and complete -- a sequent is provable
in the focused system if and only if it is provable in linear
logic. We note however, that proof search in full linear logic is
\emph{undecidable}~\cite{DBLP:conf/lics/LincolnSS95}.
% This is repeated, is it on purpose?

%%%%% Example Sec 2.1 %%%%%%%

To illustrate the core synthesis framework, consider the goal $A\tensor B
\lolli B\tensor A$. Starting focused on the goal, we can construct a derivation (i.e. a program) by identifying the
rules that are applicable at any given moment. If more than one rule is applicable,
we must make a non-determinisic choice, but focusing guarantees those choices
are only required for "true unknowns". A derivation for this goal can be
constructed by applying, from the bottom-up, $\lolli\!R,
\Uparrow\!R, \tensor L, \Uparrow\!L, \Uparrow\!L, \textsc{decideR},
\tensor R$, and then instantiating both the sub-goals $B$ and $A$ using
$\Downarrow\!R, \Uparrow\!R, \Uparrow\!L, \textsc{decideL}, \textsc{Init}$.
Note that many of these rules don't intrinsically change the proof, but are
necessary in the proof-search procedure to eliminate non-essential
non-determinism. The program corresponding to the proof is $\lambda x.~\llet{(a,b) = x}{(b,a)}$.
%
We leave writing the derivation as an exercise.

% \[
% \infer*[right=($\lolli R$)]
% {
%   \infer*[right=($\Uparrow R$)]
%   {
% ...
%     \infer*[right=($\tensor L,\Uparrow L, \Uparrow L,decideR$)]
%     {\cdot ; A,B ; \cdot \vdash B \tensor A \Uparrow}
%     {\cdot; \cdot; A\tensor B \Uparrow \vdash B\tensor A}
%   }
%   {\cdot; \cdot; A\tensor B \vdash B \tensor A}
% }
% {\cdot; \cdot; \cdot \vdash A\tensor B \lolli B\tensor A \Uparrow}
% \]

%%%%% End Example %%%%%%%%%%

% Next, we'll
% present new rules that align and build on top of these to synthesize recursive
% programs from more expressive (richer) types.

\section{Beyond Propositional Logic}\label{sec:extension}

By itself, the core synthesis process can only output simple non-recursive
programs.
In this section, we extend our framework to be able to synthesize more
interesting programs featuring general recursion over algebraic data
types (ADTs) and
polymorphism. The combination of these features diverges from the pure
logical interpretation of focusing since unguarded general recursion is unsound
from a logical perspective (and decomposing ADTs through pattern matching is
uncommon in proof theory).

In its simplest form, an algebraic data type (ADT) is a tagged sum of
any type (i.e. a named type that can be instantiated by one of many tags, or
constructors) that take some value of  a fixed type. In general,
since the tagged types can be products ($A \tensor B$), or the unit
($1$), constructors can have an arbitrary fixed number of parameters.
%
%In the \synname\
%language, the programmer can define custom ADTs; as an example, we show the
%definition of an ADT which holds zero, one, or two
%values of type $A$, using the syntax: |data Container = None 1 mid One A mid Two (A * A)|.
%
The grammar of our core calculus is extended as (where $C_n$ is a
constructor for values of some type $T$):
%
\[
\begin{array}{lclcclc}
    M,N & ::= & \dots\ \vert\ \emph{C}_n\ M\ \vert\ (\mathsf{case}\ M\ \mathsf{of}\ \dots\ \vert\ \emph{C}_n\ u \Rightarrow N)
    & \qquad\tau, \sigma & ::= & \dots\ \vert\ T \\
 %    $ADT$ & $\ ::=\ $ & (\textsf{data} $\langle\emph{name}\rangle$\ $=$\ $\emph{Cons}_1\ \tau$\
% $\vert$\ $\dots$\ $\vert$\ $\emph{Cons}_n\ \tau$) \\
\end{array}
\]
%
Algebraic data types are related to the ($\oplus$) type -- both are
forms of disjunction. There is a right rule for each constructor of the data
type, requiring only that a term is synthesized for the argument of the
constructor; and there is one left rule to deconstruct a value of ADT type in the
context by pattern matching, requiring a term of the same type to be
synthesized for each possible branch. Naively, one might consider the rules:
%
%The semantics of ADTs relate to those of the plus ($\oplus$) type -- both are
%additive disjunctions.  To construct a value of an ADT we must use one of its
%constructors, similar to the way $\oplus$ requires only proof of either the left
%or right type it consists of. Analogously, we can deconstruct a value of an ADT
%via pattern matching on its constructors, where all branches of the pattern
%match must have the same type -- akin to the left rule for the $\oplus$
%connective. In effect, the inference rules for a simple ADT are a generalized
%form of the $\oplus$ rules.  Therefore, there's one left rule for ADTs, and an
%arbitrary number of right rules, one for each constructor, where ADT $T$ and
%its constructors stand for any ADT defined as |data T = C1 X1 mid C2 X2 mid ... mid Cn Xn|:
%
\begin{mathpar}
  {\small
    \infer*[right=(adtR)]
    {\Gamma; \Delta/\Delta' \vdash M : X_n \Downarrow}
    {\Gamma; \Delta/\Delta' \vdash\ C_n \ M : T \Downarrow}}
\and
    {\small\mprset{flushleft}
    \infer*[right=(adtL)]
    {
        %\Gamma ; \Delta/ \Delta'_1 ; \Omega, y_1{:}X_1 \Uparrow\ \vdash M_1 : C
        %\and
        %y_1 \notin \Delta'_1
        %\\
        %\Gamma ; \Delta/ \Delta'_2 ; \Omega, y_2{:}X_2 \Uparrow\ \vdash M_2 : C
        %\\
        %y_2 \notin \Delta'_2
        %\\\\
        %\\ \dots
        %\\
        \overline{\Gamma ; \Delta/ \Delta'_n ; \Omega, y_n{:}X_n \Uparrow\ \vdash M_n : C}
        \\
        \overline{y_n \notin \Delta'_n}
        \\
        \Delta'_1 = \Delta'_2 = \dots = \Delta'_n
    }
    {\Gamma ; \Delta/\Delta'_1 ; \Omega, x{:}T \Uparrow\
    \vdash\ \textrm{case}\ x\ \textrm{of}\ \dots\ \mid\ C_n\ y_n
    \rightarrow M_n : C}}

\end{mathpar}

%
% repetition does not legitimize :p
%
%A more general formulation of ADTs says an ADT can be recursive (or
%"inductively defined"), meaning constructors can take as arguments
%values of the type they are defining. This change has
%a significant impact in the synthesis process. Take, for instance, the ADT
%defined as |data T = C1 T|, the synthesis goal
%$T \lolli C$, and part of its derivation:
However, for recursively defined data types, i.e. for constructors that take as
an argument a value of the type they construct, a direct application
of the rules above will not terminate.
%
Consider, for example, type $T$ and its sole constructor $C_1$. When
synthesizing a derivation for a goal $T \lolli D$, for some $D$, we could infinitely apply
\textsc{adtL}:
%

\vspace{-0.5cm}
{\small
\begin{mathpar}
    \infer*[right=($\Uparrow R$)]
    {
        \infer*[right=(adtL)]
        {
            \infer*[right=(adtL)]
            {\dots}
            {\Gamma; \Delta/\Delta'; \Omega, y{:}T \Uparrow\ \vdash \textrm{case}\ y\ 
            \textrm{of}\ C_1\ z \rightarrow \dots : D}
        }
        {\Gamma; \Delta/\Delta'; \Omega, x{:}T \Uparrow\ \vdash \textrm{case}\ x\ 
        \textrm{of}\ C_1\ y \rightarrow \dots : D}
    }
    {\Gamma; \Delta/\Delta'; \Omega, x{:}T \vdash \dots : D
    \Uparrow}
\end{mathpar}}
%
Symmetrically, the derivation for goal $T$ is also infinite, since we can apply
\textsc{adtR} infinitely, never closing the proof:

\vspace{-0.5cm}
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


To account for recursively defined types, we restrict their decomposition
when synthesizing branches of a case construct, and, symmetrically,
disallow construction of data types when trying to synthesize an argument for
their constructors.
%
%
To model this, we use two more contexts, $\Rho_C$ for constraints on construction
and $\Rho_D$ for constraints on deconstruction. Together, they hold a list of
data types that cannot be constructed or deconstructed at a given
point, respectively. For convenience, they are represented by a single $\Rho$ if
unused and all non-ADT rules trivially propagate these.
The ADT rules
account for recursion as follows, where $\Rho'_C = \Rho_C,T$ if $T$ is
recursive and $\Rho'_C = \Rho_C$ otherwise ($\Rho'_D$ is dual):
%
%TODO: ... we can actually instance ADTs that take no arguments even if they are restricted

\vspace{-0.5cm}
\begin{mathpar}
  {\small
    \infer*[right=(adtR)]
    {(\Rho_C'; \Rho_D) ; \Gamma; \Delta/\Delta' \vdash M : X_n \Downarrow \and
    T \notin \Rho_C}
    {(\Rho_C; \Rho_D);\Gamma; \Delta/\Delta' \vdash\ C_n \ M : T \Downarrow}}
\and
    \mprset{flushleft}
    {\small\infer[(adtL)]
    {
        \overline{(\Rho_C; \Rho'_D);\Gamma ; \Delta/ \Delta'_n ; \Omega, y_n{:}X_n \Uparrow\ \vdash M_n : C}
        \and
        %\\
        %(\Rho_C; \Rho'_D);\Gamma ; \Delta/ \Delta'_1 ; \Omega, y_1{:}X_1 \Uparrow\ \vdash M_1 : C
        %\and
        %y_1 \notin \Delta'_1
        %\\\\
        %\\ \dots
        %\\\\
        \overline{y_n \notin \Delta'_n}
        \and
        T \notin \Rho_D
        \and
        {\Delta'_1 = \dots = \Delta'_n}
    }
    {(\Rho_C; \Rho_D); \Gamma ; \Delta/\Delta'_1 ; \Omega, x{:}T \Uparrow\
    \vdash\ \textrm{case}\ x\ \textrm{of}\ \dots\ \mid\ C_n\ y_n
    \rightarrow M_n : C}}
\end{mathpar}
% where
% \begin{mathpar}
%     \Rho'_C = \textrm{\textbf{if}}\ T\ \textrm{is recursive \textbf{then}}\ \Rho_C,
%     T\ \textrm{\textbf{else}}\ \Rho_C

%     \Rho'_D = \textrm{likewise}
% \end{mathpar}

These modifications block the infinite derivations
described above. However, they also greatly limit the space of
derivable programs, leaving the synthesizer effectively unable to
synthesize from specifications with recursive types. To prevent this,
we add two rules to complement the restrictions on construction
and destruction of recursive types.
%
First, since we can't deconstruct some ADTs any further due to these constraints,
but must utilize all propositions linearly in some way, all propositions in $\Omega$ whose
deconstruction is restricted are to be moved to the linear context $\Delta$.
%
Second, without any additional rules, an ADT in the linear context
will loop back to the inversion context, jumping back and forth
between the two contexts; instead, when focusing on an ADT, we should
either instantiate the goal (provided they're the same type), or switch
to inversion if and only if its decomposition is \emph{not} restricted:
%
\begin{mathpar}

  {\small\infer*[right=(adt$\Uparrow$L)]
    {
        (\Rho_C; \Rho_D);\Gamma; \Delta, x{:}T/\Delta'; \Omega \Uparrow\ \vdash M : C
        \and
        T \in \Rho_D
    }
    {(\Rho_C; \Rho_D);\Gamma; \Delta/\Delta'; \Omega, x{:}T \Uparrow\ \vdash M : C}}
    \and
    % ROMES: This one is just equal to (INIT), no point in having a new one? Except that this one isn't atomic?.
    %\infer*[right=(adt-init)]
    %{  }
    %{\Rho; \Gamma; \Delta/\Delta'; x{:}T \Downarrow\ \vdash x : T}
    %\and
    {\small\infer*[right=(adt$\Downarrow$L)]
    {(\Rho_C; \Rho_D); \Gamma; \Delta/\Delta'; x{:}T \Uparrow\ \vdash M :
    T \and T \notin \Rho_D}
    {(\Rho_C; \Rho_D); \Gamma; \Delta/\Delta'; x{:}T \Downarrow\ \vdash M : T}}
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

To synthesize recursive functions, we can simply label the main goal
as $f$ and extend
the unrestricted context with the label $f$ of the appropriate type. That is, to synthesize a recursive function
of type $A \lolli B$ named \emph{f}, the
initial judgment can be written as
\begin{mathpar}
    \Gamma, f{:}A \lolli B; \Delta/\Delta'; \Omega \vdash M : A \lolli B \Uparrow
\end{mathpar}
and so all subderivations will have
($f{:}A \lolli B$) available in $\Gamma$.
% We can also trivially force recursion to be used by adding the name to the
% linear context as well.
%
However, we must restrict immediate uses of the recursive call since
otherwise every goal would have a trivial proof (a non-terminating
function that just calls itself), shadowing relevant solutions.
Instead, our framework allows the use of recursion only \emph{after} having
deconstructed a recursive ADT, satisfying the invariant: the
recursive call can only be used in \emph{recursive branches of
  ADT deconstruction}, i.e. the recursive call should only take
``smaller'' terms as arguments.
%
%To illustrate, in any
%recursive function with a list argument (whose type is defined as
%|data List = Nil mid Cons (A * List)|), recursive
%calls are only allowed when considering a judgment of the form
%$\textrm {List} \vdash C$, i.e.~when a list value is available to
%produce the goal $C$, and only in the \emph{Cons}
%branch.
%
We also forbid further recursive calls when
synthesizing arguments for the recursive call itself.
% TODO : não sei se precisa de melhor explicação mas foi uma coisa que fiz para
% não gerar um programa recursivo.
% (TODO: rewrite? O bold é meio estranho não?)


\mypara{Polymorphism} A polymorphic type, or a type \emph{scheme}, is of the form
$\forall \overline{\alpha}.\ \tau$ where $\overline{\alpha}$ is a set of
variables that stand for (non-polymorphic) types in $\tau$.

Synthesis for a scheme comprises of effectively removing the quantification,
and then treating its type variables uniformly.  First,
type variables are considered \emph{atomic types}, then, we instantiate the
bound variables of the scheme as described by the Hindley-Milner~\cite{DBLP:journals/jcss/Milner78,10.2307/1995158}
type instantiation rule (put simply, generate fresh names 
for each bound type variable); e.g. the scheme $\forall \alpha.\ \alpha \lolli
\alpha$ could be instantiated to $\alpha_0 \lolli \alpha_0$, for some
fresh $\alpha_0$. We add such a rule to our system, where $\forall \overline{\alpha}.\ \tau \sqsubseteq \tau'$ indicates type
$\tau'$ is an \emph{instantiation} of type scheme $\forall \overline{\alpha}.\
\tau$:
%
\begin{mathpar}
    \infer*[right=($\forall R$)]
    { \Rho; \Gamma; \Delta/\Delta'; \Omega \vdash M: \tau' \Uparrow \and \forall
    \overline{\alpha}.\ \tau
    \sqsubseteq \tau'}
    {\Rho; \Gamma; \Delta/\Delta'; \Omega \vdash M : \forall \overline{\alpha}.\
    \tau \Uparrow}
\end{mathpar}
%
As such, the construction of a derivation in which the only rule that can derive
an atom is the \textsc{init} rule corresponds to the synthesis of a program
where some expressions are treated agnostically,
i.e.~a polymorphic program.
%
% TODO Cut?
%The simplest example is the polymorphic function
%\emph{id} of type $\forall \alpha .\ \alpha \lolli \alpha$. The program
%synthesized from that specification is $\lambda x . x$, a lambda abstraction
%that does not constrain the type of its parameter $x$ in any way.

The main challenge of polymorphism in synthesis is the usage of schemes from the
unrestricted context.  The context $\Gamma$ now holds both (monomorphic)
types and schemes. Consequently, after the rule \textsc{decideLeft!} is applied,
we are left-focused on either a type or a scheme. Since left focus on a type is
already well defined, we need only specify how to focus on a scheme.

%
Our algorithm instantiates bound type variables of the focused scheme with fresh
\emph{existential} type variables, and the instantiated type becomes the left
focus. Inspired by the Hindley-Milner system, we also generate inference
constraints on the existential type variables (postponing the decision of what
type it should be to be used in the proof), and collect them in a new
constraints context $\Theta$ that is propagated across derivation branches (by having an input and output context
($\Theta/\Theta'$)).  In contrast to Hindley-Milner inference, new 
constraints are immediately solved against all other constraints -- a branch of
the search is desired to fail as soon as possible. 
%TODO: Como fazer? \todo{O que significa $?\alpha$ ? Não foi explicado -- no
%Hindley-Milner nao ha propriamente o problema de misturar variaveis
%existenciais com universais}
Note that we instantiate the scheme with \emph{existential} type variables
($?\alpha$) rather than type variables ($\alpha$) since the latter
represent universal types during synthesis, and the former represent a concrete
instance of a scheme, that might induce constraints on other type variables.
Additionally, we require that all existential type variables are eventually assigned a
concrete type. These concepts are formalized with the following rules, where $\forall
\overline{\alpha}.\ \tau \sqsubseteq_E \tau'$ means type $\tau'$
is an \emph{existential instantiation} of scheme $\forall \overline{\alpha}.\ \tau$,
$\textrm{ftv}_E(\tau')$ is the set of free \emph{existential} type variables in
type $\tau'$, $?\alpha \mapsto \tau_x$ is a mapping from \emph{existential} type
$?\alpha$ to type $\tau_x$, and $\textsc{unify}(c, \Theta)$ indicates whether
constraint $c$ can be unified with those in $\Theta$:

\vspace{-0.5cm}
\begin{mathpar}
    {\scriptsize\infer*[right=($\forall L$)]
    {
        \Theta/\Theta'; \Rho; \Gamma; \Delta/\Delta'; \tau' \Downarrow\ \vdash M: C
        \\
        \forall \overline{\alpha}.\ \tau \sqsubseteq_E \tau'
        \\
        \textrm{ftv}_E(\tau') \cap \{ ?\alpha\ \vert\ (?\alpha \mapsto \tau_x) \in \Theta'\} = \emptyset
    }
    {\Theta/\Theta'; \Rho; \Gamma; \Delta/\Delta'; \forall \overline{\alpha}.\ \tau \Downarrow\ \vdash M: C}}
    \and
    {\scriptsize\infer*[right=($?L$)]
    {\textsc{unify}(?\alpha
    \mapsto C, \Theta)}
    {\Theta/\Theta, ?\alpha \mapsto C ; \Rho; \Gamma; \Delta/\Delta';
    x{:}?\alpha \Downarrow\ \vdash x : C}
    \and
    \infer*[right=($\Downarrow ?L$)]
    {\textsc{unify}(?\alpha
    \mapsto A, \Theta)}
    {\Theta/\Theta, ?\alpha \mapsto A ; \Rho; \Gamma; \Delta/\Delta';
    x{:}A \Downarrow\ \vdash x : ?\alpha}}
\end{mathpar}


% ROMES: NOTE: Leave it be, its details. Fits in the appendice
% TODO: We could add to the appendice all these extra rules for better synthesis, including refinements.
%
%\mypara{Further Challenges} We now consider two more sources of infinite
%recursion in the synthesis process. The first is the use of an unrestricted
%function to synthesize a term of type $\tau$ that in turn will require a term of
%the same type $\tau$. An example is the sub-goal judgment $(a \lolli
%b \lolli b); (a \lolli b \lolli b) \Downarrow\ \vdash b$ that
%appears while synthesizing \emph{foldr} -- we apply ($\lolli$L)
%until we can use \textsc{init} ($b \Downarrow\ \vdash b$), and then we must
%synthesize an argument of type $b$. Without any additional restrictions, we
%may become again left focused on $(a \lolli b \lolli b)$, and again require $b$,
%and on and on. The solution will be to disallow the usage of the same function
%to synthesize the same goal a second time further down in the derivation.
%
%The other situation occurs when using an unrestricted polymorphic function that
%requires synthesis of a term with an existential type when the goal is an
%existential type. In contrast to the previous problem, the type of the goal and
%of the argument that will cause the loop won't match exactly, since instantiated
%bound variables are always fresh. For example, for $\forall \alpha,\beta .\
%\alpha\lolli\beta\lolli\beta;?\alpha\lolli?\beta\lolli?\beta \Downarrow\ \vdash\
%?\sigma$, we'll unify $?\beta$ with $?\sigma$, and then require a term of type
%$?\beta$ (not $?\sigma$). We want to forbid the usage of the \emph{same}
%function to attain \emph{any} existential goal, provided that function might
%create existential sub-goals (i.e. it's polymorphic). However, we noticed that,
%even though for most tried problems this ``same function'' approach worked,
%context-heavy problems such as \emph{array} (seen in \S~\ref{sec:overview})
%wouldn't terminate in a reasonable amount of time.
%%
%% In fact, with $n$ polymorphic functions in the unrestricted context, the
%% complexity of searching for a program of any existential type $?\alpha$, while
%% restricting solely the used function, is $O(n!)$~\ref{exemplo_apendice?}.
%%
%As such, we'll instead define that, given an existential\footnote{a type 
%is existential when any of its components is an existential type variable} goal $C$,
%we can only ``decide left!'' on a proposition $A$ if, altogether, 
%the amount of times we've ``decided left!'' on an polymorphic function to produce
%an existential goal is less than a \emph{constant ``existential depth''} $d_e$
%(which controls a \emph{depth} aspect of the synthesis process).
%%
%% This approach reduces the complexity of our proof-search algorithm for
%% existential types to $O(\tfrac{n!}{d_e!}) = O(n^{d_e})$.
%
%Extending the restrictions context ($\Rho$) with restrictions on using the
%unrestricted context ($\Rho_{L!}$), we modify \textsc{decideLeft!} to formalize
%the two previous paragraphs, where $\textsc{isExist}(C)$ is true if $C$ is an
%existential type, $\textsc{isPoly}(f)$ is true if $f$ is universally
%quantified (i.e. $f$ has form $\forall\overline{\alpha} f'$), and
%$\Rho_{L!}' = \Rho_{L!},(A, C)$ if $A$ is a function and $\Rho_{L!}' =
%\Rho_{L!}$ otherwise:
%%
%\begin{mathpar}
%    \mprset{flushleft}
%    \infer*[right=(decideL!)]
%    {
%    (A, C) \notin \Rho_{L!}
%    \\
%    \textsc{isExist}(C) \Rightarrow \bararound{\{u\ \mid\ (f,u)\in\Rho_{L!},\textsc{isPoly}(f),\textsc{isExist}(u)\}} < d_e
%    \\
%    \Theta/\Theta';(\Rho_C,\Rho_D,\Rho_{L!}');\Gamma, A; \Delta/\Delta' ; A
%    \Downarrow\ \vdash C
%    }
%    {\Theta/\Theta';(\Rho_C,\Rho_D,\Rho_{L!});\Gamma, A; \Delta/\Delta';\cdot \Uparrow\ \vdash C}
%    \\
%\end{mathpar}
%
%\mypara{Polymorphic ADTs} To allow type parameters and the use of universally quantified type
%variables in ADT constructors, we must guarantee that the
%\textsc{adt-init} rule can unify the type parameters and that when constructing or
%destructing an ADT, type variables in constructor parameters are substituted by
%the actual type (i.e. to construct |List Int| with
%|data List a = Cons (a * List a)|, we wouldn't try to synthesize |(a * List a)|,
%but rather |(Int * List Int)|). To unify $T_{\overline\alpha}$ with $T_{\overline\beta}$,
%the sets of type parameters $\overline\alpha$ and $\overline\beta$ must satisfy $\bararound{\overline\alpha} = \bararound{\overline\beta}$
%together with $\forall i\ 0 \leq i \land i < \bararound{\overline\alpha} \land
%\textsc{unify}(\overline\alpha_i \mapsto \overline\beta_i)$. The constructor
%type substitution needn't be explicit in the rule:
%\begin{mathpar}
%    \infer*[right=(adt-init)]
%    {\textsc{unify}(T_{\overline\alpha} \mapsto T_{\overline\beta}, \Theta)}
%    {\Theta/\Theta,T_{\overline\alpha} \mapsto T_{\overline\beta},\Rho; \Gamma; \Delta/\Delta'; x{:}T_{\overline\alpha} \Downarrow\ \vdash x :
%    T_{\overline\beta}}
%\end{mathpar}

%\mypara{Refinement Types} Refinement types are types with a predicate (a non-existing predicate is the same as it
%being \emph{true}); dependent types are functions with
%refinement types in which the argument type is labeled and said label can be used in the predicates
%of the return type (e.g. $(x : \mathsf{Int}) \lolli \{y : \mathsf{Int}\ \vert\ y = x\}$ specifies a function that
%takes an Int and returns an Int of equal value). We extend
%the types syntax with our refinement types:
%\[
%\begin{tabular}{lclc}
%    $\tau$ & $\ ::=\ $ & $ \dots \vert\  (x:\tau) \lolli \sigma\ \vert\  \{x:\tau\ \vert\ P\}$ \\
%    $P$ & $\ ::=\ $ & $P = P\ \vert\ P \neq P\ \vert\ P \vee P\ \vert\ P \wedge
%    P\ \vert\ P \Rightarrow P\ \vert\ n = n\ \vert\ n \neq n$ \\
%    & & $\vert\ n \leq n\ \vert\ n \geq n\ \vert\ n < n\ \vert\ n > n\ \vert\
%    true\ \vert\ false\ \vert\ x$ \\
%    $n$ & $\ ::=\ $ & $n * n\ \vert\ n + n\ \vert\ n - n\ \vert\
%    \langle\emph{natural}\rangle\ \vert\ x$
%    \\
%\end{tabular}
%\]
%The addition of refinement types to the synthesizer doesn't
%interfere with the rest of the process. We define the following right and
%left rule, to synthesize or consume in synthesis a refinement type, where
%$\textsc{getModel}(p)$ is a call to an SMT solver that returns a model of an
%uninterpreted function that satisfies
%$\forall_{a,b,\dots,n}\ h_{a} \Rightarrow h_{b} \Rightarrow \dots
%\Rightarrow h_{n} \Rightarrow p$, where $n$ is the refinement type label
%and $h_{n}$ its predicate, with $a,\dots,n$ standing for the label of every refinement type
%in the propositional contexts;
%and $\textsc{sat}(p_{a} \Rightarrow p_{b})$ is a call to an SMT solver that
%determines universal satisfiability of the implication between predicates (the
%left focused proposition subtypes the goal).
%\begin{mathpar}
%    \infer*[right=(refR)]
%    { \textsc{getModel}(p) = M }
%    {\Theta/\Theta';\Rho;\Gamma;\Delta/\Delta' \vdash M : \{a : A\ \vert\
%    p\}\Uparrow }
%    \and
%    \infer*[right=(refL)]
%    { \textsc{sat}(p_{a} \Rightarrow p_{b}) }
%    {\Theta/\Theta';\Rho;\Gamma;\Delta/\Delta'; x{:}(\{a : A\ \vert\
%    p_{a}\})\Downarrow\ \vdash x : \{b : A\ \vert\ p_{b}\} }
%\end{mathpar}
%
%
%\mypara{Fast path} To speed up the process and get a cleaner %and sometimes more correct
%output, we add a rule that lets us ``skip some rules'' if left focused on a
%$\bang$-ed proposition, and the goal is $\bang$-ed:
%\begin{mathpar}
%    \infer*[right=($\bang\Downarrow$L)]
%    { \Theta/\Theta';\Rho;\Gamma;\Delta; x{:}A\Downarrow\ \vdash M : C}
%    {\Theta/\Theta';\Rho;\Gamma;\Delta; x{:}\bang A\Downarrow\ \vdash M : \bang C}
%\end{mathpar}

\section{Evaluation}\label{sec:evaluation}

We implemented our framework both as a Haskell GHC plugin and as
a standalone synthesizer that can typecheck Haskell-like programs with ``goal
signatures'' for which valid expressions are synthesized. We've tested and
benchmarked both implementations on numerous synthesis challenges with
successful results.
% (see Appendix~\ref{app:examples} for an extended list of examples).
Among the more intricate examples, we can easily
synthesize the |Monad| instances of |Maybe| and |State|. However, the more interesting
result is a real-world example from \cite{Bernardy_2018}:
%
with linear types one can provide a safe interface to manipulate mutable arrays.
Linear Haskell~\cite{Bernardy_2018}  provides an implementation of |array :: Int ->
[(Int,a)] -> Array a| which, internally, uses mutable arrays via the interface:
%

%\vspace{-0.5cm}
{\small
\begin{code}
newMArray :: Int -> (MArray a ⊸ Ur b) ⊸ b
write :: MArray a ⊸ (Int,a) -> MArray a
read :: MArray a ⊸ Int -> (MArray a, Ur b)
freeze :: MArray a ⊸ Ur (Array a)
\end{code}}
%
The flagship result from our synthesis framework, which also illustrates the
preciseness of linear types, is that we're able to synthesize the exact
implementation of |array| given in Linear Haskell given the above interface and
the |array| type goal, all in a hundred milliseconds:
%
%\vspace{-0.5cm}
\begin{code}
array size pairs = newMArray size (\ma -> freeze (foldl write ma pairs))
\end{code}
The standalone implementation further supports (experimentally) refinement
types and additional synth guidelines. Figure~\ref{fig:benchmarks}
lists benchmarks for a suite of examples. The Goal column describes
the type of the synthesized term using typical Haskell
terminology. The Keywords column denotes the use of additional
synthesis guidance features that we implemented in our synthesizer:
the \emph{choose} keyword instructs the synthesizer to stop after one
valid term is found, the equality clause in the list reverse function
serves as an input output example that guides the search, the
\emph{depth} keyword controls the instantiation depth of
quantifiers. The Components column describes the library of function
(signatures) provided for the particular synthesis goal.

\begin{figure}
{\scriptsize
\begin{center}
    \begin{tabular}{ccccc}
        \hline
        Group & Goal & Avg. time $\pm\,\sigma$ & Keywords & Components \\
        \hline
        \multirow{4}{4em}{Linear Logic} & uncurry & $133\mu s\pm 4.9\mu s$ &&\\ 
        %& distributivity & $179\mu s\pm 5.0\mu s$ && \\ 
        & call by name & $196\mu s\pm 4.6\mu s$ && \\ 
        & 0/1 & $294\mu s\pm 5.3\mu s$ && \\ 
        \hline
        \multirow{7}{4em}{List} & map & $288\mu s\pm 7.2\mu s$  && \\ 
        & append & $292\mu s\pm 7.0\mu s$ & & \\ 
        & foldl & $1.69ms\pm 5.3\mu s$ & \emph{choose 1} & \\ 
        & foldr & $704\mu s\pm 10\mu s$ && \\ 
        & concat & $505\mu s\pm 18\mu s$ && \\
        %& uncons & $215\mu s\pm 15\mu s$ && \\
        & reverse & $17.4ms\pm 515\mu s$ & \emph{reverse [1,2] == [2,1]} & \\ 
        \hline
        \multirow{2}{4em}{Maybe} & $>>=$ & $194\mu s\pm 5.3\mu s$ && \\ 
        & maybe & $161\mu s\pm 4.8\mu s$&& \\
        \hline
        \multirow{7}{4em}{State} & runState & $190\mu s\pm 6.8\mu s$ && \\ 
        & $>>=$ & $979\mu s\pm 23\mu s$ && \\
        & $>>=$ & $\infty$ & \emph{using (runState)} & \\
        & get & $133\mu s\pm 3.8\mu s$ && \\
        & put & $146\mu s\pm 3.4\mu s$ && \\
        & modify & $219\mu s\pm 4.9\mu s$ && \\
        & evalState & $156\mu s\pm 4.0\mu s$ && \\
        % \multirow{5}{4em}{Binary Tree} & singleton & 1s & yes & yes \\ 
        % & insert & 1s & yes & unordered \\
        % & map & 1s & yes & yes \\
        % & append & 1s & yes & appends to rightmost leaf \\
        % & join node & 1s & yes & joins at rightmost leaf \\
        % \hline
        % \multirow{7}{4em}{Map} & singleton & 1s & yes & yes \\ 
        % & insert & 1s & yes & unordered \\
        % & insertWithKey & 1s & yes & ignores function \\
        % & union & 1s & yes & ignores keys \\
        % & mapAccum & 1s & no & ?? \\
        % & map & 1s & yes & yes \\
        % & mapKeys & 1s & yes & yes \\
        \hline
        Misc & either & $197\mu s\pm 5.3\mu s$ && \\ 
        \hline
        \multirow{2}{4em}{Array} & & & \emph{depth 3} & \emph{freeze, foldl} \\
        & array~\ref{sec:evaluation} & $80ms\pm 870\mu s$ & \emph{using (foldl),depth 3} & \emph{newMArray,write} \\
        \hline
        Refinements & add3 & $39ms\pm 1.1ms$ & & + \\
        \hline
    \end{tabular}
  \end{center}
}
\vspace{-0.5cm}
\caption{Benchmarks\label{fig:benchmarks}}
\end{figure}

\section{Related Work}\label{sec:related}

Type-based program synthesis is a vast field of study. Most
works~\cite{DBLP:conf/lopstr/HughesO20,DBLP:conf/pldi/PolikarpovaKS16,DBLP:conf/pldi/OseraZ15,DBLP:conf/popl/FrankleOWZ16}
follow some variation of the synthesis-as-proof-search approach. Focusing
in synthesis appeared first in the literature in~\cite{10.1145/3408991}.
%
Each synthesis framework differ due to a variety of rich
types explored and their corresponding logics and languages.
% ; or nuances of the synthesis process itself.
% , such as complementing types with program examples;
%or even the programming paradigm of the output produced (e.g. generating heap
%manipulating programs~\cite{DBLP:journals/pacmpl/PolikarpovaS19}).
%
% Some other common
% patterns we follow are the use of type
% refinements~\cite{DBLP:conf/pldi/PolikarpovaKS16}, polymorphic types, and the
% support for synthesis of recursive
% functions~\cite{DBLP:conf/pldi/PolikarpovaKS16,DBLP:conf/pldi/OseraZ15}. These
% works share some common ground with each other and with us -- most
% famously the Curry-Howard correspondence, but also, for example, 
% focusing-based proof-search~\cite{10.1093/logcom/2.3.297}.

% \mypara{Type-and-Example-Directed Program Synthesis} This
% work~\cite{DBLP:conf/pldi/OseraZ15,DBLP:conf/popl/FrankleOWZ16}
% explores a purely functional, recursive program synthesis technique
% based on types/proof search (as we intend to do), with examples as an
% auxiliar technique to trim down the program synthesis vast search
% space. A good use is
% made of the general strategy of using a type system to generate
% programs (by ``inverting'' the type system), rather than using it to
% type-check one.  Moreover, the paper uses a data structure called
% ``refinement tree'' in conjunction with the extra information provided
% by the examples to allow for efficient synthesis of non-trivial
% programs. Overall it employs good engineering to achieve type-based
% synthesis of functional typed programs, with at least two additions
% that we might want to follow too (type refinements and recursive
% functions).

% or how to turn your type system upside down ~ não apagar a Kubrick reference? :)
  
% \mypara{Program Synthesis from Polymorphic Refinement Types}
The
work~\cite{DBLP:conf/pldi/PolikarpovaKS16} also studies synthesis of recursive
functional programs in an ``advanced'' context. Their specifications combine two
rich forms of types: polymorphic and refinement types.
% (which correspond to a
% first-order logic through the Curry-Howard isomorphism).
%
% Their approach to
% refinement types consists of an algorithm that supports decomposition of the
% refinement specification.
%
%,allowing for separation between the language of
%specification and programs and making the approach amenable to compositional
%synthesis techniques.
We also support refinements (and polymorphism),
but they are not as integrated in the synthesis process as in \cite{DBLP:conf/pldi/PolikarpovaKS16}.
Instead, our synthesizer leverages the expressiveness of linear
types and techniques for proof-search in linear logic to guide its process.

% \mypara{Resourceful Program Synthesis from Graded Linear Types}
The
work~\cite{DBLP:conf/lopstr/HughesO20} synthesizes programs using an
approach similar ours. It employs so-called graded
modal types, which are a refinement of pure linear types
% -- a more
% \emph{fine-grained} version 
that allows for a quantitative
specification of resource usage, in contrast to ours either
\emph{linear} or \emph{unrestricted} (via the linear logic
exponential) use of assumptions. Their resource management is thus more
complex than ours.
% -- which, in contrast, is the one used in our work.
%
They also use focusing as a solution to trim down search space and to
ensure that synthesis only produces well-typed programs. However, since their
underlying logic is \emph{modal} rather than purely \emph{linear}, it
lacks a clear correspondence with concurrent session-typed
programs~\cite{DBLP:journals/mscs/CairesPT16,DBLP:conf/concur/CairesP10},
which is a crucial avenue of future work. Moreover, their use of grading
effectively requires an SMT solver to be integrated with the
synthesis procedure, which can limit the effectiveness of the overall
approach.
% as one scales to more sophisticated settings (e.g.~refinement
% types).
Additionally, our system extends the focusing-based system with
recursion, ADTs, polymorphism and refinements to synthesize
more expressive programs.

\vspace{0.2cm}
\noindent
\textbf{Acknowledgements}
%
This work is supported by NOVA LINCS (UIDB/04516/2020) with the financial support of FCT.IP.

\bibliographystyle{splncs04}
\bibliography{references}

\end{document}

\appendix

\section{Formal System}~\label{app:final_system}

In this section we present the complete system specifying the synthesis process.

\mypara{Core Rules}

\begin{itemize}

\item Right invertible rules
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

\item Transition to left inversion

\begin{mathpar}
    \infer*[right=($\Uparrow$R)]
    {\Gamma ; \Delta/ \Delta' ; \Omega \Uparrow\ \vdash M: C \and C\ \textrm{not
    right asynchronous}}
    {\Gamma ; \Delta/\Delta' ; \Omega \vdash M: C \Uparrow}
\end{mathpar}

\item Left invertible rules, which decompose asynchronous propositions in $\Omega$
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
\item When a non-invertible proposition is in $\Omega$, move it to $\Delta$ and keep inverting on the left
\begin{mathpar}
    \infer*[right=($\Uparrow$L)]
    {\Gamma; \Delta, A/\Delta'; \Omega \Uparrow\ \vdash M: C \and A\ 
    \textrm{not left asynchronous}}
    {\Gamma; \Delta/\Delta'; \Omega, A \Uparrow\ \vdash M: C}
\end{mathpar}

\item Transition to focusing, since there are no more propositions in $\Omega$ (the decision rules)
\[
  \begin{array}{c}
    \infer*[right=(decideR)]
    {\Gamma; \Delta/\Delta' \vdash M: C \Downarrow \and C\ \textrm{not atomic}}
    {\Gamma; \Delta/\Delta';\cdot \Uparrow\ \vdash M: C}\\[0.5em]
    \infer*[right=(decideL)]
    {\Gamma; \Delta/\Delta' ; A \Downarrow\ \vdash M: C}
    {\Gamma; \Delta, A/\Delta';\cdot \Uparrow\ \vdash M: C}
\qquad
    \infer*[right=(decideL!)]
    {\Gamma, A; \Delta/\Delta' ; A \Downarrow\ \vdash M: C}
    {\Gamma, A; \Delta/\Delta';\cdot \Uparrow\ \vdash M: C}
  \end{array}
  \]
\item Rules that focus on a right or left proposition, chosen with the decision rules

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

\item When the focused proposition becomes asynchronous, we do one of
\[
\begin{array}{c}
    \infer*[right=(init)]
    {  }
    {\Gamma; \Delta/\Delta'; x{:}A \Downarrow\ \vdash x : A}
    \qquad
     \infer*[right=($\Downarrow R$)]
    {\Gamma; \Delta/\Delta'; \cdot \vdash M: A \Uparrow}
    {\Gamma; \Delta/\Delta' \vdash M: A \Downarrow}\\[0.5em]
    \infer*[right=($\Downarrow L$)]
    {\Gamma; \Delta/\Delta'; A \Uparrow\ \vdash M: C \and A\ \textrm{not atomic and not left synchronous}}
    {\Gamma; \Delta/\Delta'; A \Downarrow\ \vdash M: C}

\end{array}
\]
\end{itemize}

\mypara{Beyond propositional logic}

\begin{itemize}

\item To synthesize an algebraic data type
\begin{mathpar}
    \infer*[right=(adtR)]
    {(\Rho_C'; \Rho_D) ; \Gamma; \Delta/\Delta' \vdash M : X_n \Downarrow \and
    T \notin \Rho_C}
    {(\Rho_C; \Rho_D);\Gamma; \Delta/\Delta' \vdash\ C_n \ M : T \Downarrow}
\and
    \mprset{flushleft}
    \infer*[right=(adtL)]
    {
        \overline{(\Rho_C; \Rho'_D);\Gamma ; \Delta/ \Delta'_n ; \Omega, y_n{:}X_n \Uparrow\ \vdash M_n : C}
        \and
        \overline{y_n \notin \Delta'_n}
        \and
        T \notin \Rho_D
        \and
        {\Delta'_1 = \dots = \Delta'_n}
    }
    {(\Rho_C; \Rho_D); \Gamma ; \Delta/\Delta'_1 ; \Omega, x{:}T \Uparrow\
    \vdash\ \textrm{case}\ x\ \textrm{of}\ \dots\ \mid\ C_n\ y_n
    \rightarrow M_n : C}
\end{mathpar}
\item And the additional rules to unblock synthesis given the restrictions on algebraic data types

\begin{mathpar}
    \infer*[right=(adt$\Uparrow$L)]
    {
        (\Rho_C; \Rho_D);\Gamma; \Delta, x{:}T/\Delta'; \Omega \Uparrow\ \vdash M : C
        \and
        T \in \Rho_D
    }
    {(\Rho_C; \Rho_D);\Gamma; \Delta/\Delta'; \Omega, x{:}T \Uparrow\ \vdash M : C}
    \and
    \infer*[right=(adt$\Downarrow$L)]
    {(\Rho_C; \Rho_D); \Gamma; \Delta/\Delta'; x{:}T \Uparrow\ \vdash M :
    T \and T \notin \Rho_D}
    {(\Rho_C; \Rho_D); \Gamma; \Delta/\Delta'; x{:}T \Downarrow\ \vdash M : T}
\end{mathpar}
\item Note that if a left focused algebraic data type cannot be deconstructed
because of a restriction, it might still be instanced through \textsc{init}.
Specialized to ADTs, it would be:
\begin{mathpar}
    \infer*[right=(adt-init)]
    {  }
    {\Rho; \Gamma; \Delta/\Delta'; x{:}T \Downarrow\ \vdash x : T}
    \and
\end{mathpar}

\end{itemize}

\mypara{Polymorphism}

\begin{itemize}
\item Introducing and using schemes
\begin{mathpar}
    \infer*[right=($\forall R$)]
    { \Rho; \Gamma; \Delta/\Delta'; \Omega \vdash M: \tau' \Uparrow \and \forall
    \overline{\alpha}.\ \tau
    \sqsubseteq \tau'}
    {\Rho; \Gamma; \Delta/\Delta'; \Omega \vdash M: \forall \overline{\alpha}.\
    \tau \Uparrow}
  \and
    \infer*[right=($\forall L$)]
    {
        \Theta/\Theta'; \Rho; \Gamma; \Delta/\Delta'; \tau' \Downarrow\ \vdash M: C
        \\
        \forall \overline{\alpha}.\ \tau \sqsubseteq_E \tau'
        \\
        \textrm{ftv}_E(\tau') \cap \{ ?\alpha\ \vert\ (?\alpha \mapsto \tau_x) \in \Theta'\} = \emptyset
    }
    {\Theta/\Theta'; \Rho; \Gamma; \Delta/\Delta'; \forall \overline{\alpha}.\ \tau \Downarrow\ \vdash M: C}
\end{mathpar}
\item And rules regarding existential variables, both when using them for
instancing a type and when instancing an algebraic data type existential
argument type.
\begin{mathpar}
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
\end{itemize}

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

\section{Examples}%
\label{app:examples}

The following examples have two components, the input program that was
processed by our standalone synthesizer program, and the resulting program
including the synthesized fragments. In the examples, signatures preceeded by
|synth| mark synthesis goals for which programs using the type as the
specification will be synthesized. These examples also make use of the
experimental keywords such as |choose| and |using|.

\mypara{Maybe}\
\\
Input program:
\begin{code}
data Maybe a = Nothing | Just a;
data List a = Nil | Cons (a * List a);

synth return :: a ⊸ Maybe a;
synth empty :: Maybe a;
synth bind :: Maybe a ⊸ (a ⊸ Maybe b) -> Maybe b;
synth maybe :: b -> (a ⊸ b) -> Maybe a ⊸ b;
\end{code}
Output program:
\begin{code}
return :: (a ⊸ Maybe a);
return = Just;

empty :: Maybe a;
empty = Nothing;

bind :: (Maybe a ⊸ (!(a ⊸ Maybe b) ⊸ Maybe b));
bind c d = case c of
    Nothing -> let !e = d in Nothing
  | Just f -> let !g = d in g f;

maybe :: (!b ⊸ (!(a ⊸ b) ⊸ (Maybe a ⊸ b)));
maybe c d e = let !f = c in
  let !g = d in
    case e of
        Nothing -> f
      | Just h -> g h;
\end{code}

\mypara{List}\
\\
Input program:
\begin{code}
data List a = Nil | Cons (a * List a);
data Maybe a = Nothing | Just a;

synth singleton :: a ⊸ List a;
synth append :: List a ⊸ List a ⊸ List a;
synth map :: (!(a ⊸ b)) ⊸ List a ⊸ List b;
synth foldl :: !(b ⊸ a ⊸ b) ⊸ b ⊸ List a ⊸ b | choose 1;
synth uncons :: List a ⊸ Maybe (a * List a);
synth foldr :: !(a ⊸ b ⊸ b) ⊸ b ⊸ List a ⊸ b;
synth insert :: a ⊸ List a ⊸ List a;
synth concat :: List (List a) ⊸ List a;
\end{code}
Ouput program:
\begin{code}
singleton :: (a ⊸ List a);
singleton b = Cons (b, Nil);

append :: (List a ⊸ (List a ⊸ List a));
append b c = case b of
    Nil -> c
  | Cons d ->
      let e*f = d in Cons (e, append f c);

map :: (!(a ⊸ b) ⊸ (List a ⊸ List b));
map c d = let !e = c in
  case d of
      Nil -> Nil
    | Cons f ->
        let g*h = f in Cons (e g, map (!e) h);

foldl :: (!(b ⊸ (a ⊸ b)) ⊸ (b ⊸ (List a ⊸ b)));
foldl c d e = let !f = c in
  case e of
      Nil -> d
    | Cons g ->
        let h*i = g in
          foldl (!f) (f d h) i;

uncons :: (List a ⊸ Maybe (a * List a));
uncons b = case b of
    Nil -> Nothing
  | Cons c -> let d*e = c in Just (d, e);

foldr :: (!(a ⊸ (b ⊸ b)) ⊸ (b ⊸ (List a ⊸ b)));
foldr c d e = let !f = c in
  case e of
      Nil -> d
    | Cons g ->
        let h*i = g in
          f h (foldr (!f) d i);

insert :: (a ⊸ (List a ⊸ List a));
insert b c = case c of
    Nil -> Cons (b, Nil)
  | Cons h*i -> Cons (h, insert b i);

concat :: (List (List a) ⊸ List a);
concat b = case b of
    Nil -> Nil
  | Cons d*e ->
        case d of
            Nil -> concat e
          | Cons k ->
              let l*m = k in
                Cons (l, concat (Cons (m, e)));
\end{code}

\mypara{State}
%(with a slight optimization that will be added as a control keyword
%futurely, that allows bind using runState to terminate in a reasonable time)
Input program:
\begin{code}
data State b a = State (!b ⊸ (a * !b));

synth runState :: State b a ⊸ (!b ⊸ (a * !b));
synth bind :: (State c a ⊸ (a ⊸ State c b) ⊸ State c b) | using (runState);
synth return :: a ⊸ State b a;
synth get :: State a a;
synth put :: !a ⊸ (State a 1);
synth modify :: (!a ⊸ !a) ⊸ State a 1;
synth evalState :: State b a ⊸ !b ⊸ a;
\end{code}
Output program:
\begin{code}
data State b a = State (!b ⊸ (a * !b));

runState :: (State b a ⊸ (!b ⊸ (a * !b)));
runState c !f = case c of
    State e ->
        let h*i = e (!f) in
          let !j = i in (h, (!j));

bind :: (State c a ⊸ ((a ⊸ State c b) ⊸ State c b));
bind bs bt = case bs of
    State bu ->
      State (\bv -> let !bw = bv in
                      let cu*cv = bu (!bw) in
                        let !cw = cv in
                          (let dr*ds = runState (bt cu) (!cw) in
                             let !dt = ds in dr, (!cw)));

return :: (a ⊸ State b a);
return c = State (\d -> let !e = d in
               (c, (!e)));

get :: State a a;
get = State (\b -> let !c = b in
               (c, (!c)));

put :: (!a ⊸ State a 1);
put b = let !c = b in
  State (\d -> let !e = d in
                 ((), (!e)));

modify :: ((!a ⊸ !a) ⊸ State a 1);
modify b = State (\c -> let !d = c in
               let !f = b (!d) in ((), (!f)));

evalState :: (State b a ⊸ (!b ⊸ a));
evalState c d = case c of
    State e ->
      let !f = d in
        let h*i = e (!f) in
          let !j = i in h;
\end{code}

