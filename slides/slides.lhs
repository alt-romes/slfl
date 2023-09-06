\documentclass[aspectratio=169,dvipsnames]{beamer}

\usepackage{appendixnumberbeamer}
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

\usepackage{hyperref}
% \usepackage{svg}

\usetheme{Copenhagen}
%\usetheme{Singapore}
\usecolortheme{spruce}
\setbeamertemplate{navigation symbols}{}
\setbeamertemplate{itemize items}[circle]
\setbeamercovered{transparent}
\setbeamertemplate{footline}[frame number]

%include polycode.fmt
%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format ⊸ = "\lolli "
%format mid = "\mid"
%format period_   = "."

\newcommand{\lolli}{\multimap}
\newcommand{\tensor}{\otimes}
\newcommand{\one}{\mathbf{1}}
\newcommand{\bang}{{!}}
\newcommand{\mypara}[1]{\paragraph{\textbf{#1}.}}
\newcommand{\bararound}[1]{\mid\!#1\!\mid}

\newcommand{\listof}[1]{[#1]}

\newcommand{\llet}[2]{\mathsf{let}\ #1\ \mathsf{in}\ #2}
\newcommand{\myFor}[2]{\For{$#1$}{$#2$}}
\newcommand{\id}[1]{\textsf{\textsl{#1}}}
\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}

\title{Functional Program Synthesis from Linear Types}
\author{Rodrigo Mesquita}

\begin{document}

\frame[plain]{\titlepage}

\begin{frame}{Program synthesis}
  Program synthesis is about deriving programs from high-level specifications.
  \begin{itemize}
    \item<2-> The search space of valid programs is very large
    \item<2-> We need to interpret user intent
  \end{itemize}
  \pause
  Specifications can be
  \begin{itemize}
  \item Natural language (ChatGPT)
  \item Type-driven
  \item Example-driven
  \end{itemize}
\end{frame}

\begin{frame}{Type-driven program synthesis}
In \emph{type-driven} synthesis, the high-level specifications are (rich) types
\begin{itemize}
\item<2-> Types are a familiar interface for the user
\item<2-> Rich types prune the search space
  \begin{itemize}
  \item<2-> $(x:\mathsf{Int}) \to (y:\mathsf{Int}) \to \{z:\mathsf{Int} \mid z = x + y \}$ is very precise
  \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}{Example Synthesis from Types}

\only<1>{
\begin{example}[Goal]
\begin{code}
map :: (a -> b) -> [a] -> [b]
\end{code}
\end{example}
}

\only<2-3>{
\begin{example}[Wrong program synthesized]
\begin{code}
map :: (a -> b) -> [a] -> [b]
map f ls = []
\end{code}
\end{example}
}

\only<3>{
\begin{itemize}
\item Simples types specify what goes in and out
\item But not much on what happens
\end{itemize}
}

\only<4->{
\begin{example}[What we wanted]
\begin{code}
map :: (a -> b) -> [a] -> [b]
map f ls = case ls of
  Nil -> Nil
  Cons x xs -> Cons (f x) (map f xs)
\end{code}
\end{example}
}

\only<5->{
\begin{itemize}
\item We need goals to be more precise
\item S.t. the correct map function follows unambiguously from its type
\item<6> We argue linear types make for good specifications, concisely
restricting what the function does with the arguments
\end{itemize}
}


\end{frame}

\begin{frame}{Linear Types}

A linear function ($\lolli$) consumes its argument \emph{exactly once}
% \\(if its application is consumed exactly once)

\only<2>{
\begin{example}[Bad!]
\begin{code}
map :: (a ⊸ b) -> [a] ⊸ [b]
map f ls = []
\end{code}
\end{example}
(List is unused)
}

\only<3->{
\begin{example}[Good!]
\begin{code}
map :: (a ⊸ b) -> [a] ⊸ [b]
map f ls = case ls of
  Nil -> Nil
  Cons x xs -> Cons (f x) (map f xs)
\end{code}
\end{example}

}
\only<4>{
Linear types concisely describe interesting functions
\begin{itemize}
\item<4-> They say exactly which arguments \emph{must be used}
\end{itemize}
}
\end{frame}

\begin{frame}{Our contribution}
We explore \textbf{synthesis} from specifications based on \textbf{linear types}.\\
% \begin{itemize}
% \item Linear types have been generally overlooked in synthesis
% \item And are making their way into mainstream languages, like Haskell
% \item This paves the way for synthesis of concurrent programs from Session Types
% \end{itemize}
\pause
Linear types make for \textbf{good specifications}
\begin{itemize}
\item<1-2> Concisely specify how things are used to describe interesting programs
\item<1-2> Greatly prune the search space
  % \begin{itemize}
  % \item We don't consider programs where linear propositions are used more than once!
  % \end{itemize}
\end{itemize}
\pause
We develop a framework for synthesis of linear programs\pause 
  \begin{itemize}
    \item<1-4> Extending a core linear language with features like recursion and polymorphism
  \end{itemize}
\pause
And implement the framework as a standalone synthesizer and a GHC plugin
% And we support that claim through a prototype standalone synthesizer\footnote{https://github.com/alt-romes/slfl} and a GHC type-hole plugin\footnote{https://github.com/alt-romes/ghc-linear-synthesis-plugin}
\end{frame}

\begin{frame}{Core language for Synthesis}

The core language for synthesis we use is a pure functional linear calculus
\begin{itemize}
\item With linear functions ($\lolli$), pairs ($(x,y)$), ...
\item No recursion, no datatypes, no polymorphism
\end{itemize}

\end{frame}

\begin{frame}{So, how do we synthesize a (linear) program?}
Synthesizing a program seems like a daunting task, but we can reduce it to the more well-known problem of proof-search
% \footnote{Furthermore, the connection between linear types and linear logic
% allows us to leverage the large body of literature on linear logic}
\pause
\begin{block}{Curry-Howard isomorphism}
\begin{itemize}
\item Fundamental connection between logic and programming languages
\begin{itemize}
  \item Propositions are types\pause
  \item Proofs are programs\pause
  \item \emph{Proof-search is program-synthesis}
\end{itemize}
\end{itemize}
\end{block}
\pause
If proofs are programs and props are types, constructing a proof of a
proposition is deriving a program of a given type.
\end{frame}

% \begin{frame}{Linear logic to linear types}

% Curry-Howard gives a mapping between linear logic and our linear language
% \pause
% \only<1-2>{
% \begin{itemize}
% \item Propositions in linear logic map to linear types (e.g. $A \lolli B$)
% \item Proofs in linear logic map to linear programs
% \item Each language construct maps to an inference rule in the logic
% \end{itemize}
% }

% \only<3->{

% }
% \end{frame}

\begin{frame}{Synthesis as proof search (Example)}

\only<1>{
\begin{example}[Prove A $\lolli$ A]
\[
\infer{?}{\cdot \vdash A \lolli A}
\]
\end{example}
}

\only<2>{
\begin{example}[Prove A $\lolli$ A]
\[
\infer*[right=($\lolli I$)]
{
  \infer{?}{A \vdash A}
}{\cdot \vdash A \lolli A}
\]
\end{example}
}

\only<3-4>{
\begin{example}[Prove A $\lolli$ A]
\[
\infer*[right=($\lolli I$)]
{
  \infer*[right=($Init$)]{\,}{A \vdash A}
}{\cdot \vdash A \lolli A}
\]
\end{example}
}

\only<5>{
\begin{example}[Program from A $\lolli$ A]
\[
\begin{array}{ccc}
\begin{array}{c}
\infer*[right=($\lolli I$)]
{
  \infer*[right=($Init$)]{\,}{A \vdash A}
}{\cdot \vdash A \lolli A}\end{array} & \Longrightarrow & \lambda x.~\_
\end{array}
\]
\end{example}
}

\only<6>{
\begin{example}[Program from A $\lolli$ A]
\[
\begin{array}{ccc}
\begin{array}{c}
\infer*[right=($\lolli I$)]
{
  \infer*[right=($Init$)]{\,}{A \vdash A}
}{\cdot \vdash A \lolli A}\end{array} & \Longrightarrow & \lambda x.~x
\end{array}
\]
\end{example}
}

\only<4->{
Through C.H. correspondence we can extract a program from this proof
\begin{itemize}
\item $Init$ maps to using a variable
\item $\lolli I$ maps to introducing a function (i.e. lambda abstraction)
\end{itemize}
}

\end{frame}

% \begin{frame}{Synthesis as Proof Search (Example)}
% \only<1-2>{
% Consider this example program
% \[
% \begin{array}{l}
% \mathsf{id} : \forall \alpha.~\alpha\to\alpha\\
% \mathsf{id} = \Lambda \alpha.~\lambda (x{:}\alpha).~x
% \end{array}
% \]
% }
% \pause
% And its corresponding typing derivation
% \[
% \infer*[right=($\forall$\! I)]
% {
% \infer*[right=($\rightarrow$\! I)]
% {
% \infer*[right=($Var$)]
% { }
% {\alpha, x{:}\alpha \vdash x : \alpha}
% }
% {\alpha \vdash \lambda (x{:}\alpha).~x : \alpha \to \alpha}
% }
% {\cdot \vdash \Lambda \alpha.~\lambda (x{:}\alpha).~x : \forall \alpha.~\alpha\to\alpha}
% \]
% \end{frame}
%
% \begin{frame}{Synthesis as Proof Search (Example)}
% \only<1>{
% Let's start with the goal, and construct the proof bottom-up, applying the rules we can
% }
% \only<2>{
% The only rule that constructs a scheme is ($\forall\!$ I)
% }
% \only<3>{
% And the only rule that constructs a function is ($\rightarrow\!$ I)
% }
% \only<4>{
% And then to prove $\alpha$ knowning $\alpha$ we use ($Var$)
% }
% \only<5-9>{
% We could simultaneously construct terms, which are compact representations of proofs
% }
% \[
% \only<1>{
% \infer
% { }
% {\cdot \vdash \_ : \forall \alpha.~\alpha\to\alpha}
% }
% \only<2>{
% \infer*[right=($\forall$\! I)]
% {
% \infer
% { }
% {\alpha \vdash \_ : \alpha \to \alpha}
% }
% {\cdot \vdash \_ : \forall \alpha.~\alpha\to\alpha}
% }
% \only<3>{
% \infer*[right=($\forall$\! I)]
% {
% \infer*[right=($\rightarrow$\! I)]
% {
% \infer
% { }
% {\alpha, x{:}\alpha \vdash \_ : \alpha}
% }
% {\alpha \vdash \_ : \alpha \to \alpha}
% }
% {\cdot \vdash \_ : \forall \alpha.~\alpha\to\alpha}
% }
% \only<4>{
% \infer*[right=($\forall$\! I)]
% {
% \infer*[right=($\rightarrow$\! I)]
% {
% \infer*[right=($Var$)]
% { }
% {\alpha, x{:}\alpha \vdash \_ : \alpha}
% }
% {\alpha \vdash \_ : \alpha \to \alpha}
% }
% {\cdot \vdash \_ : \forall \alpha.~\alpha\to\alpha}
% }
% \only<5>{
% \infer*[right=($\forall$\! I)]
% {
% \infer*[right=($\rightarrow$\! I)]
% {
% \infer*[right=($Var$)]
% { }
% {\alpha, x{:}\alpha \vdash \_ : \alpha}
% }
% {\alpha \vdash \_ : \alpha \to \alpha}
% }
% {\cdot \vdash \Lambda \alpha.~\_ : \forall \alpha.~\alpha\to\alpha}
% }
% \only<6>{
% \infer*[right=($\forall$\! I)]
% {
% \infer*[right=($\rightarrow$\! I)]
% {
% \infer*[right=($Var$)]
% { }
% {\alpha, x{:}\alpha \vdash \_ : \alpha}
% }
% {\alpha \vdash \lambda (x{:}\alpha).~\_ : \alpha \to \alpha}
% }
% {\cdot \vdash \Lambda \alpha.~\_ : \forall \alpha.~\alpha\to\alpha}
% }
% \only<7>{
% \infer*[right=($\forall$\! I)]
% {
% \infer*[right=($\rightarrow$\! I)]
% {
% \infer*[right=($Var$)]
% { }
% {\alpha, x{:}\alpha \vdash x : \alpha}
% }
% {\alpha \vdash \lambda (x{:}\alpha).~\_ : \alpha \to \alpha}
% }
% {\cdot \vdash \Lambda \alpha.~\_ : \forall \alpha.~\alpha\to\alpha}
% }
% \only<8>{
% \infer*[right=($\forall$\! I)]
% {
% \infer*[right=($\rightarrow$\! I)]
% {
% \infer*[right=($Var$)]
% { }
% {\alpha, x{:}\alpha \vdash x : \alpha}
% }
% {\alpha \vdash \lambda (x{:}\alpha).~x : \alpha \to \alpha}
% }
% {\cdot \vdash \Lambda \alpha.~\_ : \forall \alpha.~\alpha\to\alpha}
% }
% \only<9>{
% \infer*[right=($\forall$\! I)]
% {
% \infer*[right=($\rightarrow$\! I)]
% {
% \infer*[right=($Var$)]
% { }
% {\alpha, x{:}\alpha \vdash x : \alpha}
% }
% {\alpha \vdash \lambda (x{:}\alpha).~x : \alpha \to \alpha}
% }
% {\cdot \vdash \Lambda \alpha.~\lambda (x{:}\alpha).~x : \forall \alpha.~\alpha\to\alpha}
% }
% \]
% \end{frame}

\begin{frame}{Proof search, algorithmically}

In practice, proof search is challenging (the examples were simple)
\begin{itemize}
\item How do we guarantee the linear usage of resources? (resource management)
\item Which rules should we apply at any given moment? (focusing)
\end{itemize}

\end{frame}

\begin{frame}{Focusing -- proof search discipline}
The foundational technique we use for proof search is \emph{focusing}.\\
The key idea is
\pause
\begin{itemize}
\item Separating rules into ones that can be applied freely without affecting provability\pause
\item Applying all such rules eagerly\pause
\item \emph{Choose} from the others when no more ``immediate'' rules can be applied\pause
\item \emph{Backtrack} to choice if proof fails
\end{itemize}
\pause
(Focusing is sound and complete wrt linear logic)
\end{frame}

\begin{frame}{Focusing (Example)}
\[
\infer %*[right=($\lolli R$)]
{
\only<2->{
  \infer %*[right=($\wedge L$)]
  {
  \only<3->{
    \infer %*[right=($\wedge R$)]
    {
    \only<3>{choice!}
    \only<4>{
      \infer
      {fail}
      {A \vdash B}
      \and
      \infer
      {fail}
      {B \vdash A}
    }
    \only<5>{
      \infer
      { }
      {B \vdash B}
      \and
      \infer
      { }
      {A \vdash A}
    }
    }
    {A,B \vdash B \wedge A}
  }
  }
  {
  A \wedge B \vdash B \wedge A
  }
}
}
{
\cdot \vdash A \wedge B \lolli B \wedge A
}
\]
\end{frame}

\begin{frame}{Beyond propositional logic}

To synthesize more interesting programs (e.g. even map) we need more features\\
\pause
We extend our language with
\begin{itemize}
\item inductive datatypes,
\item recursion,
\item and polymorphism
\end{itemize}

\end{frame}

\begin{frame}{Handling Polymorphism}

\only<1>{
\begin{example}
\begin{code}
f :: a -> (a -> b) -> b
f x g = g x
\end{code}
\end{example}
\begin{itemize}
\item It's impossible to produce a polymorphic $b$ from nothing
\item The only way is to apply the function to the argument (parametricity!)
\item Parametric polymorphism further increases the expressiveness and preciseness of the goals
\end{itemize}
}

\only<2>{
Mostly, we also leverage the C.H. correspondence between polymorphism and second-order logic
\begin{itemize}
\item And integrate it in our focusing algorithm for synthesis
\end{itemize}
}
\end{frame}

\begin{frame}{Inductive datatypes and Recursion}

Recursion is crucial to synthesize more interesting programs (e.g. map), but is also a source of difficulties.\\
In essence
\pause
\begin{itemize}
\item Allow function name being synthesized to occur in its own body\pause
\item But we can't allow the trivial (incorrect) solution (e.g. $map = map$)\pause
\item The proof-search itself must terminate, which isn't trivial with inductive datatypes\pause
\end{itemize}

We integrate recursion into our system as well

\end{frame}

\begin{frame}{Non-terminating proof (Example)}

Consider
\begin{code}
data List = Nil | Cons Int List
\end{code}
\pause
and goal
\begin{code}
x :: List
\end{code}
\pause
if we (naively) always tried to construct list using |Cons|, we would never terminate
\begin{code}
x = Cons 0 (Cons 0 (Cons 0 (Cons 0 ...)))
\end{code}
\pause
(We solve this by not allowing datatypes to be created/destructed unrestrictedly)

\end{frame}

\begin{frame}{Results}

We ran our synthesis framework implementation on custom synthesis benchmarks,
successfully synthesizing all goals performantly\\
\pause
And the coolest synth example is taken from Linear Haskell:\\
\begin{code}
newMArray :: Int -> (MArray a ⊸ Ur b) ⊸ b
write :: MArray a ⊸ (Int,a) -> MArray a
read :: MArray a ⊸ Int -> (MArray a, Ur b)
freeze :: MArray a ⊸ Ur (Array a)
synth array :: Int -> [(Int,a)] -> Array a
\end{code}
\pause
Resulting in:
\begin{code}
array size pairs = newMArray size (\ma -> freeze (foldl write ma pairs))
\end{code}
\end{frame}

\begin{frame}{Benchmarks}

\begin{figure}[t]
{\scriptsize
\begin{center}
    \begin{tabular}{ccccc}
        \hline
        Group & Goal & Avg. time $\pm\,\sigma$ & Keywords & Components \\
        \hline
        \pause
        \multirow{4}{4em}{Linear Logic} & uncurry & $133\mu s\pm 4.9\mu s$ &&\\ 
        %& distributivity & $179\mu s\pm 5.0\mu s$ && \\ 
        & call by name & $196\mu s\pm 4.6\mu s$ && \\ 
        & 0/1 & $294\mu s\pm 5.3\mu s$ && \\ 
        \hline
        \pause
        \multirow{7}{4em}{List} & map & $288\mu s\pm 7.2\mu s$  && \\ 
        & append & $292\mu s\pm 7.0\mu s$ & & \\ 
        & foldl & $1.69ms\pm 5.3\mu s$ & \emph{choose 1} & \\ 
        & foldr & $704\mu s\pm 10\mu s$ && \\ 
        & concat & $505\mu s\pm 18\mu s$ && \\
        %& uncons & $215\mu s\pm 15\mu s$ && \\
        & reverse & $17.4ms\pm 515\mu s$ & \emph{reverse [1,2] == [2,1]} & \\ 
        \hline
        \pause
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
        \pause
        Misc & either & $197\mu s\pm 5.3\mu s$ && \\ 
        \hline
        \pause
        \multirow{2}{4em}{Array} & & & \emph{depth 3} & \emph{freeze, foldl} \\
        & array~\ref{sec:evaluation} & $80ms\pm 870\mu s$ & \emph{using (foldl),depth 3} & \emph{newMArray,write} \\
        \hline
        \pause
        Refinements & add3 & $39ms\pm 1.1ms$ & & + \\
        \hline
    \end{tabular}
  \end{center}
}
\end{figure}

\end{frame}

\begin{frame}{Conclusion}
\begin{itemize}
\item Linear types make for good synthesis specifications\pause
\item Linear types synthesis is efficient
  \begin{itemize}
  \item We leverage linear logic literature (focusing)
  \item And never consider functions in which linear resources are not used linearly (pruning the space)
  \end{itemize}
\pause
\item This is the short version, see the paper for more:
  \begin{itemize}
  \item Refinements
  \item Hints
  \item etc...
  \end{itemize}
\end{itemize}
\end{frame}

\begin{frame}{The End}
\centering
Obrigado!
\end{frame}

\appendix

\begin{frame}{Constructing proofs algorithmically}
Constructing proofs algorithmically in linear logic is hard, there's a lot of non-determinism
\begin{itemize}
\item In the top-down nature of natural deduction elimination rules
\item In the splitting of linear contexts
\item In which rule to apply at any point
\end{itemize}
\end{frame}

\begin{frame}{ND1\footnote{This is the first of three non-determinism sources we'll address}: Elimination rules in a natural deduction system}
Our first source of non-determinism can be seen through the function introduction and elimination rules
\begin{mathpar}
\infer*[right=($\rightarrow\!$ I)]
{\Gamma, x{:}\alpha \vdash M : \beta}
{\Gamma \vdash (\lambda (x{:}\alpha).~M) : \alpha \rightarrow \beta}
\and
\infer*[right=($\rightarrow\!$ E)]
{\Gamma \vdash M : \varphi \rightarrow \beta \and \Gamma \vdash N : \varphi}
{\Gamma \vdash M~N : \beta}
\and
\only<1>{
\infer
{ ? }
{\cdot \vdash (\alpha \lolli \beta) \lolli \alpha \lolli \beta}
}
\only<2->{
\infer*[right=($\rightarrow$\! I)]
{
\infer
{ ? }
{f{:}\alpha\lolli\beta,x{:}\alpha \vdash \beta}
}
{\cdot \vdash (\alpha \lolli \beta) \lolli \alpha \lolli \beta}
}
\end{mathpar}
\only<3>{
We'd need to come up with some instantiation of $\varphi$ in order to apply ($\rightarrow$\! E).
}
\end{frame}

\begin{frame}{Sequent calculus to the rescue}
The issue is natural deduction elimination rules are read top-down.
However, in the (equivalent) \emph{sequent calculus} all inference rules can be naturally read bottom-up!
\pause
\begin{mathpar}
  \infer*[right=($\rightarrow L$)]
  {\Gamma, f{:}\alpha\rightarrow\beta, x{:}\beta \vdash M : \tau \and \Gamma, f{:}\alpha\rightarrow\beta \vdash N : \alpha}
  {\Gamma, f{:}\alpha\rightarrow\beta \vdash M[f~N/x] : \tau}
\end{mathpar}
\end{frame}

\begin{frame}{ND2: Splitting linear contexts}
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
\end{frame}

\begin{frame}{Using Input/Output contexts}
\begin{mathpar}
{\small
\infer[($\lolli$\! R)]
{\Delta_1, x{:}A/\Delta_2 \vdash M : B}
{ \Delta_1/\Delta_2 \vdash \lambda x. M : A\lolli B}
\and
\infer[($\tensor$ \! R)]
{\Delta_1/\Delta_2 \vdash M : A \and \Delta_2/\Delta_3 \vdash N : B}
{\Delta_1/\Delta_3 \vdash (M,N) : A \tensor B}
\and
\infer[(var)]
{ \, }
{\Delta_1,x/\Delta_1 : A \vdash x : A}
}
\end{mathpar}
\end{frame}

\begin{frame}{ND3: Don't-care non-determinism when applying rules}
Andreoli's "focusing" disciplines proof-search by reformulating sequent
calculus rules to remove don't-care-non-determinism.
\begin{itemize}
\item Split rules into \emph{invertible} and \emph{non-invertible}
\item Apply all invertible rules eagerly and then choose a proposition to \emph{focus} on.
\item Then apply non-invertible rules until we reach the end, an invertible proposition, or fail
\item On fail, backtrack to the state in which focusing began.
\end{itemize}

\end{frame}

\begin{frame}{Andreoli's focusing}
\begin{mathpar}
\Gamma; \Delta; \Omega \vdash M : A \Uparrow
\and
\Gamma; \Delta; \Omega \Uparrow\ \vdash M : A
\and
\Gamma;\Delta \vdash M : A \Downarrow
\and
\Gamma;\Delta; B\Downarrow\ \vdash M: A
\end{mathpar}
\end{frame}

\begin{frame}{The rest of the owl}
Combining linear logic, sequent calculus, resource management, and focusing, we
can define a core system to drive the synthesis process for linear logic.
\pause
\begin{itemize}
\item Is complete wrt propositional linear logic
\item Only has essencial non-determinism
\item Know exactly where to backtrack from
\end{itemize}
\pause
But this core system doesn't treat
\begin{itemize}
\item Recursion
\item Inductive datatypes
\item Polymorphism
\end{itemize}
\pause
We explain how we handle that in the paper!
\end{frame}

\end{document}

% vim: foldmethod=marker foldmarker=\\begin{frame},\\end{frame} foldenable
