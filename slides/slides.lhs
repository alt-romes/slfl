\documentclass[aspectratio=169,dvipsnames]{beamer}

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

\begin{frame}{Type-driven program synthesis}

Program synthesis is about deriving programs from high-level specifications.
\begin{itemize}
  \item<2-> The search space of valid programs is very large
  \item<2-> We need to interpret user intent
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

\begin{frame}{Our contribution}
We explore \textbf{synthesis} from specifications based on \textbf{linear types}.
\begin{itemize}
\item Linear types have been generally overlooked in synthesis
\item And are making their way into mainstream languages, like Haskell
\item This paves the way for synthesis of concurrent programs from Session Types
\end{itemize}
\pause
Linear types make for \textbf{great specifications}
\begin{itemize}
\item Describe interesting programs by nature
\item Greatly prune the search space % We don't consider programs where linear propositions are used more than once!
\end{itemize}
\pause
And we support that claim through a prototype standalone synthesizer\footnote{https://github.com/alt-romes/slfl} and a GHC type-hole plugin\footnote{https://github.com/alt-romes/ghc-linear-synthesis-plugin}
\end{frame}

\begin{frame}{Linear Types (aside)}

A linear function consumes its argument \emph{exactly once} \\(if its application is consumed exactly once)

\only<2>{
\begin{example}[Bad!]
\begin{code}
map :: (a ⊸ b) -> [a] ⊸ [b]
map _ _ = []
\end{code}
\end{example}
}

\only<3->{
\begin{example}[Good!]
\begin{code}
map :: (a ⊸ b) -> [a] ⊸ [b]
map f ls = case ls of
  [] -> []
  x : xs -> f x : map f xs
\end{code}
\end{example}

}
\only<4>{
Linear types concisely describe interesting functions
\begin{itemize}
\item<4-> They say exactly which that things \emph{must be used}
\end{itemize}
}
\end{frame}

\begin{frame}{So, how do we synthesize a (linear) program?}
Synthesizing a program seems like a dauting task, but we can reduce it to the more well-known problem of proof-search\footnote{
Furthermore, the connection between linear types and linear logic allows us to leverage the
large body of literature on linear logic}.
\pause
\begin{block}{Curry-Howard isomorphism}
\begin{itemize}
\item Fundamental connection between logic and programming languages
\begin{itemize}
  \item Propositions are types\pause
  \item Proofs are programs\pause
  \item \emph{(Bottom-up) proof-search is program-synthesis}
\end{itemize}
\end{itemize}
\end{block}
\pause
If proofs are programs, constructing a proof is constructing a program!
\end{frame}

\begin{frame}{Synthesis as Proof Search (Example)}
\only<1-2>{
Consider this example program
\[
\begin{array}{l}
\mathsf{id} : \forall \alpha.~\alpha\to\alpha\\
\mathsf{id} = \Lambda \alpha.~\lambda (x{:}\alpha).~x
\end{array}
\]
}
\pause
And its corresponding typing derivation
\[
\infer*[right=($\forall$\! I)]
{
\infer*[right=($\rightarrow$\! I)]
{
\infer*[right=($Var$)]
{ }
{\alpha, x{:}\alpha \vdash x : \alpha}
}
{\alpha \vdash \lambda (x{:}\alpha).~x : \alpha \to \alpha}
}
{\cdot \vdash \Lambda \alpha.~\lambda (x{:}\alpha).~x : \forall \alpha.~\alpha\to\alpha}
\]
\end{frame}

\begin{frame}{Synthesis as Proof Search (Example)}
\only<1>{
Let's start with the goal, and construct the proof bottom-up, applying the rules we can
}
\only<2>{
The only rule that constructs a scheme is ($\forall\!$ I)
}
\only<3>{
And the only rule that constructs a function is ($\rightarrow\!$ I)
}
\only<4>{
And then to prove $\alpha$ knowning $\alpha$ we use ($Var$)
}
\only<5-9>{
We could simultaneously construct terms, which are compact representations of proofs
}
\[
\only<1>{
\infer
{ }
{\cdot \vdash \_ : \forall \alpha.~\alpha\to\alpha}
}
\only<2>{
\infer*[right=($\forall$\! I)]
{
\infer
{ }
{\alpha \vdash \_ : \alpha \to \alpha}
}
{\cdot \vdash \_ : \forall \alpha.~\alpha\to\alpha}
}
\only<3>{
\infer*[right=($\forall$\! I)]
{
\infer*[right=($\rightarrow$\! I)]
{
\infer
{ }
{\alpha, x{:}\alpha \vdash \_ : \alpha}
}
{\alpha \vdash \_ : \alpha \to \alpha}
}
{\cdot \vdash \_ : \forall \alpha.~\alpha\to\alpha}
}
\only<4>{
\infer*[right=($\forall$\! I)]
{
\infer*[right=($\rightarrow$\! I)]
{
\infer*[right=($Var$)]
{ }
{\alpha, x{:}\alpha \vdash \_ : \alpha}
}
{\alpha \vdash \_ : \alpha \to \alpha}
}
{\cdot \vdash \_ : \forall \alpha.~\alpha\to\alpha}
}
\only<5>{
\infer*[right=($\forall$\! I)]
{
\infer*[right=($\rightarrow$\! I)]
{
\infer*[right=($Var$)]
{ }
{\alpha, x{:}\alpha \vdash \_ : \alpha}
}
{\alpha \vdash \_ : \alpha \to \alpha}
}
{\cdot \vdash \Lambda \alpha.~\_ : \forall \alpha.~\alpha\to\alpha}
}
\only<6>{
\infer*[right=($\forall$\! I)]
{
\infer*[right=($\rightarrow$\! I)]
{
\infer*[right=($Var$)]
{ }
{\alpha, x{:}\alpha \vdash \_ : \alpha}
}
{\alpha \vdash \lambda (x{:}\alpha).~\_ : \alpha \to \alpha}
}
{\cdot \vdash \Lambda \alpha.~\_ : \forall \alpha.~\alpha\to\alpha}
}
\only<7>{
\infer*[right=($\forall$\! I)]
{
\infer*[right=($\rightarrow$\! I)]
{
\infer*[right=($Var$)]
{ }
{\alpha, x{:}\alpha \vdash x : \alpha}
}
{\alpha \vdash \lambda (x{:}\alpha).~\_ : \alpha \to \alpha}
}
{\cdot \vdash \Lambda \alpha.~\_ : \forall \alpha.~\alpha\to\alpha}
}
\only<8>{
\infer*[right=($\forall$\! I)]
{
\infer*[right=($\rightarrow$\! I)]
{
\infer*[right=($Var$)]
{ }
{\alpha, x{:}\alpha \vdash x : \alpha}
}
{\alpha \vdash \lambda (x{:}\alpha).~x : \alpha \to \alpha}
}
{\cdot \vdash \Lambda \alpha.~\_ : \forall \alpha.~\alpha\to\alpha}
}
\only<9>{
\infer*[right=($\forall$\! I)]
{
\infer*[right=($\rightarrow$\! I)]
{
\infer*[right=($Var$)]
{ }
{\alpha, x{:}\alpha \vdash x : \alpha}
}
{\alpha \vdash \lambda (x{:}\alpha).~x : \alpha \to \alpha}
}
{\cdot \vdash \Lambda \alpha.~\lambda (x{:}\alpha).~x : \forall \alpha.~\alpha\to\alpha}
}
\]
\end{frame}

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
