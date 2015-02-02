\documentclass[a4paper,UKenglish]{lipics}
%This is a template for producing LIPIcs articles. 
%See lipics-manual.pdf for further information.
%for A4 paper format use option "a4paper", for US-letter use option "letterpaper"
%for british hyphenation rules use option "UKenglish", for american hyphenation rules use option "USenglish"
% for section-numbered lemmas etc., use "numberwithinsect"
 
\usepackage{microtype}% if unwanted, comment out or use option "draft"

%\graphicspath{{./graphics/}}%helpful if your graphic files are in another directory

\bibliographystyle{plain}% the recommended bibstyle
%%%\smartqed  % flush right qed marks, e.g. at end of proof
%
\usepackage{graphicx}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{url}
\usepackage{stmaryrd}
\usepackage{ifpdf}
\ifpdf
  \usepackage{hyperref}
\fi
%\usepackage[x11names]{xcolor}
%\usepackage[all]{xy}
%\usepackage{xspace}
%\usepackage{pstricks}
%\usepackage{listings}
%\usepackage{wrapfig}
%\usepackage{mathpartir}

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%subst numeral a = "\C{" a "}"

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.4,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor{yellow}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0,0,0}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
}

\ColourStuff

\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\C}[1]{\red{\mathsf{#1}}}
\newcommand{\F}[1]{\green{\mathsf{#1}}}
\newcommand{\V}[1]{\purple{\mathit{#1}}}

\newtheorem{princ}{Principle}

\newcommand{\citep}{\cite}
\newcommand{\citet}{\cite}

% Author macros::begin %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{A Polynomial Testing Principle}
%\titlerunning{A Polynomial Testing Principle} %optional, in case that the title is too long; the running title should fit into the top page column

\author{Conor McBride}
\affil{Mathematically Structured Programming Group, University of Strathclyde\\
  Livingstone Tower, 26 Richmond Street, Glasgow, G1 1XH, Scotland\\
  \texttt{conor.mcbride@@strath.ac.uk}}
\authorrunning{C. McBride} %mandatory. First: Use abbreviated first/middle names. Second (only in severe cases): Use first author plus 'et. al.'

\Copyright{Conor McBride}%mandatory, please use full first names. LIPIcs license is "CC-BY";  http://creativecommons.org/licenses/by/3.0/

\subjclass{F.4.1 Mathematical Logic}% mandatory: Please choose ACM 1998 classifications from http://www.acm.org/about/class/ccs98-html . E.g., cite as "F.1.1 Models of Computation". 
\keywords{finite difference methods, testing coverage, mechanical theorem proving, dependently typed programming}% mandatory: Please provide 1-5 keywords
% Author macros::end %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Editor-only macros:: begin (do not touch as author)%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\serieslogo{}%please provide filename (without suffix)
\volumeinfo%(easychair interface)
  {Billy Editor and Bill Editors}% editors
  {2}% number of editors: 1, 2, ....
  {Conference title on which this volume is based on}% event
  {1}% volume
  {1}% issue
  {1}% starting page number
\EventShortName{}
\DOI{10.4230/LIPIcs.xxx.yyy.p}% to be completed by the volume editor
% Editor-only macros::end %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\maketitle

\begin{abstract} 
Two polynomial functions of degree at most \(n\)
agree on all inputs if they agree on \(n+1\) different inputs, e.g.,
on \(\{0,1,2,\ldots,n\}\). This fact gives us a simple procedure for
testing equivalence in a language of polynomial expressions. Moreover,
we may readily extend this language to include a summation operator
and test standard results which are usually established inductively.

I present a short proof of this testing principle which rests on the
construction and correctness of a syntactic forward-difference
operator. This paper is a literate Agda file,
containing just one
%format TLCAPoly = "\mathsf{TLCAPoly}"
\begin{code}

module TLCAPoly where

\end{code}
nothing is imported and there are 250 non-blank lines of code,
all of which I show here.
\end{abstract}

\section{In(tro)duction}

Once upon a time in the late 1990s, I was a PhD student working for
Rod Burstall at the Laboratory for Foundations of Computer Science in
Edinburgh. I supplemented my income by working as a teaching assistant
for the Computer Science department, and I supplemented my income
supplement by moonlighting as a teaching assistant for the Mathematics
department, working in particular with classes taught by
mathematicians to first year undergraduate computer scientists. The
mathematicians often asked the students to ``show'' things which was,
for many of our students, an unfamiliar game. Old chestnuts like \[
\sum_{0 \le i \le n}i = \frac{1}{2}n(n+1)
\hfill\mbox{were a cause of panic and terror.}
 \]
Learning to prove via weekly assignments is rather like
learning chess by post: on Monday you send a card stating your move,
and on Friday you receive the reply ``You can't do that with a
Bishop!''.

My PhD research involved working with interactive proof assistants
(specifically, \textsc{Lego}~\citep{legomanual}), so it seemed obvious
to me that we should consider the use of machines to shorten the
undergraduate feedback loop. At the time, Rod was working on a more
basic proof editor,
\textsc{ProveEasy}~\citep{DBLP:journals/tcs/Burstall00}, with which he was
successfully teaching programming language semantics to third year
undergraduates. I wondered if \textsc{ProveEasy} might help the first
years grapple with induction and proposed to demonstrate Rod's system
to my mathematical employers. Carefully avoiding vulgar fractions, I drove
the machine to deliver an interactive proof of
\[ 2\sum_{0 \le i \le n}i = n(n+1)
\hfill \mbox{They were unimpressed. I became depressed.}
\]

To cheer me up, Rod attempted cynicism: `But Conor, aren't most of
these students going to work in banks? Do they really to prove that?
Don't they just need to bung in three numbers and see that it works?'.
`Rod,' I replied, `you're absolutely right. The formulae on both sides
of the equation are manifestly quadratic, so bunging in three numbers
to see that it works \emph{is} a proof!'. Of course, it takes rather
more mathematics to see why the result is that easy to \emph{test}
than to \emph{prove} it directly. Indeed, I intended my remark merely
as a throwaway absurdity, but it stuck with me. Once in a while I
would idly fiddle with representations of polynomials, looking for an
easy way to prove a testing lemma, but somehow things always became
tricky very quickly.

Little did I know in the late 1990s that Marko Petkov\v{s}ek, Herbert
Wilf and Doron Zeilberger had given a fascinating
treatment of this and other `proof by testing' methods in their
wondrous compendium, \emph{A=B}~\cite{zeil}. Their tools are powerful
but informal computer algebra packages: mine is Martin-L\"of's
intensional type theory~\cite{martinloef:atheoryoftypes}, which is a
formal discipline for proof where the division of labour between
people and machines is negotiable by the act of programming.
Recently, I found a way to prove the result in 250 lines of
Agda~\cite{norell:agda}, without recourse to any library
functionality, and remaining entirely within the theory of the natural
numbers. I suspect this means I have learned something in the
intervening years. This paper is an attempt to communicate it.


\section{Polynomials and testing}

\newcommand{\con}{\underline}
\newcommand{\id}{\iota}
\newcommand{\pp}{\:\oplus\:}
\newcommand{\pt}{\mathbin{\otimes}}

Polynomial functions are just those generated by
constants and the identity, closed under pointwise addition and multiplication.
\[
\con{n}\:x = n
\qquad
\id\:x = x
\qquad
(p\pp q)\:x = p\:x + q\:x
\qquad
(p\pt q)\:x = p\:x \times q\:x
\]

\newcommand{\dgr}[1]{||{#1}||}
\newcommand{\fd}{\Delta}

We can define the \emph{degree}, \(\dgr{p}\), of a polynomial recursively:
\[
\dgr{\con{n}}=0\qquad
\dgr{\id}=1\qquad
\dgr{p\pp q} = \dgr{p} \vee \dgr{q} \qquad
\dgr{p\pt q} = \dgr{p} + \dgr{q}
\]

The \emph{testing principle} is just that if \(\dgr{p} \le n\),
\(\dgr{q} \le n\) and \(p\:i = q\:i\) for \(i\in\{0,1,\ldots,n\}\),
then \(p\:x=q\:x\) for all natural numbers \(x\).

One way to see that it holds is to construct the \emph{forward-difference} operator,
\(\fd\), satisfying the specification
\[
  \fd p \:x = p\:(1+x) - p \:x
\]
and check that
\begin{itemize}
\item if \(\dgr{p}=0\) then \(p = \con{p\:0}\) and \(\fd p = \con{0}\)
\item if \(\dgr{p}=1+n\) then \(\dgr{\fd p}=n\).
\end{itemize}
The specification of \(\fd\) gives us an easy proof that
\[
  p\:x = p\:0 + \sum_{i < x}\fd p\:i
\]

As a consequence we should gain an easy inductive argument for the
testing principle: if \(p\) and \(q\) have degree at most \(1+n\) and
agree on \(\{0,1,\ldots,1+n\}\), then \(p\:0=q\:0\) and \(\fd p\) and
\(\fd q\) agree on \(\{0,1,\ldots,n\}\); inductively, \(\fd p = \fd
q\), so replacing equal for equal in the above summation, \(p\:x = q\:x\).

So, can we construct \(\fd\) and make this argument formal? McBrides
have been in the business of constructing symbolic differential
operators in functional programming languages for nearly half a
century~\cite{dad-phd}, so it will be something of a shame for me if
we cannot. It is, however, tricky in parts.


\section{Polynomials by degree}

We can define natural numbers and the basic arithmetic operators
straightforwardly. The `BUILTIN' pragma allows us to use decimal notation.

%format Set = "\D{Set}"
%format Nat = "\D{Nat}"
%format ze = "\C{ze}"
%format su = "\C{su}"
%format + = "\mathbin{\F{+}}"
%format * = "\mathbin{\F{\times}}"
%format \/ = "\mathbin{\F{\vee}}"
%format _+_ = "\F\_\!" + "\!\F\_"
%format _*_ = "\F\_\!" * "\!\F\_"
%format _\/_ = "\F\_\!" \/ "\!\F\_"

\begin{code}
data Nat : Set where
  ze  :         Nat
  su  : Nat ->  Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
ze    + y  = y
su x  + y  = su (x + y)
infixr 5 _+_

_*_ : Nat -> Nat -> Nat
ze * x      = ze
su n * x  = n * x + x
infixr 6 _*_
\end{code}

%format sum = "\F{\Sigma}"
\newcommand{\sumDefn}{
\begin{code}
sum : (f : Nat -> Nat) -> Nat -> Nat
sum f ze      = 0
sum f (su n)  = sum f n + f n
\end{code}}

%format == = "\mathrel{\D{\equiv}}"
%format _==_ = "\D\_\!" == "\!\D\_"
%format refl = "\C{refl}"
%format =$= = "\F{=\!\!\!\!\$\!\!\!\!=}"
%format $= = "\F{\$\!\!\!\!=}"
%format =$ = "\F{=\!\!\!\!\$}"
%format _=$=_ = _ =$= _
%format _$=_ = "\F{\_}" $= "\F{\_}"
%format _=$_ = "\F{\_}" =$ "\F{\_}"
%format Agda.Primitive = "\mathsf{Agda.Primitive}"
%format Level = "\D{Level}"
%format <^ = "\F{\lceil}\!"
%format ^> = "\!\F{\rceil}"
%format <^_^> = <^ _ ^>
\newcommand{\equalityDecl}{
\begin{code}
data _==_ {A : Set}(a : A) : A -> Set where refl : a == a
infix 0 _==_
\end{code}
}

%format !!! = "\F{\square}"
%format _!!! = "\F{\_}" !!!
%format =! = "\F{=\!\![}"
%format !> = "\F{\rangle\!\!=}"
%format != = "\F{]\!\!=}"
%format <! = "\F{=\!\!\langle}"
%format _=!_!>_ = "\F{\_}" =! "\F{\_}" !> "\F{\_}"
%format _<!_!=_ = "\F{\_}" <! "\F{\_}" != "\F{\_}"
\newcommand{\equalityRewriting}{
\begin{code}
_=!_!>_ : forall {X : Set}(x : X){y z} -> x == y -> y == z -> x == z
x =! refl !> q = q

_<!_!=_ : forall {X : Set}(x : X){y z} -> y == x -> y == z -> x == z
x <! refl != q = q

_!!! : forall {X : Set}(x : X) -> x == x
x !!! = refl
infixr 2 _!!! _=!_!>_ _<!_!=_
\end{code}}

\newcommand{\equalityTools}{
\begin{code}
<^_^> : forall {X : Set}(x : X) -> x == x
<^ x ^> = refl

_=$=_ : {S T : Set}{f g : S -> T}{x y : S} -> f == g -> x == y -> f x == g y
refl =$= refl = refl

infixl 9 _=$=_
\end{code}}

%format One = "\D{1}"
%format <> = "\C{\langle\rangle}"
%format constructor = "\mathkw{constructor}"
\newcommand{\oneDecl}{
\begin{code}
record One : Set where constructor <>
\end{code}}

%format Zero = "\D{0}"
\newcommand{\zeroDecl}{
\begin{code}
data Zero : Set where
\end{code}}

Addition and multiplication both associate rightward,
the latter binding more tightly. For convenience in writing polynomials,
let us also define exponentiation as iterated multiplication.

%format ^ = "\F{{}^{\wedge}}"
%format _^_ = "\F{\_}" ^ "\F{\_}"
\begin{code}
_^_ : Nat -> Nat -> Nat
x ^ ze    = 1
x ^ su n  = (x ^ n) * x
\end{code}

In order to capture \emph{degree}, one might be tempted to define
 \begin{code}
_\/_ : Nat -> Nat -> Nat
ze    \/  y     = y
su x  \/  ze    = su x
su x  \/  su y  = su (x \/ y)
\end{code}
and then give a type of polynomials \emph{indexed by degree}.
%format Woly = "\D{Poly}"
%format forall = "\forall"
%format wk = "\C{\kappa}"
%format wi = "\C{\id}"
%format w+ = "\mathbin{\C{\pp}}"
%format w* = "\mathbin{\C{\pt}}"
%format _w+_ = "\C\_\!" w+ "\!\C\_"
%format _w*_ = "\C\_\!" w* "\!\C\_"
%format wl = "\F{\llbracket}"
%format wr = "\F{\rrbracket}"
%format wl_wr = wl "\F{\_}" wr
 \begin{code}
data Woly : Nat -> Set where
  wk    :                             Nat ->     Woly 0
  wi    :                                        Woly 1
  _w+_  : forall {l m} ->  Woly l ->  Woly m ->  Woly (l \/ m)
  _w*_  : forall {l m} ->  Woly l ->  Woly m ->  Woly (l + m)

wl_wr : forall {n} -> Woly n -> Nat -> Nat
wl wk n wr    x = n
wl wi wr      x = x
wl p w+ r wr  x = wl p wr x + wl r wr x
wl p w* r wr  x = wl p wr x * wl r wr x
\end{code}

%format wd = "\F{\fd}"

We might attempt to define |wd| reducing degree, as follows
%format hole = "\orangeFG{?}"
%if False
 \begin{code}
postulate hole : {X : Set} -> X
\end{code}
%endif
\begin{spec}
wd : forall {n} -> Woly (su n) -> Woly n
wd wi        = hole
wd (p w+ r)  = hole
wd (p w* r)  = hole
\end{spec}
but these patterns do not
typecheck, because it is not obvious how to unify |su n| with |l \/ m|
or |l + m|. The trouble is that our |wd| function has a
\emph{prescriptive} index pattern in its argument type---not just a
universally quantified variable---whilst our constructors have
\emph{descriptive} indices, imposing constraints by instantiation.
For pattern matching to work, these indices must unify, but our use of
defined functions (which I habitually colour green), |l \/ m| and |l +
m|, have taken us outside the constructor-form language where
unification is straightforward. We have learned an important design principle.

\begin{princ}[Don't touch the green slime!]\footnote{With the advent of colour
television, the 1970s saw a great deal of science fiction
in which green cleaning gel Swarfega was portrayed as a noxious substance,
e.g., \emph{Doctor Who: The Green Death} by Robert Sloman and Barry Letts.}
When combining prescriptive and descriptive indices, ensure both are in constructor
form. Exclude defined functions which yield difficult unification problems.
\end{princ}

One way to avoid green slime without losing precision is to recast the datatype
definition equationally, making use of the \emph{propositional equality}:
\equalityDecl

We may now replace non-constructor descriptive indices by equations and get to work:
%format Joly = "\D{Poly}"
%format jk = "\C{\kappa}"
%format ji = "\C{\id}"
%format jplus = "\C{plus}"
%format jtimes = "\C{times}"
 \begin{code}
data Joly : Nat -> Set where
  jk      :                               Nat ->                        Joly 0
  ji      :                                                             Joly 1
  jplus   : forall {l m n} ->  Joly l ->  Joly m ->  (l \/ m)  == n ->  Joly n
  jtimes  : forall {l m n} ->  Joly l ->  Joly m ->  (l + m)   == n ->  Joly n
\end{code}
%format jd = "\F{\fd}"
\vspace*{ -0.3in}
 \begin{code}
jd : forall {n} -> Joly (su n) -> Joly n
jd ji                = jk 1
jd (jplus   p r  q)  = hole
jd (jtimes  p r  q)  = hole
\end{code}

To make further progress, we shall need somehow to exploit the fact
that in both cases, at least one of |p| and |r| has non-zero
degree. This is especially galling as, morally, we should have
something as simple as |wd (p w+ r) = wd p w+ wd r|.  By being precise
about the degree of polynomials, we have just made trouble for
ourselves. We have just encountered another design principle of
dependent types.

\begin{princ}[Jagger/Richards]\footnote{You can't
always get what you want, but if you try sometime, you just might find
that you get what you need.}  Be minimally
prescriptive, not maximally descriptive.
\end{princ}

In order to establish our testing principle, we do not need precise
knowledge of the degree of a polynomial: an \emph{upper bound} will
suffice.  We can see the index of our type of polynomials not as a
degree measure being propagated outwards, but as a degree requirement
being propagated \emph{inwards}. The very syntax of datatype declarations
is suggestive of descriptions propagated outwards, but it is usually a
mistake to think in those terms.

We can get a little further, observing that polynomials of all degrees are
closed under constants and addition, whilst the identity polynomial requires
the degree to be positive. It is only in the case of products that we
must precise about how we apportion our multiplicative resources.
%format Koly = "\D{Poly}"
%format kk = "\C{\kappa}"
%format ki = "\C{\id}"
%format ktimes = "\C{times}"
%format k+ = "\mathbin{\C{\pp}}"
%format _k+_ = _ w+ _
%format kd = "\F{\fd}"
 \begin{code}
data Koly : Nat -> Set where
  kk      : forall {n} ->                 Nat ->                        Koly n
  ki      : forall {n} ->                                               Koly (su n)
  _k+_    : forall {n} ->      Koly n ->  Koly n ->                     Koly n
  ktimes  : forall {l m n} ->  Koly l ->  Koly m ->  (l + m)   == n ->  Koly n

kd : forall {n} -> Koly (su n) -> Koly n
kd (kk _)            = kk 0
kd ki                = kk 1
kd (p k+ r)          = kd p k+ kd r
kd (ktimes  p r  q)  = hole
\end{code}

We can use the specification of |kd| to try to figure out how to deal with
multiplication. Firstly, let us eliminate subtraction by rephrasing
\[
p\:(1+x) = p\:x + \fd p\:x
\]
and then we may reason as follows:
\[\begin{array}{ll@@{\qquad}l}
   & (p\pt r)\:(1+x) & \mbox{definition of \(\pt\)} \\
 = & p\:(1+x) \times r\:(1+x) & \mbox{spec of \(\fd p\)}\\
 = & (p\:x + \fd p\:x) \times r\:(1+x)  & \mbox{distribution}\\
 = & p\:x\times r\:(1+x) + \fd p\:x \times r\:(1+x) & \mbox{spec of \(\fd r\)}\\
 = & p\:x\times(r\:x + \fd r\:x) + \fd p\:x\times r\:(1+x)  & \mbox{distribution}\\
 = & p\:x\times r\:x + p\:x\times\fd r\:x + \fd p\:x\times r\:(1+x)
    & \mbox{algebra} \\    
 = & (p\:x\times r\:x) + (\fd p\:x\times r\:(1+x) + p\:x\times\fd r\:x)
    & \mbox{definition of \(\pt\)} \\
 = & (p\pt r)\:x + (\fd p\:x\times r\:(1+x) + p\:x\times\fd r\:x) 
\end{array}\]
So, we need
\[
\fd(p\pt r) = \fd p \pt (r\cdot(1+)) \pp p\pt \fd r
\]

If we have eyes to see, we can take some useful hints here:
\begin{itemize}
\item we shall need to account for \emph{shifting}, as in \(r\cdot(1+)\);
\item we shall need to separate the degenerate cases where |p| or |r| have degree
  |ze| from the general case when both have non-zero degree, in order to ensure that
  |kd| is recursively applicable;
\item we shall need to make it obvious that
  |ze + n| = |n| = |n + ze| and |l + su m| = |su l + m|.
\end{itemize}

Shifting preserves degree, so we may readily add it to the datatype of
polynomials, at the cost of introducing some redundancy. Meanwhile,
the case analysis we need on our sum of degrees is not the one which
arises naturally from the recursive definition of |+|. Some theorem
proving will be necessary, but a good start is to write down the case
analysis we need, relationally. Indeed, this is a key lesson which I
learned from James McKinna and which sits at the heart of our work on
Epigram~\cite{conor.james:viewfromleft}:

\begin{princ}[Structure by Construction]
If you need to observe a particular inductive structure, work with the type which is
defined to have that inductive structure.
\end{princ}

%format Add = "\D{Add}"
%format zel = "\C{zel}"
%format zer = "\C{zer}"
%format susu = "\C{susu}"
%format Qoly = "\D{Poly}"
%format qk = "\C{\kappa}"
%format qi = "\C{\id}"
%format qu = "\C{\uparrow}\!"
%format qtimes = "\C{times}"
%format q+ = "\mathbin{\C{\pp}}"
%format _q+_ = "\C\_\!" q+ "\!\C\_"
%format qd = "\F{\fd}"
%format ql = "\F{\llbracket}"
%format qr = "\F{\rrbracket}"
%format ql_qr = ql "\F{\_}" qr
\begin{code}
data Add : Nat -> Nat -> Nat -> Set where
  zel   : forall {n} ->                   Add  ze      n       n
  zer   : forall {n} ->                   Add  n       ze      n
  susu  : forall {l m n} -> Add l m n ->  Add  (su l)  (su m)  (su (su n))
\end{code}

We can now define polynomials in a workable way.
\begin{code}
data Qoly : Nat -> Set where
  qk      : forall {n} ->                 Nat ->                    Qoly n
  qi      : forall {n} ->                                           Qoly (su n)
  qu      : forall {n} ->                 Qoly n ->                 Qoly n
  _q+_    : forall {n} ->      Qoly n ->  Qoly n ->                 Qoly n
  qtimes  : forall {l m n} ->  Qoly l ->  Qoly m ->  Add l m n ->   Qoly n
\end{code}
%if False
\begin{code}
  qsum    : forall {n} -> Qoly n -> Qoly (su n)
infixr 5 _q+_
\end{code}
%endif
The evaluator for polynomials can safely ignore the informatin about adding
degrees.
\begin{code}
ql_qr : forall {n} -> Qoly n -> Nat -> Nat
ql qk n qr          x = n
ql qi qr            x = x
ql qu p qr          x = ql p qr (su x)
ql p q+ r qr        x = ql p qr x + ql r qr x
ql qtimes p r a qr  x = ql p qr x * ql r qr x
\end{code}
%if False
\begin{code}
ql qsum p qr x = sum ql p qr x
\end{code}
%endif

However, when we come to define |qd|, we can now make substantial progress,
splitting the multiplication into the three cases which matter.
\begin{spec}
qd : forall {n} -> Qoly (su n) -> Qoly n
qd (qk _)                 = qk 0
qd qi                     = qk 1
qd (qu p)                 = qu (qd p)
qd (p q+ r)               = qd p q+ qd r
qd (qtimes p r zel)       = qtimes (qk (ql p qr 0)) (qd r)  zel
qd (qtimes p r zer)       = qtimes (qd p) (qk (ql r qr 0))  zer
qd (qtimes p r (susu a))  = qtimes (qd p) (qu r) hole q+ qtimes p (qd r) hole
\end{spec}

The proof obligations, thus identified, are easily discharged:
%format sul = "\F{sul}"
%format sur = "\F{sur}"
\begin{code}
sul : forall {l m n} -> Add l m n -> Add (su l) m (su n)
sul (zel {ze})    = zer
sul (zel {su n})  = susu zel
sul zer           = zer
sul (susu s)      = susu (sul s)

sur : forall {l m n} -> Add l m n -> Add l (su m) (su n)
sur zel           = zel 
sur (zer {ze})    = zel
sur (zer {su n})  = susu zer
sur (susu s)      = susu (sur s)
\end{code}

%if False
\begin{code}
qd : forall {n} -> Qoly (su n) -> Qoly n
qd (qk _)                 = qk 0
qd qi                     = qk 1
qd (qu p)                 = qu (qd p)
qd (p q+ r)               = qd p q+ qd r
qd (qtimes p r zel)       = qtimes (qk (ql p qr 0)) (qd r)  zel
qd (qtimes p r zer)       = qtimes (qd p) (qk (ql r qr 0))  zer
qd (qtimes p r (susu a))  = qtimes (qd p) (qu r) (sur a) q+ qtimes p (qd r) (sul a)
qd (qsum p)               = p
\end{code}
%endif
\vspace*{ -0.3in}
\begin{spec}
qd (qtimes p r (susu a))  = qtimes (qd p) (qu r) (sur a) q+ qtimes p (qd r) (sul a)
\end{spec}

Of course, we should like the convenience of our |w*| operator, at
least for \emph{constructing} polynomials. We need simply prove that |Add| respects
|+|.

%format add = "\F{add}"
%format q* = "\mathbin{\F{\pt}}"
%format _q*_ = "\F\_\!" q* "\!\F\_"
\begin{code}
add : (l m : Nat) -> Add l m (l + m)
add ze     m  = zel
add (su l) m  = sul (add l m)
\end{code}
\begin{code}
_q*_ : forall {l m} -> Qoly l -> Qoly m -> Qoly (l + m)
_q*_ {l}{m} p r = qtimes p r (add l m)
infixr 6 _q*_
\end{code}

Similarly, let us grant ourselves versions of |qk| and |qi| which fix their
degree, and define the exponential.
%format x1 = "\F{\iota}_1"
%format k0 = "\F{\kappa}_0"
%format ^^ = "\F{{}^{\owedge}}"
%format _^^_ = _ ^^ _
\begin{code}
x1 : Qoly 1
x1 = qi

k0 : Nat -> Qoly 0
k0 n = qk n

_^^_ : forall {m} -> Qoly m -> (n : Nat) -> Qoly (n * m)
p ^^ ze = qk 1
p ^^ su n = (p ^^ n) q* p
\end{code}

We may now write polynomials, taking care to use |x1| in the highest degree term,
\[
 |(x1 ^^ 2) q+ k0 2 q* qi q+ qk 1 : Qoly 2|
\]
thus fixing the bound and leaving some slack in the other terms.

We now have a definition of |Qoly|nomials indexed by a bound on their
degree which readily admits a candidate for the forward-difference
operator |qd|.


\section{Stating the testing principle}

Let us be careful to define the conditions under which we expect two
polynomials to be pointwise equal. We shall require a conjunction of
individual equations, hence let us define the relevant logical apparatus:
the unit type and the cartesian product.

%format rewrite = "\mathkw{rewrite}"
%format & = "\D{\times}"
%format _&_ = _ & _
%format / = "\C{,}"
%format _/_ = _ / _
%format fst = "\F{fst}"
%format snd = "\F{snd}"
\oneDecl
\vspace*{ -0.4in}
\begin{code}
record _&_ (S T : Set) : Set where constructor _/_; field fst : S ; snd : T
open _&_ public
\end{code}

To state the condition that polynomials coincide on \(\{i || i < |k|\}\), we may
define:

%format TestEq = "\F{TestEq}"
\begin{code}
TestEq : (k : Nat){n : Nat}(p r : Qoly n) -> Set
TestEq ze      p r =  One
TestEq (su k)  p r =  (ql p qr ze == ql r qr ze) & TestEq k (qu p) (qu r)
\end{code}

We can now state the key lemma that we hope to prove.

%format testLem = "\F{testLem}"
\begin{code}
testLem : (n : Nat)(p r : Qoly n) -> TestEq (su n) p r -> (x : Nat) -> ql p qr x == ql r qr x
\end{code}

Of course, in order to \emph{prove} the testing principle, we shall need
the machinery for constructing proofs of equations.


\section{Some kit for equational reasoning}

It is standard to make use of Agda's mixfix notation for presenting
equational explanations in readable form. I give two ways to take a step,
combining symmetry with transitivity, and one way to finish.
\equalityRewriting

Meanwhile, the following apparatus is useful for building \emph{structural}
explanations of equality between applicative forms.
\equalityTools

For example, let us prove the lemma that any polynomial of degree at most |0| is
constant.

%format qkLem = "\F{kLem}"
\begin{code}
qkLem : (p : Qoly 0)(x y : Nat) -> ql p qr x == ql p qr y
qkLem (qk n)            x y  = refl
qkLem (qu p)            x y  =
  ql qu p qr x               =! refl !>
  ql p qr (su x)             =! qkLem p (su x) (su y) !>
  ql p qr (su y)             <! refl !=
  ql qu p qr y               !!!
qkLem (p q+ r)          x y  =
  ql (p q+ r) qr x           =! refl !>
  ql p qr x + ql r qr x      =! <^ _+_ ^> =$= qkLem p x y =$= qkLem r x y !>
  ql p qr y + ql r qr y      <! refl !=
  ql (p q+ r) qr y           !!!
qkLem (qtimes p r zel)  x y  =
  ql (p q* r) qr x           =! refl !>
  ql p qr x * ql r qr x      =! <^ _*_ ^> =$= qkLem p x y =$= qkLem r x y !>
  ql p qr y * ql r qr y      <! refl !=
  ql (p q* r) qr y           !!!
qkLem (qtimes p r zer)  x y  =
  ql (p q* r) qr x           =! refl !>
  ql p qr x * ql r qr x      =! <^ _*_ ^> =$= qkLem p x y =$= qkLem r x y !>
  ql p qr y * ql r qr y      <! refl !=
  ql (p q* r) qr y           !!!
\end{code}

The steps where the equality proof is |refl| can be omitted, as they follow just
by symbolic evaluation. It may, however, add clarity to retain them.


\section{Proving the testing principle}

Let us now show that the testing principle follows from the as yet
unproven hypothesis that |qd| satisfies its specification:

%format qdLem = qd "\F{Lem}"
\begin{code}
qdLem : forall {n}(p : Qoly (su n)) x -> ql p qr (su x) == ql p qr x + ql qd p qr x
\end{code}

As identified earlier, the key fact is that the test conditions for some |p| and |r| imply the test conditions for |qd p| and |qd r|.

%format testQdLem = "\F{test}" qd "\F{Lem}"
\begin{code}
testQdLem : (k : Nat){n : Nat}(p r : Qoly (su n)) ->
  TestEq (su k) p r -> TestEq k (qd p) (qd r)
\end{code}

Assuming this, we may deliver the main induction.

\begin{code}
testLem ze      p r (q / <>) x         =
  ql p qr x                            =! qkLem p x ze !>
  ql p qr 0                            =! q !>
  ql r qr 0                            <! qkLem r x ze !=
  ql r qr x                            !!!
testLem (su n)  p r (q0 / qs)  ze      =
  ql p qr ze                           =! q0 !>
  ql r qr ze                           !!!
testLem (su n)  p r qs         (su x)  =
  ql p qr (su x)                       =! qdLem p x !>
  ql p qr x + ql qd p qr x
    =! (<^ _+_ ^>  =$=  testLem (su n) p r qs x =$= testLem n (qd p) (qd r) (testQdLem (su n) p r qs) x) !>
  ql r qr x + ql qd r qr x             <! qdLem r x !=
  ql r qr (su x)                       !!!
\end{code}

To establish |testQdLem|, we need to establish equality of
\emph{differences} by cancelling what the differences are added to. We
shall need the \emph{left-cancellation} property of addition.

%format +cancel = + "\F{cancel}"
\begin{code}
+cancel : forall w y {x z} -> w == y -> w + x == y + z -> x == z
\end{code}
\vspace*{ -0.3in}
\begin{code}
testQdLem ze      p r  q          = <>
testQdLem (su k)  p r  (q0 / qs)  =
  +cancel (ql p qr 0) (ql r qr 0) q0 (
    ql p qr 0 + ql qd p qr 0  <! qdLem p 0 !=
    ql p qr 1                 =! fst qs !>
    ql r qr 1                 =! qdLem r 0 !>
    ql r qr 0 + ql qd r qr 0  !!! ) /
  testQdLem k (qu p) (qu r) qs
\end{code}


\section{No confusion, cancellation, decision}

The left-cancellation property ultimately boils down to iterating the
observation that |su| is injective. Likewise, to show that we can
actually decide the test condition, we shall need to show that numeric
equality is decidable, which also relies on the \emph{`no confusion'}
property of the datatype |Nat|---constructors are injective and
disjoint. Back when we worked for Rod, Healfdene Goguen and James
McKinna taught me a reflective method to state and prove a bunch of
constructor properties simultaneously: we define the intended
consequences of an equation between constructor forms, and then show
that those consequences do indeed hold on the
diagonal~\cite{DBLP:conf/types/McBrideGM04}.

%format NoConf = "\F{NoConf}"
%format noConf = "\F{noConf}"
\zeroDecl
\vspace*{ -0.3in}
\begin{code}
NoConf : Nat -> Nat -> Set
NoConf  ze      ze      =  One
NoConf  (su x)  (su y)  =  x == y
NoConf  _       _       =  Zero

noConf : forall {x y} -> x == y -> NoConf x y
noConf {ze}    refl = <>
noConf {su x}  refl = refl
\end{code}

The cancellation property we need follows by an easy induction. Again,
we work along the diagonal, using |noConf| to strip a |su| at each step.

\begin{code}
+cancel ze      .ze      refl refl  = refl
+cancel (su w)  .(su w)  refl q     = +cancel w w refl (noConf q)
\end{code}

In the step case, |q : su (w + x) == su (w + z)|, so |noConf q : (w + x) == (w + z)|.

Meanwhile, we can frame the decision problem for the numeric equation
|x == y| as the question of whether the type has an inhabitant or is
provably empty.

%format Dec = "\D{Dec}"
%format yes = "\C{yes}"
%format no = "\C{no}"
\begin{code}
data Dec (P : Set) : Set where
  yes  : P ->            Dec P
  no   : (P -> Zero) ->  Dec P
\end{code}

The method for deciding equality is just like the usual method for
testing it, except that we generate evidence via |noConf|.

%format decEq = "\F{decEq}"
\begin{code}
decEq : (x y : Nat) -> Dec (x == y)
decEq  ze      ze                        = yes refl
decEq  ze      (su y)                    = no noConf
decEq  (su x)  ze                        = no noConf
decEq  (su x)  (su y)   with  decEq x y
decEq  (su x)  (su .x)  |     yes refl   = yes refl
decEq  (su x)  (su y)   |     no nq      = no \ q -> nq (noConf q)
\end{code}

While we are in a decisive mode, let us show that the test condition is decidable,
just by iterating numerical equality tests.

%format testEq = "\F{testEq}"
\begin{code}
testEq : (k : Nat){n : Nat}(p r : Qoly n) -> Dec (TestEq k p r)
testEq ze      p r = yes <>
testEq (su k)  p r with decEq (ql p qr 0) (ql r qr 0) | testEq k (qu p) (qu r)
... | yes y  | yes z  = yes (y / z)
... | yes y  | no np  = no \ xy -> np (snd xy)
... | no np  | _      = no \ xy -> np (fst xy)
\end{code}

We can now give our testing principle a friendly user interface, incorporating
decision.


\section{The testing deliverable}

Much as with |NoConf|, we can compute for any pair of polynomials a
statement which might be of interest---if the test condition holds, we
state that the polynomials are pointwise equal---and we can prove that
statement, because deciding the test condition delivers the evidence
we need.

%format TestStmt = "\F{TestStmt}"
%format testStmt = "\F{testStmt}"
\begin{code}
TestStmt : (n : Nat)(p q : Qoly n) -> Set
TestStmt n p r with testEq (su n) p r
... | yes qs  = (x : Nat) -> ql p qr x == ql r qr x
... | no _   = One

testStmt : {n : Nat}(p r : Qoly n) -> TestStmt n p r
testStmt {n} p r with testEq (su n) p r
... | yes qs  = testLem n p r qs
... | no _    = <>
\end{code}


\section{Associativity, Commutativity, Distributivity}

Before we can tackle the correctness of |qd|, we shall need some basic facts
about |+| and |*|. There is little surprising about these proofs, but I include
them for completeness.

Associativity of addition follows by an induction which triggers computation.
%format +assoc = "\F{+assoc}"
\begin{code}
+assoc : (l m n : Nat) -> (l + m) + n == l + (m + n)
+assoc ze      m n  = refl
+assoc (su l)  m n  = <^ su ^> =$= +assoc l m n
\end{code}

Commutativity of addition follows from lemmas which simulate the behaviour of
addition by recursion on the second argument, oriented right-to-left.
%format +ze = "\F{+ze}"
%format +su = "\F{+su}"
%format +comm = "\F{+comm}"
\begin{code}
+ze : {n : Nat} -> n == n + ze
+ze {ze}         =  refl
+ze {su n}       =  <^ su ^> =$= +ze

+su : (m n : Nat) -> su (m + n) == m + su n
+su ze      n    =  refl
+su (su m)  n    =  <^ su ^> =$= +su m n

+comm : (m n : Nat) -> m + n == n + m
+comm ze      n  =  +ze
+comm (su m)  n  =  su (m + n)  =! <^ su ^> =$= +comm m n !>
                    su (n + m)  =! +su n m !>
                    n + su m    !!!
\end{code}

We shall also need the distributivity of multiplication over
addition. James McKinna taught me to prepare by proving a
lemma that transposes the middle of a sum of sums.
%format mid4 = "\F{mid4}"
\begin{code}
mid4 : (w x y z : Nat) -> (w + x) + (y + z) == (w + y) + (x + z)
mid4 w x y z =
  (w + x) + (y + z)   =! +assoc w x (y + z) !>
  w + (x + (y + z))   =! <^ _+_ w ^> =$= (  x + (y + z)  <! +assoc x y z !=
                                            (x + y) + z  =! <^ _+_ ^> =$= +comm x y =$= <^ z ^> !>
                                            (y + x) + z  =! +assoc y x z !>
                                            y + (x + z)  !!!) !>
  w + (y + (x + z))   <! +assoc w y (x + z) !=
  (w + y) + (x + z)   !!!
\end{code}

The step case of left-distributivity, is just such a transposition.
%format *dist+ = "\F{*dist+}"
%format +dist* = "\F{+dist*}"
\begin{code}
*dist+ : (a b c : Nat) -> a * (b + c) == a * b + a * c
*dist+ ze      b c  = refl
*dist+ (su a)  b c  =
  a * (b + c) + (b + c)       =! <^ _+_ ^> =$= *dist+ a b c =$= <^ (b + c) ^> !>
  (a * b + a * c) + b + c     =! mid4 (a * b) (a * c) b c !>
  (a * b + b) + (a * c + c)   !!!
\end{code}

Meanwhile, the strategic insertion of a |ze| will bring the step case of right-distributivity also into this form.
\begin{code}
+dist* : (a b c : Nat) -> (a + b) * c == a * c + b * c
+dist* ze b c = refl
+dist* (su a) b c =
  (a + b) * c + c             =! <^ _+_ ^> =$= +dist* a b c =$= +ze !>
  (a * c + b * c) + (c + ze)  =! mid4 (a * c) (b * c) c ze !>
  (a * c + c) + (b * c + ze)  <! <^ _+_ (su a * c) ^> =$= +ze !=
  su a * c + b * c      !!!
\end{code}

We need neither associativity nor commutativity of multiplication, as
our products are binary, and the definition of |qd| preserves left-to-right
order.  Thus equipped with rather less than the ring theory of the
integers, we are none the less ready to proceed.


\section{Correctness of |qd|}

It is high time we sealed the argument with a proof that |qd| satisfies its
specification, really computing the difference between |qu p| and |p|.

\begin{spec}
qdLem : forall {n}(p : Qoly (su n)) x -> ql p qr (su x) == ql p qr x + ql qd p qr x
\end{spec}

The basic plan is to do induction over the computation of |qd|, then
basic algebraic rearrangement using the above facts. It is thoroughly
unremarkable, if a little gory in places.

Constants, identity and shifting are very simple.
Addition yet again requires us to swap the middle of a sum of sums.
\begin{code}
qdLem (qk n)    x = n =! +ze !> n + 0 !!!
qdLem qi        x = 1 + x =! +comm 1 x !> x + 1 !!!
qdLem (qu p)    x = qdLem p (su x)
qdLem (p q+ r)  x =
  ql p qr (su x) + ql r qr (su x)                          =! <^ _+_ ^> =$= qdLem p x =$= qdLem r x !>
  (ql p qr x + ql qd p qr x) + (ql r qr x + ql qd r qr x)  =! mid4 (ql p qr x) (ql qd p qr x) (ql r qr x) (ql qd r qr x) !>
  ql p q+ r qr x + ql qd (p q+ r) qr x                     !!!
\end{code}

The edge cases of multiplication require the constancy of zero-degree polynomials. The
two subproblems are mirror images.
\begin{code}
qdLem (qtimes p r zel) x =
  ql p qr (su x) * ql r qr (su x)                       =! <^ _*_ ^> =$= qkLem p (su x) 0 =$= qdLem r x !>
  ql p qr 0 * (ql r qr x + ql qd r qr x)                =! *dist+ (ql p qr 0) (ql r qr x) (ql qd r qr x) !>
  ql p qr 0 * ql r qr x + ql p qr 0 * ql qd r qr x      <! <^ _+_ ^> =$= (<^ _*_ ^> =$= qkLem p x 0 =$= refl) =$= refl !=
  ql p qr x * ql r qr x + ql p qr 0 * ql qd r qr x      !!!
\end{code}
\begin{code}
qdLem (qtimes p r zer) x =
  ql p qr (su x) * ql r qr (su x)                       =! <^ _*_ ^> =$= qdLem p x =$= qkLem r (su x) 0 !>
  (ql p qr x + ql qd p qr x) * ql r qr 0                =! +dist* (ql p qr x) (ql qd p qr x) (ql r qr ze) !>
  ql p qr x * ql r qr 0 + ql qd p qr x * ql r qr 0      <! <^ _+_ ^> =$= (<^ _*_ (ql p qr x) ^> =$= qkLem r x 0) =$= refl !=
  ql p qr x * ql r qr x + ql qd p qr x * ql r qr 0      !!!
\end{code}

The only tricky case is the nondegenerate multiplication. Here, I am
careful about when to apply the induction hypothesis for |r|, as |ql r
qr (su x)| occurs on both sides: I wait until after it has been
duplicated by distribution, then rewrite only one of the copies.
\begin{code}
qdLem (qtimes p r (susu a)) x =
  ql p qr (su x) * ql r qr (su x)              =! <^ _*_ ^> =$= qdLem p x =$= refl !>
  (ql p qr x + ql qd p qr x) * ql r qr (su x)  =! +dist* (ql p qr x) (ql qd p qr x) (ql r qr (su x)) !>
  ql p qr x * ql r qr (su x) + ql qd p qr x * ql r qr (su x)
    =! <^ _+_ ^> =$= (<^ _*_ (ql p qr x) ^> =$= qdLem r x) =$= refl !>
  ql p qr x * (ql r qr x + ql qd r qr x) + ql qd p qr x * ql r qr (su x)
     =! <^ _+_ ^> =$= *dist+ (ql p qr x) (ql r qr x) (ql qd r qr x) =$= refl !>
  (ql p qr x * ql r qr x + ql p qr x * ql qd r qr x) + ql qd p qr x * ql r qr (su x)
     =! +assoc (ql p qr x * ql r qr x) _ _ !>
  ql p qr x * ql r qr x + ql p qr x * ql qd r qr x + ql qd p qr x * ql r qr (su x)
     =! <^ _+_ (ql p qr x * ql r qr x) ^> =$= +comm (ql p qr x * ql qd r qr x) (ql qd p qr x * ql r qr (su x)) !>
  ql p qr x * ql r qr x + ql qd p qr x * ql r qr (su x) + ql p qr x * ql qd r qr x !!!
\end{code}
%if False
\begin{code}
qdLem (qsum p) x = refl
\end{code}
%endif

The proof boils down to rewriting by |qkLem| and inductive hypotheses,
then elementary ring-solving: the latter could readily be disposed of
by a reflective tactic in the style of Boutin~\citep{DBLP:conf/tacs/Boutin97}.


\section{Summing up}

We have proven our polynomial testing principle, but we have rather lost
sight of the problem which led us to it---proving results about \emph{summation}.
\sumDefn

Now, our language of |Qoly|nomials with constants in
|Nat| does not admit summation: that would require us to
work with rationals at considerable additional effort. However,
we can just extend the \emph{syntax} with summation, \emph{incrementing
degree}, and give |sum| as its semantics.
%format qsum = "\C{\sigma}"
%format QQUADS = "\qquad\qquad\qquad"
\begin{spec}
qsum : forall {n} -> Qoly n -> Qoly (su n)
ql qsum p qr x = sum ql p qr x
\end{spec}

Of course, we are then obliged to augment the rest of the development.
The non-zero index of |qsum| means that no obligation arises for |qkLem|.
Meanwhile, by careful alignment, |sum| is exactly the notion of `integration'
corresponding to forward-difference |qd|, hence the extension of |qd|
is direct and the corresponding case of |qdLem| trivial.

\begin{spec}
qd     (qsum p)    = p
qdLem  (qsum p) x  = refl
\end{spec}

And with those seven extra lines, we are ready to prove classic results by
finitary testing.

%format triangle = "\F{triangle}"
%format square = "\F{square}"
%format cubes = "\F{cubes}"
\begin{code}
triangle  :  (x : Nat) -> 2 * sum (\ i -> i) (su x) == x * (x + 1)
triangle  =  testStmt (k0 2 q* qu (qsum x1)) (x1 q* (x1 q+ qk 1))

square    :  (x : Nat) -> sum (\ i -> 2 * i + 1) x == x ^ 2
square    =  testStmt (qsum (k0 2 q* x1 q+ qk 1)) (x1 ^^ 2)

cubes     :  (x : Nat) -> sum (\ i -> i ^ 3) x == (sum (\ i -> i) x) ^ 2
cubes     =  testStmt (qsum (x1 ^^ 3)) (qsum x1 ^^ 2)
\end{code}

In effect, it is enough for us to say so, and the machine will see for
itself.  The essence of proof is to explain how infinitary statements
can be reduced to a finitary collection of tests. By exposing an
intrinsic notion of degree for polynomials, their very form tells us
how to test them. What is unusual is that these problems do not
require any algebraic calculation or symbolic evaluation, just
arithmetic. In some sense, we have found a basis from which testing
can reveal the absence of bugs, not just, as Dijkstra observed, their
presence~\cite{dijk}.  Rod Burstall's casual remark about trying three examples
has exposed a remarkably simple way to see truths which are often
presented as subtle. Indeed, Rod's guidance it is that has me striving
for vantage points from which the view is clear. This paper is for
him.



%if False

\section{Detritus}

\newcommand{\shift}[1]{#1\!\uparrow} 



Polynomials are closed under composition: we can construct \(p\cdot
q\) by substituting \(q\) for \(\iota\) in \(p\), so that 
\[
  (p\cdot q)\:x = p\:(q\:x)
\]
In particular, we can \emph{shift} a polynomial by one
\[
  (\shift{p}) = p\cdot(\con{1}\pp\iota)
\qquad
  \shift{p}\:x = p\:(1+x)
\]

The \emph{forward-difference} operator \(\fd\) should satisfy the specification
\[
  \shift{p} = p \pp \fd p \qquad\mbox{i.e.,}\quad p\:(1+x) = p\:x + \fd p\:x
\]
but can we define it? Clearly
\[
  \fd\con{n} = \con{0} \qquad \fd\id = \con{1}
\]

Rearranging sums is enough to see
\[
\begin{array}[b]{l@@{\;=\;}l@@{\;\pp\;}l}
\shift{p} & p & \fd p \\
\shift{q} & q & \fd q \\
\hline
\shift{(p\pp q)} & (p\pp q) & \fd (p\pp q)
\end{array}
\qquad\mbox{so}\quad \fd (p\pp q) = \fd p \pp \fd q
\]

What about \(\fd(p\pt q)\)? Making use of the specification for \(\fd p\) and \(\fd p\)
and a little algebra, we have
\[\begin{array}{l@@{\quad=\quad}l}
  \shift{(p\pt q)} & \shift{p}\pt\shift{q} \\
   & (p\pp \fd p)\pt\shift{q} \\
   & p\pt\shift{q}\pp \fd p\pt\shift{q}\\
   & p\pt(q\pp\fd q)\pp \fd p\pt\shift{q} \\
   & p\pt q \pp p\pt\fd q \pp \fd p\pt\shift{q} \\
   & p\pt q \pp (\fd p\pt\shift{q} \pp p\pt\fd q)
\end{array}\]
so we can take
\[
\fd(p\pt q) = \fd p\pt\shift{q} \pp p\pt\fd q
\]

The specification of \(\fd p\) gives us an easy inductive proof of
\[
  p\:n = p\:0 + \sum{i < n}\fd p\:i
\]
The base for \(n=0\) is trivial. Now observe that
\[
p\:(1+n) = \shift{p}\:n = (p\pp\fd)\:n = p\:n + \fd p\:n =
 p\:0 + \sum{i < n}\fd p\:i + \fd p\: n =
 p\:0 + \sum{i < 1+n}\fd p\:i
\]

It is not hard to check that 
\begin{itemize}
\item if \(\dgr{p}=0\) then \(p = \con{p\:0}\)
\item if \(\dgr{p}=1+n\) then \(\dgr{\fd p}=n\).
\end{itemize}

Now, let us see why
\[
\mbox{if}\quad\dgr{p}\vee\dgr{q}\le n\quad
\mbox{and}\quad p\:i=q\:i \;\mbox{for}\;i\in\{0,\ldots,n\}\quad
\mbox{then}\quad p = q
\]
In the case when \(n=0\),
\[
p = \con{p\:0} = \con{q\:0} = q
\]
Suppose, inductively, that the result holds for \(n\). Let us establish it for
\(1 + n\). As
\[
  p\:i=q\:i \;\mbox{for}\;i\in\{0,\ldots,1+n\}
\]
we have
\[
  p\:0 = q\:0 \quad\mbox{and}\quad
  \shift{p}\:i=\shift{q}\:i \;\mbox{for}\;i\in\{0,\ldots,n\}
\]
so
\[
  (p\pp\fd p)\:i=(q\pp\fd q)\:i \;\mbox{for}\;i\in\{0,\ldots,n\}
\]
and, as \(p\:i=q\:i\) in that range
\[
  \fd p\:i=\fd q\:i \;\mbox{for}\;i\in\{0,\ldots,n\}
\]
hence, by inductive hypothesis,
\[
  \fd p = \fd q
\]
but, now we have
\[
p\:n = p\:0 + \sum_{i<n}\fd p\:i = q\:0 + \sum_{i<n}\fd q\:i = q\:n
\]




Let us work with the natural numbers, defined inductively as follows.

Our polynomial language will also contain a \emph{summation} operator,
encoding the following higher-order function:
%format diff = "\F{\Delta}"
Note, that |sum f n| is \(\sum_{|i| < |n|}|f i|\), so we allow for
zero-length sequences, but we shall need to take care to avoid off-by-one
errors when summing up to \emph{and including} \(n\). We expect that if
|f| is polynomial of degree \(d\). then |sum f| is polynomial of degree
\(d+1\). Summation is a little like \emph{integration} in that respect.
The corresponding notion of differentiation is \emph{forward-difference},
specified informally as follows
\[|del f x| = |f (su x)| - |f x|\]
The |del| operator decrements degree, and, in particular,
\[|del (sum f) x| = |sum f (su x)| - |sum f x| = |f x + sum f x| - |sum f x| = |f x|\]
I deliberately chose the `strictly below \(n\)' definition of |sum|
to ensure compatibility with forward-difference. The alternative
`up to \(n\)' definition is similarly compatible with
\emph{backward}-difference, |f n - f (n - 1)|, but when working with
|Nat|, the |su|ccessor operation is much less trouble than its partial
inverse. Indeed, working with inductively defined natural numbers, one
learns to avoid subtraction like the plague.

Constants, identity, addition, multiplication and summation will allow
us to give a semantics to a simple language of polynomial expressions.


\section{Polynomial expressions}
%endif

\bibliography{Ornament}   % name your BibTeX data base

\end{document}
