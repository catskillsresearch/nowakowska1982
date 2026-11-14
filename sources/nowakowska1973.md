---
book: Language of Motivation and Language of Actions (Mouton, 1973)
cite: Nowakowska73a
verification_status: draft
ranges:
  - section: 2.1.4
    file: nowakowska_1973_section214.md
    pages_approx: 52–70
  - section: 2.2.4
    file: nowakowska_1973_section_224.md
    pages: 79–89
  - section: 5.3
    file: nowakowska_1973_section_53.md
    pages: 200–210
note: >-
  Page-anchored ingest of scanned OCR ranges used by Batch B
  (MotCalc sample + promise CF proofs). Full book is not transcribed.
---

# Nowakowska (1973) — scanned ranges

Citation: [@Nowakowska73a]. OCR drafts live in the linked section files;
figures under `figures/nowakowska1973/`.


---

# §2.1.4. Rules of semantic inference (sampled MotCalc rules)

<!-- source_file: nowakowska_1973_section214.md -->

# Transcription (LLM vision OCR)


<!-- page 1 -->

MOTIVATIONAL CALCULUS

Next, the semantic implication satisfies the law of contraposition, i.e. if

$$
A \xrightarrow{s} B
$$

then

$$
\sim B \xrightarrow{s} \sim A.
$$

Indeed, $A \& \sim B$ and $\sim B \& \sim \sim A$, which is the same as $\sim B \& A$, are either both admissible, or both inadmissible.

In the presentation of the specific semantic implications, we shall make use of the logical functors $\&$ and $\lor$, whenever practicable, in order to combine several formulae into one. Thus, we shall write

$$
A \xrightarrow{s} B \& C
$$

whenever $A \xrightarrow{s} B$ and $A \xrightarrow{s} C$. Similarly, we shall write

$$
(1) \quad A \lor B \xrightarrow{s} C
$$

if $A \xrightarrow{s} C$ and $B \xrightarrow{s} C$. Note that the formula (1) can usually be interpreted only as a conventional way of expressing the fact that $A \xrightarrow{s} C$ and $B \xrightarrow{s} C$, as the utterance $A \lor B$ may be inadmissible.

Thus, unless used for propositional arguments, the meaning of the symbols $\lor$ and $\&$ in the formulae for semantic implications will be as follows: the symbol $\&$ appearing on the right hand side and the symbol $\lor$ appearing on the left hand side should be interpreted as used in the conventional way of combining several implications into one, as described above. The symbol $\lor$ on the right hand side will denote the usual alternative in the logical sense, while the symbol $\&$ on the left hand side, the linguistic conjunction of sentences.

Finally, double implication

$$
A \xleftrightarrow{s} B
$$

will be used to express the fact that $A \xrightarrow{s} B$ and $B \xrightarrow{s} A$.

### 2.1.4. *Rules of semantic inference for some motivational functors*

#### 2.1.4.1. *I know, I am certain, I think*

In the formulae below, we shall denote by $K$, $Cr$, and $T$ the functors ‘I know that’, ‘I am certain that’, and ‘I think that’. Each of these functors applies to propositional arguments. We shall interpret ‘I know that $p$’, to be denoted by $Kp$, as synonymous with ‘I know that $p$ is true’, and we exclude from the consideration the use of ‘I know’ as in the sentence *I know him quite well*, where the argument is not a proposition.

The functor $K$ can be negated in two ways. First, as mentioned above, we denote by $\sim Kp$ the sentence ‘It is not true that I know that $p$’. Second, we shall introduce the

<!-- page 2 -->

MOTIVATIONAL CALCULUS

functor $K'$, to be read as ‘I don't know’, applicable to two or more propositional arguments. Accordingly, $K'(p, q)$ is to be read as ‘I don't know whether $p$ or $q$’.

Two types of negation will also be used for the functor $T$: the symbol $\sim Tp$ will stand for ‘It is not true that I think that $p$’, and we shall introduce the functor $T'$, to be read as ‘I don't think that’. The functor $T$ (and also $T'$) is interpreted here as an expression of judgment, as used in *I think that he is ill*, and not as referring to the process of thinking, as in *I think of him quite often*.

We can now proceed with the presentation of the semantic inference rules. First, it seems quite obvious that we may formulate the following three laws:

$$
\begin{aligned}
(2) \quad & K(p \ \& \ q) \xrightarrow{s} Kp \ \& \ Kq \\
(3) \quad & Cr(p \ \& \ q) \xrightarrow{s} Cr\,p \ \& \ Cr\,q \\
(4) \quad & T(p \ \& \ q) \xrightarrow{s} Tp \ \& \ Tq.
\end{aligned}
$$

The justification of the above formulae is quite simple; we shall illustrate it by analysing the first of them. Thus, one has to show that $K(p \ \& \ q) \xrightarrow{s} Kp$ and $K(p \ \& \ q) \xrightarrow{s} Kq$. Indeed, consider the sentence of the form $K(p \ \& \ q) \ \& \ \sim Kp$, i.e. ‘I know that both $p$ and $q$ (are true), but it is not true that I know that $p$ (is true)’. This sentence seems to be inadmissible, no matter what $p$ and $q$ are, which shows, by definition of the symbol $\xrightarrow{s}$, that $K(p \ \& \ q) \xrightarrow{s} Kp$. Similarly, $K(p \ \& \ q) \xrightarrow{s} Kq$, which yields formula (2).

As already mentioned, formula (2) may be interpreted as a rule, which allows us to make the inference $K_3 p \ \& \ K_3 q$ (‘he knows that $p$ and he knows that $q$’) from the utterance $K(p \ \& \ q)$. In other words, if someone utters a sentence of the form ‘I know that $p$ and $q$’, one may infer he knows that $p$ and he also knows that $q$.

In the sequel, when discussing particular semantic implications, we shall sometimes refer to them as the inference rules which lead from sentences expressed in the first person singular to propositions expressed in the third person singular asserting something about the speaker's intentions.

There is an interesting problem of converses to (2), (3), and (4). With the provisions discussed below, we have

$$
\begin{aligned}
(5) \quad & Kp \ \& \ Kq \xrightarrow{s} K(p \ \& \ q) \\
(6) \quad & Cr\,p \ \& \ Cr\,q \xrightarrow{s} Cr(p \ \& \ q) \\
(7) \quad & Tp \ \& \ Tq \xrightarrow{s} T(p \ \& \ q).
\end{aligned}
$$

The first of these laws, however, is true only if ‘I know’ is interpreted as intended, i.e. as an assertion of truth, and not as used sometimes instead of functors such as ‘I heard that’, ‘I know that it is generally believed that’, etc.

The second of these laws, namely the inference concerning the functor $Cr$, can be made only if the sentences $Cr\,p$ and $Cr\,q$ are combined into one utterance, i.e. if $Cr\,p$

<!-- page 3 -->

MOTIVATIONAL CALCULUS

& $Cr\,q$ stands for linguistic rather than logical conjunction. Generally, if the sentences $Cr\,p$ and $Cr\,q$ are uttered on two different occasions, one cannot infer that $Cr(p \ \& \ q)$, i.e. that the speaker is certain that both $p$ and $q$. In fact, by observing when we have $Cr\,p \ \& \ Cr\,q$ in the logical but not in the linguistic sense, and $\sim Cr(p \ \& \ q)$, one can obtain some information on how high the (subjective) probability of an event must be for a person to assert that he is certain that this event will occur.

Indeed, imagine two events, say $A$ and $B$, with probabilities $a = P(A)$ and $b = P(B)$, and assume that $A$ and $B$ are independent, so that the probability of the joint occurrence $A \cap B$ is $ab$. Suppose now that the speaker knows the probabilities $a$ and $b$, and also knows that the events $A$ and $B$ are independent. We may postulate the existence of a number $r$ (possibly depending on the speaker), such that he will apply the functor ‘I am certain that’ to a description of an event only if his subjective probability of this event is at least $r$. If the subjective and objective probabilities did in fact coincide, and if it turned out that the subject applies the functor $Cr$ to events $A$ and $B$ when confronted with them separately, but does not apply this functor when analysing the possibilities of the joint occurrence $A \cap B$, we would know that $a \ge r$, $b \ge r$, and $ab < r$, that is,

$$
(8) \quad ab < r \le \min(a, b).
$$

A series of observations for different events $A$, $B$ should allow us to obtain reasonable estimates of the number $r$.

Of course, when performing this experiment one would have to take into account the fact that the subjective and objective probabilities do not coincide, and use instead of (8) the corresponding bounds obtained with the help of well-known relations between subjective and objective probabilities.$^{8}$ Thus, if $f(x)$ is the subjective probability of an event whose objective probability is $x$, the relation (8) would be replaced by

$$
(9) \quad f(ab) < r \le \min\bigl(f(a), f(b)\bigr).
$$

Similar restrictions apply to rule (7); thus, (7) is true if the symbol $\&$ on the left hand side is interpreted as linguistic conjunction rather than logical conjunction.

Let us now analyse some rules concerning the negation ‘I don't know’. First, we have$^{9}$

$$
(10) \quad K'(p, q) \xrightarrow{s} K'(q, p),
$$

since the sentence ‘I don't know whether $p$ or $q$, but it is not true that I don't know whether $q$ or $p$’ is inadmissible.

$^{8}$ See for instance C.H. Coombs, R.M. Dawes, and A. Tversky, *Mathematical Psychology* (Prentice Hall, Englewood Cliffs, 1970).

$^{9}$ A system for functors ‘I know that’ and ‘I believe that’ (considered in the next section) has been developed by J. Hintikka (see *Knowledge and Belief*). As already pointed out, his system differs primarily in the interpretation of the concept of implication used. Also, Hintikka considers the sentence ‘I do not know whether $p$’, which in our notation corresponds to $K'(p, \sim p)$.

<!-- page 4 -->

MOTIVATIONAL CALCULUS

Next,

$$
(11) \quad K'(p, q) \xrightarrow{s} \sim Kp,
$$

and by (10) also

$$
(12) \quad K'(p, q) \xrightarrow{s} \sim Kq.
$$

Combining (11) and (12) we may write

$$
(13) \quad K'(p, q) \xrightarrow{s} \sim Kp \ \& \ \sim Kq.
$$

The three rules above state that from the utterance ‘I don't know whether $p$ or $q$’ one can infer that it is not true that the speaker knows that $p$, and it is not true that the speaker knows that $q$.

By contraposition of (11) we have

$$
(14) \quad Kp \xrightarrow{s} \sim K'(p, q),
$$

i.e. if the speaker knows that $p$, then it is not true that he doesn't know whether $p$ or $q$.

We may also state the rule

$$
(15) \quad \sim K'(p, q) \xrightarrow{s} K_3 p \lor K_3 q.
$$

Here it is essential that the subscript 3 is used on the right hand side, as the alternative $Kp \lor Kq$ is, in general, not admissible (this point has already been discussed in preceding sections).

To verify (15) analyse the utterance

$$
\sim K'_3(p, q) \ \& \ \sim(K_3 p \lor K_3 q)
$$

that is,

$$
\sim K'_3(p, q) \ \& \ \sim K_3 p \ \& \ \sim K_3 q;
$$

in words: ‘It is not true that he doesn't know whether $p$ or $q$, but it is also not true that he knows that $p$ and it is not true that he knows that $q$’.

Regarding the functors $Cr$ and $T$ we have

$$
(16) \quad Cr\,p \xrightarrow{s} \sim T\,\sim p,
$$

or, by law of contraposition (changing $p$ and $\sim p$):

$$
(17) \quad Tp \xrightarrow{s} \sim Cr\,\sim p.
$$

Thus, if someone claims ‘I am certain that $p$’, then it is not true that he thinks that not $p$. Indeed, the sentence ‘I am certain that $p$, but I think that not $p$’ is not admissible.

Next, we have

$$
(18) \quad Tp \xrightarrow{s} T'\,\sim p.
$$

or, by law of contraposition (changing $p$ and $\sim p$):

<!-- page 5 -->

MOTIVATIONAL CALCULUS

$$
(19) \quad \sim T'p \xrightarrow{s} \sim T\,\sim p
$$

since the sentence ‘It is not true that I don’t think that $p$, but I think that not $p$’ is inadmissible. Consider for instance the sentence *It is not true that I don’t think he’s dead, but I think that he is alive.*

Substituting $p \ \& \ q$ and $p \lor q$ for $p$ in (18) and using de Morgan’s laws one obtains

$$
\begin{aligned}
(20) \quad & T(p \ \& \ q) \xrightarrow{s} T'(\sim p \lor \sim q) \\
(21) \quad & T(p \lor q) \xrightarrow{s} T'(\sim p \ \& \ \sim q).
\end{aligned}
$$

It ought to be noticed, however, that not all sentences of the form $T(p \lor q)$ are admissible, as the functor ‘I think’ implies a degree of doubt; thus, it cannot be used for the case when $p \lor q$ is a tautology, such as $p \lor \sim p$. This may be illustrated by a sentence such as *I think that their child is either a boy or a girl*, which can be uttered only as a joke, or else in rather unusual circumstances.

Furthermore, we have

$$
(22) \quad T'p \ \& \ T'q \xrightarrow{s} T'(p \lor q),
$$

and a modified version of the converse to (18):

$$
(23) \quad T'p \xrightarrow{s} \sim Tp.
$$

(It may be doubted, however, that the right hand side in (23) can be replaced by $T\,\sim p$, the latter being perhaps too strong. Thus, someone who says *I don’t think it will rain tomorrow* will agree that it is false that he thinks that it will rain, but might object to phrasing it that he thinks it won’t rain.)

#### 2.1.4.2. *I believe, I doubt*

We shall denote by $B$, $B'$, and $D$ the functors ‘I believe that’, ‘I don’t believe that’, and ‘I doubt that’. These functors, as the functors considered in 2.1.4.1, are applicable to propositional arguments.

We list below several semantic implications for the functors $B$, $B'$, and $D$, connecting these functors with conjunction and alternative.

Regarding functor $B$ we have$^{10}$

$$
\begin{aligned}
(24) \quad & B(p \ \& \ q) \xleftrightarrow{s} Bp \ \& \ Bq \\
(25) \quad & B(p \lor q) \xrightarrow{s} T'(\sim p \ \& \ \sim q).
\end{aligned}
$$

[^10]: It is worth mentioning that using the functors $B$ and $K$, Hintikka (in *Knowledge and Belief*) introduces the concepts of *doxastic* and *epistemic* implications. According to him, $p$ implies $q$ *doxastically* (see p. 76) if the sentence $B(p \ \& \ \sim q)$ is indefensible, and $p$ implies $q$ *epistemically* (see p. 79) if the sentence $K(p \ \& \ \sim q)$ is indefensible. Hintikka introduces the first of these concepts for the purpose of analysing Moor’s problem of saying and disbelieving, i.e. in an attempt to explain why a sentence of the form ‘$p$, but I do not believe that $p$’ is absurd.

<!-- page 6 -->

MOTIVATIONAL CALCULUS

For the functor $B'$ we have, in general

$$
(26) \quad B'p \xrightarrow{s} T\,\sim p.
$$

Substituting the conjunction $p \ \& \ q$ and the alternative $p \lor q$ for $p$ in (26), and using de Morgan's laws, we obtain

$$
\begin{aligned}
(27) \quad & B'(p \ \& \ q) \xrightarrow{s} T(\sim p \lor \sim q) \\
(28) \quad & B'(p \lor q) \xrightarrow{s} T(\sim p \ \& \ \sim q).
\end{aligned}
$$

Moreover,

$$
(29) \quad B'p \ \& \ B'q \xrightarrow{s} B'(p \lor q) \ \& \ B(\sim p \ \& \ \sim q).
$$

Finally, for functor $D$ we have in general

$$
(30) \quad Dp \xrightarrow{s} T'p
$$

and also

$$
(31) \quad Dp \ \& \ Dq \xrightarrow{s} D(p \lor q).
$$

Of these rules, (25) and (29) seem to be most interesting. Concerning (25), it appears that if someone claims that he believes that $p$ or $q$, one cannot infer that he believes $p$, or that he believes $q$, and one can only infer that he has some doubts regarding the conjunction $\sim p \ \& \ \sim q$. Thus, when three candidates, say $A$, $B$, and $C$ run for an election, $C$ having a very small chance of winning, a person might well say *I believe that either $A$ or $B$ will win*; it implies that he doesn't think that $C$ will win, but does not imply that he believes that $A$ will win, or that he believes that $B$ will win.

Next, (29) is a shortened version of two implications, $B'p \ \& \ B'q \xrightarrow{s} B'(p \lor q)$ and $B'p \ \& \ B'q \xrightarrow{s} B(\sim p \ \& \ \sim q)$. To illustrate this, one can analyse the inference which can be drawn from an utterance such as *I don't believe that rabies can be cured by taking aspirin, and I don't believe that they can be cured by uttering magic spells*.

It seems that the legitimate inference is that the speaker does not believe that rabies can be cured by either taking aspirin or uttering magic spells; also, one may infer that he believes that rabies cannot be cured by taking aspirin, and that they cannot be cured by uttering magic spells.

#### 2.1.4.3. *Some problems of ordering epistemic functors*

In Chapter 1 we discussed the problem of ordering the functors such as $K$, $Cr$, $T$, $B$, and $D$ considered above, and also other functors of the same class, such as ‘I am convinced that’, ‘I suppose that’ (possibly modified by intensional functors, e.g. ‘I am rather certain that’, etc). It was suggested that to each of these functors there corresponds an interval on the scale of subjective probability. Clearly, if $I_F$ and $I_G$ are intervals on the subjective probability scale corresponding to functors $F$ and $G$, then the relation $I_F \subset I_G$ implies the semantic inference rule $Fp \xrightarrow{s} Gp$. Assigning to each

<!-- page 7 -->

MOTIVATIONAL CALCULUS

Assigning to each of the functors the midpoint of the interval corresponding to it, we arrive at an ordering of functors of the considered class.

There is, however, a more interesting way of arriving at an ordering of the considered class of functors. Intuitively, we shall try to devise a method of ordering these functors according to the ‘strength’ of conviction which they represent.

Note first that the most natural way of ordering functors, according to which $F$ precedes $G$ if $Fp \xrightarrow{s} Gp$ may be inapplicable, for there may exist pairs $F$, $G$ such that neither $Fp \xrightarrow{s} Gp$ nor $Gp \xrightarrow{s} Fp$. One could argue, for instance, that such a pair of functors is $K$ and $T$, the sentence $Kp$ being too definite to imply the rather vague $Tp$. Indeed, the sentence $Kp \ \& \ \sim Tp$ is rather admissible (compare the somewhat heated denial: *it is not true that I think that hepatitis is an unpleasant disease; I know it*).

A possible approach to the problem of ordering might be as follows.

Consider the inference schemes from propositional calculus, or from traditional logic, such as

$$
\begin{array}{ccc}
\begin{array}{c}
\vDash p \Rightarrow q \\
\vDash p \\
\hline
\vDash q
\end{array}
&
\text{or}
&
\begin{array}{c}
\vDash p \Rightarrow q \\
\vDash \sim q \\
\hline
\vDash \sim p
\end{array}
\end{array}
$$

or, say Barbara and Celarent modes$^{11}$

$$
\begin{array}{ccc}
\begin{array}{c}
\text{Every } M \text{ is } P \quad (MaP) \\
\text{Every } S \text{ is } M \quad (SaM) \\
\hline
\text{Every } S \text{ is } P \quad (SaP)
\end{array}
&
&
\begin{array}{c}
\text{No } M \text{ is } P \quad (MeP) \\
\text{Every } S \text{ is } M \quad (SaM) \\
\hline
\text{No } S \text{ is } P \quad (SeP)
\end{array}
\end{array}
$$

Suppose now that with each of these inference schemata we associate the set of semantic inference rules obtained as follows: we apply functors from among $K$, $Cr$, $T$, $B$ to each of the premises, and take as the left hand side of the semantic implication the conjunction of sentences thus obtained. Such a conjunction semantically implies the conclusion of the original inference scheme, to which a functor from the set $\{K, Cr, B, T\}$ is applied. For instance, from the inference scheme

$$
\begin{array}{c}
\vDash p \Rightarrow q \\
\vDash p \\
\hline
\vDash q
\end{array}
$$

we obtain semantic inference rules such as

$$
\begin{aligned}
(32) \quad & K(p \Rightarrow q) \ \& \ Cr\,p \xrightarrow{s} Cr\,q \\
(33) \quad & T(p \Rightarrow q) \ \& \ Bp \xrightarrow{s} Tq.
\end{aligned}
$$

$^{11}$ See for instance F.H. Parker and H.B. Veatch, *Logic as a Human Instrument* (Harper and Bros., New York, 1959), 302–303 (where, however, no traditional names of syllogisms are given). For the list of names, see K. Pasenkiewicz, *Logika ogólna* (General logic), in Polish (Warszawa, PWN, 1968), 157–158.

<!-- page 8 -->

Similarly, the Celarent yields semantic inference rules such as

$$
\begin{aligned}
(34) \quad & B(MeP) \ \& \ Cr(SaM) \xrightarrow{s} B(SeP) \\
(35) \quad & K(MeP) \ \& \ T(SaM) \xrightarrow{s} T(SeP)
\end{aligned}
$$

and so on. Thus, rule (32) reads that if someone claims that he knows that $p$ implies $q$, and that he is certain of the premise $p$, then he is also certain of the conclusion $q$. Similarly, the utterance ‘I know that no $M$ is $P$, and I think that every $S$ is $M$’ implies semantically that the speaker thinks that no $S$ is $P$ [rule (35)].

Imagine now that we collected a set, call it $\Psi$, of such semantic inference rules. We may then say that a given ordering of the set $\{K, Cr, T, B\}$ is compatible with $\Psi$, if for every rule in $\Psi$, the functor appearing in the conclusion of the rule does not precede in this ordering the latest among the functors used in the premises.

For instance, if the set $\Psi$ consists of the single rule (32), then each of the orderings such as $(K, Cr, B, T)$, $(T, K, B, Cr)$, $(T, B, K, Cr)$, etc., with $K$ preceding $Cr$, is compatible with $\Psi$. Now, if $\Psi$ consists of rules (32) and (35) (say), out of the three orderings above only the first is compatible with $\Psi$, as (35) requires that $K$ precedes $T$. Thus, adding new rules may only decrease the set of compatible orderings of the set of functors.

The following conjectures seem to be at least plausible:

(1) as the set $\Psi$ increases by adding to it new semantic inference rules obtained in the manner described above, more and more orderings become actually eliminated as incompatible;

(2) there will eventually remain exactly one ordering which will be compatible with all semantic inference rules obtained in the above manner;

(3) the ordering described in (2) will be

$$
(36) \quad (K, Cr, B, T);
$$

(4) every rule in $\Psi$ will be described by the following ‘weakest link’ principle: the functor applied to the conclusion coincides with the last [in the ordering (36)] among the functors used in the premises. In other words, the conclusion is as certain as the least certain of the premises.

Clearly, the same method of ordering may be applied to other functors from the considered class of epistemic functors, such as ‘I am sure that’, ‘I suppose that’, etc.

#### 2.1.4.4. *I can, I cannot*

We shall denote by $C$ and $C'$ respectively the functors ‘I can’ and ‘I cannot’. As distinct from the functors considered previously, $C$ and $C'$ do not apply to propositional arguments, but to verb phrases, or — more specifically — to descriptions of actions. By actions we shall also mean some psychological processes, as in *I can imagine that*, etc.

In studying the semantic implications below, we shall represent sentences starting

<!-- page 9 -->

<!-- page 9 -->

MOTIVATIONAL CALCULUS

from ‘I can’ or ‘I cannot’ by specifying the object to which the action can (or cannot) be applied, and the prospective outcome of this action, i.e. a future state of the object. Accordingly, we shall write

$$
m(a, P)
$$

for ‘(to) make $a$ to be $P$’, and we shall write $C[m(a, P)]$ and $C'[m(a, P)]$ for ‘I can make $a$ to be $P$’ and ‘I cannot make $a$ to be $P$’, respectively.

Thus, in the sentence *I can lend you this book* the object $a$ is the book in question, and the predicate $P$ stands for ‘is temporarily in your possession’. Similarly, in the sentence *I cannot close this window* the object $a$ is the window, and the predicate $P$ stands for ‘is closed’.

Sometimes the predicate $P$ contains the specification of time, as in *I can telephone him after six o'clock tonight*, and sometimes it leaves the time unspecified, as in *I cannot understand this passage*. The object $a$ sometimes coincides with the speaker, as in *I can swim to the other side of the river*.

We shall use the conjunction and alternative according to the normal usage of connectives ‘and’ and ‘or’ in natural language, as applied to shorten two phrases whose objects or predicates coincide. Thus, $m(a, P) \ \& \ m(b, P)$ will be written as $m(a \ \& \ b, P)$, while $m(a, P) \ \& \ m(a, Q)$ will be written as $m(a, P \ \& \ Q)$. Similar notations$^{12}$ will be used for the alternative: $m(a \lor b, P)$ will stand for $m(a, P) \lor m(b, P)$, while $m(a, P \lor Q)$ will stand for $m(a, P) \lor m(a, Q)$.

Finally, negation $\sim$ may concern only the predicate $P$; we shall write $m(a, \sim P)$ for ‘(to) make $a$ to be $\sim P$’.

In the formulae below, symbols $a$, $b$ will denote distinct objects, and symbols $P$, $Q$, distinct predicates. Moreover, we shall write $P \ \& \ Q = \emptyset$ to denote the fact that predicates $P$ and $Q$ are disjoint in the sense that if $a$ is $P$, then $a$ is not $Q$ and vice versa. Similarly, we shall write $m(a, P) \ \& \ m(b, Q) = \emptyset$ to denote the fact that making $a$ to be $P$ excludes making $b$ to be $Q$, and vice versa.

An analysis of sentences in which the speaker claims that he can or cannot do something, yields the following rules

$$
(37) \quad C[m(a, P) \ \& \ m(b, Q)] \xrightarrow{s} C[m(a, P)] \ \& \ C[m(b, Q)]
$$

and, more specifically,

$$
(38) \quad C[m(a \ \& \ b, P)] \xrightarrow{s} C[m(a, P)] \ \& \ C[m(b, P)]
$$

$$
(39) \quad C[m(a, P \ \& \ Q)] \xrightarrow{s} C[m(a, P)] \ \& \ C[m(a, Q)].
$$

It seems that unless $m(a, P) \ \& \ m(b, Q) = \emptyset$, the converse to (37), and hence also to (38) and (39), is true, i.e. if a person claims that he can $m(a, P)$ and that he can $m(b, Q)$,

$^{12}$ Here again one should point out that such notation does not adequately correspond to the way of combining phrases in natural language. Indeed, ‘$a$ and $b$ are $P$’ is not necessarily the conjunction ‘$a$ is $P$ and $b$ is $P$’ (compare: *John and Mary made friends*). Similar examples may be found against the usage of ‘$a$ is $P$ and $Q$’ for ‘$a$ is $P$ and $a$ is $Q$’, etc, (see Strawson, *Introduction*).

<!-- page 10 -->

## MOTIVATIONAL CALCULUS

and moreover, asserts it in one utterance, then he can make the conjunction $m(a, P) \ \& \ m(b, Q)$. It is important, however, that in the converse to (37), i.e. in

$$
(40) \quad C[m(a, P)] \ \& \ C[m(b, Q)] \xrightarrow{s} C[m(a, P) \ \& \ m(b, Q)]
$$

the sign $\&$ on the left hand side is interpreted as a linguistic conjunction, rather than a logical one. Indeed, a person may be able to run from $x$ to $y$ in, say, less than 2 minutes, and he may be able to run from $y$ to $z$ in less than 2 minutes, but it does not imply that he is able to run from $x$ to $z$ via $y$ in less than 4 minutes.

Now, when $m(a, P) \ \& \ m(b, Q) = \emptyset$, the converse (40) cannot be true. In fact, it appears that the use of the connective ‘and’ in such cases may be inadmissible. Consider, for example, the sentence *I can stay home all day Saturday, and I can go to a theatre on Saturday*, a rather inadmissible utterance. However, if one is willing to accept this utterance as admissible, then it is usually taken to imply that the speaker can either stay at home all day, or that he can go to the theatre (on Saturday). In other words, in case of disjoint $m(a, P)$ and $m(b, Q)$ we have

$$
(41) \quad C[m(a, P)] \ \& \ C[m(b, Q)] \xrightarrow{s} C[m(a, P) \lor m(b, Q)].
$$

In such cases, it would seem more proper to use the connective ‘or’, i.e.

$$
(42) \quad C[m(a, P)] \lor C[m(b, Q)] \xrightarrow{s} C[m(a, P) \lor m(b, Q)].
$$

It may be shown that in general the converse to (42) is false, i.e. that $C[m(a, P) \lor m(b, Q)]$ does not imply the alternative $C[m(a, P)] \lor C[m(b, Q)]$. Indeed, imagine a person shooting at a target divided into two sections, left and right, and assume that he has enough skill to be able to hit the target at will, but not enough skill to hit the desired part of the target. Then, if $a$ stands for the bullet, and $P$ and $Q$ for predicates ‘hit the left (right) section of the target’, $C[m(a, P) \lor m(a, Q)]$ is simply $C[m(a, P \lor Q)]$, that is, the sentence *I can hit the target*. In this case $C[m(a, P)]$ stands for *I can hit the left section of the target*, and similarly for $C[m(a, Q)]$; we have then $C[m(a, P \lor Q)]$ but not $C[m(a, P)]$, and not $C[m(a, Q)]$.

There is an interesting usage of the sentence of the form $C[m(a, P) \lor m(a, Q)]$ when $P \subset Q$; the sentence then is partially ‘redundant’, as logically $m(a, P)$ implies $m(a, Q)$. If such a sentence is uttered, in spite of its redundancy, the speaker’s intentions are that $C[m(a, Q)]$, and that making $a$ to be $P$ is possible, though he cannot guarantee it. This usage is illustrated by examples such as *I can cure him, or at least make him suffer less* or *I can kill the enemy, or at least disable him*.

Next, regarding the functor $C'$ we have

$$
(43) \quad C'[m(a, P)] \xrightarrow{s} \sim C[m(a, P)].
$$

It is important, however, to note that ‘I cannot’ may also be used as synonymous with ‘I shouldn’t’, ‘I oughtn’t’, etc., and ‘I can’ is also used sometimes as expression of permission, or lack of constraint (hence synonymous with ‘I may’). The law (43) holds

<!-- page 11 -->

MOTIVATIONAL CALCULUS

if on both sides the functors are interpreted in the same way, i.e. either both referring to physical possibility, or both to the presence or absence of constraints. Next, we have the following semantic inference rules:

$$
(44) \quad C'[m(a, P) \ \& \ m(b, Q)] \xrightarrow{s} C[m(a, P)] \ \& \ C[m(b, Q)],
$$

and

$$
(45) \quad C'[m(a, P) \lor m(b, Q)] \xrightarrow{s} C'[m(a, P)] \ \& \ C'[m(b, Q)].
$$

Thus, the utterance *I cannot afford to buy a house and a car* implies that the speaker can in fact afford to buy a house, and that he can afford to buy a car (though not both of these items). Similarly, *I cannot afford to buy a house or a car* implies that the speaker cannot afford to buy either of them, i.e. that he cannot afford to buy a house, and that he cannot afford to buy a car.

We shall, however, not include (44) in the system, as it would lead to the following troubles: putting $m(b, Q) = m(a, P)$ in (44) we obtain $C'[m(a, P)] \xrightarrow{s} C[m(a, P)]$, while (43) gives $C'[m(a, P)] \xrightarrow{s} \sim C[m(a, P)]$. This means that if both (43) and (44) are included in the system, it becomes inconsistent, unless we make an obviously unacceptable assumption that every utterance of the form $C'[m(a, P)]$ is inadmissible. Thus, if we want to have the system consistent, and allow the admissibility of utterances $C'[m(a, P)]$, one of the laws (43) or (44) has to be removed.

Finally, if $P \subset Q$, i.e. if every object which is $P$ is also $Q$, we have

$$
(46) \quad C[m(a, P)] \xrightarrow{s} C[m(a, Q)]
$$

and

$$
(47) \quad C'[m(a, Q)] \xrightarrow{s} C'[m(a, P)].
$$

#### 2.1.4.5. *I am glad that*

We shall now consider semantic implications for one of the functors from class 2, i.e. from the class of emotional functors, namely for the functor ‘I am glad that’. This functor applies to propositional arguments. It will be more convenient, however, to specify the form of the argument in a manner similar to that used in paragraph 2.1.4.4. for the functor ‘I can’. Accordingly, in the proposition which appears as an argument for ‘I am glad that’, we shall distinguish its object, $a$, and predicate $P$. We shall use the symbol $G(a, P)$ to denote the sentence ‘I am glad that $a$ is $P$’ (will be $P$, was $P$, etc).

In the sequel, $(a, P)$ will denote the proposition ‘$a$ is $P$’, and we shall apply functors such as $K$ and $T$ to these propositions. Finally, we shall denote by $(a, P)G$ the passive form of the sentence $G(a, P)$, i.e. ‘$a$ being $P$ makes me glad’.

We can now formulate the semantic implications concerning the functor $G$. First of all, we have

$$
(48) \quad G(a, P) \xrightarrow{s} K_3(a, P) \lor T_3(a, P),
$$

<!-- page 12 -->

MOTIVATIONAL CALCULUS

i.e. the sentence ‘I am glad that $a$ is $P$’ implies that the speaker either knows that $a$ is $P$, or at least thinks so.

This may be illustrated by the sentence such as *I am glad that London is the capital of France.* If this sentence is accepted, it must also be accepted that the speaker has some gaps in his knowledge of geography, and is convinced that London is in fact the capital of France.

Next, we have

$$
(49) \quad G[(a, P) \lor (b, Q)] \xrightarrow{s} (a, P)G_3 \ \& \ (b, Q)G_3
$$

i.e. if someone claims that he is glad that an alternative holds, then each of the parts of the alternative must have the property of making him glad. Specifically, if either objects or predicates in (49) coincide, we obtain

$$
(50) \quad G(a \lor b, P) \xrightarrow{s} (a, P)G_3 \ \& \ (b, P)G_3
$$

and

$$
(51) \quad G(a, P \lor Q) \xrightarrow{s} (a, P)G_3 \ \& \ (a, Q)G_3.
$$

The intuitive justification of rule (49) is the following. The utterance of an alternative signifies usually that the speaker does not know which of the components of the alternative holds; thus, if someone asserts that he is glad that some alternative holds, the message which he conveys is that he will be glad in either case (though, perhaps, not in the same degree) — and this is precisely the content of laws (49)–(51).

As an example, consider the sentence *I am glad that he'll come during the weekend*, the inference being that his coming on Saturday will make the speaker glad, and so will his coming on Sunday.

It is interesting to observe that from the sentence in which the speaker asserts that he is glad because of a conjunction, one cannot make any inference about the components of the conjunction. In other words, the sentence $G[(a, P) \ \& \ (b, Q)]$ does not imply $(a, P)G_3$, nor does it imply $(b, Q)G_3$. Indeed, a person who misplaced his gloves may well assert that he is glad because he found them (he found both the left and the right glove); however, this does not imply that finding one glove makes him glad, unless he already has the other one.

Using (51) and de Morgan’s laws, one can obtain the following laws concerning the negation: consider the sentence $G(a, \sim(P \ \& \ Q))$ which is equivalent to $G(a, \sim P \lor \sim Q)$, hence, by (51), to $(a, \sim P)G_3 \ \& \ (a, \sim Q)G_3$. In other words, we have

$$
(52) \quad G(a, \sim(P \ \& \ Q)) \xrightarrow{s} (a, \sim P)G_3 \ \& \ (a, \sim Q)G_3.
$$

Thus, *I am glad that it is not cold and raining* implies that the speaker is glad that it is not cold, and also that he is glad that it is not raining.

<!-- page 13 -->

MOTIVATIONAL CALCULUS

#### 2.1.4.6. *I prefer, I want, I don't want*

We shall now consider proper motivational functors ‘I prefer’, ‘I want’, and ‘I don't want’, to be denoted by $Pf$, $W$, and $W'$ respectively. Regarding the functor $W$, we shall denote by $W(a, P)$ the sentence ‘I want $a$ to be $P$’. Similarly, $W'(a, P)$ will stand for ‘I don't want $a$ to be $P$’.

The functor $Pf$ applies to pairs of arguments of the form considered; thus, we shall write $Pf(a, P; b, Q)$ for the sentence ‘I prefer $a$ to be $P$ than $b$ to be $Q$’.

In most cases of the usage of functor $Pf$ in the natural language, either the objects or the predicates coincide, that is, in most cases the considered sentence has the form

$$
Pf(a, P; a, Q)
$$

or

$$
Pf(a, P; b, P).
$$

As an example of the first usage we may take the sentence *I prefer coffee with sugar to coffee without it*. The usage with $P = Q$, i.e. the second of the above, is *I prefer pears to apples*, the predicate $P$ standing for ‘to be eaten by me’. However, the usage with $a \neq b$ and $P \neq Q$ is not excluded, as in *I prefer coffee with sugar to tea without it*.

It seems that the utterance $Pf(a, P; b, Q)$ in the case when $a \neq b$ and $P \neq Q$ indicates that in some sense the preferences for objects $a$ and $b$, and for predicates $P$ and $Q$ are opposite one to another. The justification of this is that if it were not so, there would be no point in expressing the direction of preference with distinct predicates. Thus, for instance, the sentence *I prefer good apples to bad pears* implies that if the choice was made between good pears and good apples, the pears would be preferred (here it is implicitly assumed that the predicate ‘good’ is better than the predicate ‘bad’).

If one could define preferences towards objects separately, and towards predicates separately, then — denoting these preferences by the same symbol $Pf$ — we would have

$$
(53) \quad Pf(a, P; b, Q) \xrightarrow{s} [Pf_3(a, b) \ \& \ Pf_3(Q, P)] \lor [Pf_3(b, a) \ \& \ Pf_3(P, Q)].
$$

Preferences for predicates, as appear above, may be determined empirically for certain classes of predicates, for instance, colours.

We have also

$$
(54) \quad Pf(a, P; b, P) \ \& \ Pf(a, Q; b, Q) \xrightarrow{s} Pf(a, P \lor Q; b, P \lor Q).
$$

Thus, if a person claims that he prefers to see film $A$ to film $B$ on the 5 P.M. program, and that he prefers to see film $A$ to film $B$ on the 8 P.M. program, then he prefers to see film $A$ to film $B$ on either of the programs.

Next, regarding the alternative, we have the following law

$$
(55) \quad Pf(a, P; b \lor c, P) \xrightarrow{s} Pf(a, P; b, P) \ \& \ Pf(a, P; c, P).
$$

This is in accordance with the use of the connective ‘or’ in the natural language, where

<!-- page 14 -->

MOTIVATIONAL CALCULUS

it reflects a degree of uncertainty. Thus, if someone claims that he prefers $a$ to be $P$ to either $b$ or $c$ being $P$, then he must prefer $(a, P)$ to $(b, P)$ and also $(a, P)$ to $(c, P)$. To give an example, *I prefer beef to either lamb or pork* means that the speaker prefers beef to lamb, and that he prefers beef to pork.

The preferences in which there appear alternatives either of objects or of predicates constitute the basis for the construction of the utility scale. The alternatives then have the form of ‘lotteries’ assigning probabilities to various events, and preferences concern pairs of lotteries. The events described in these lotteries have the form of pairs $(a, P)$, and the lottery assigns probabilities to events of this type either for the same predicate $P$ and various objects $a$, or for the same object $a$ and various predicates $P$. One of the possible sets of axioms implying the existence of a utility scale was presented in Chapter 1. The problem of utility and its connection with preference relation has been studied extensively in the literature, and we shall not discuss it in this section.

We shall now investigate the properties of the functors $W$ and $W'$.

For the first of these functors and the conjunction we have

$$
(56) \quad W(a, P \ \& \ Q) \xrightarrow{s} W(a, P) \ \& \ W(a, Q)
$$

and

$$
(57) \quad W(a \ \& \ b, P) \xrightarrow{s} W(a, P) \ \& \ W(b, P).
$$

The converses to (56) and (57) are not true. First, the sentence $W(a, P) \ \& \ W(a, Q)$ may be admissible even if $P \ \& \ Q = \emptyset$, when the properties expressed by $P$ and $Q$ are sufficiently desirable. Then the sentence $W(a, P \ \& \ Q)$ is not admissible, and the conjunction

$$
W(a, P) \ \& \ W(a, Q) \ \& \ \sim W(a, P \ \& \ Q)
$$

is admissible, which shows that the converse to (56) does not hold.

It may happen, however, that $P$ and $Q$ do not exclude one another, and yet, the person may want $a$ to be $P$, want $a$ to be $Q$, but may not want $a$ to be both $P$ and $Q$. Such a situation occurs if the joint combination of $P$ and $Q$ has some undesirable ‘side effects’. Thus, some men may want their wives to be intelligent, want them to be attractive, but not both.

Similar reasoning shows that the converse to (57) is also false. Thus, a woman may want to have $a$ as her husband, and she may also want to have $b$ as her husband, and yet be unwilling to commit bigamy.

We have, however,

$$
(58) \quad W(a, P) \ \& \ W(a, Q) \xrightarrow{s} W(a, P \lor Q)
$$

and

$$
(59) \quad W(a, P) \ \& \ W(b, P) \xrightarrow{s} W(a \lor b, P).
$$

<!-- page 15 -->

MOTIVATIONAL CALCULUS

The converses to (58) and (59) are, of course, false. Indeed, someone may say that he wants to have an international competition won by a competitor of a specific nationality, and yet be indifferent regarding various competitors of this nationality, so that he would object to making the inference that he wants a specific person of this nationality to win the competition.

For the functor $W'$, i.e. ‘I don't want’, the implications bear some resemblance to de Morgan's laws. Generally, we have

$$
(60) \quad W(a, P) \xrightarrow{s} W'(a, \sim P).
$$

It seems, however, that the converse is false: imagine two candidates, $a$ and $b$, running for an election. Then if someone wants $a$ to win (predicate $P$), he doesn't want $b$ to win (i.e. $a$ to lose). However, if someone doesn't want $a$ to win, he may well agree that for this to happen $b$ must win, but he might object against phrasing it that he wants $b$ to win, so to say, on his own merit; it may be that out of two bad candidates, $b$ presents a ‘lesser evil’.

As consequences of (60) we obtain

$$
(61) \quad W(a, P \ \& \ Q) \xrightarrow{s} W'(a, \sim P \lor \sim Q)
$$

and

$$
(62) \quad W(a, P \lor Q) \xrightarrow{s} W'(a, \sim P \ \& \ \sim Q).
$$

We have also

$$
(63) \quad W'(a, P) \ \& \ W'(b, Q) \xrightarrow{s} W'[(a, P) \lor (b, Q)],
$$

hence from (57), replacing its right hand side by the conjunction $W'(a, \sim P) \ \& \ W'(b, \sim P)$ [by (60)] and using (63):

$$
(64) \quad W(a \ \& \ b, P) \xrightarrow{s} W'(a \lor b, \sim P).
$$

Finally, connecting functors $W$, $W'$, and $Pf$, we have an obvious law

$$
(65) \quad W(a, P) \ \& \ W'(b, Q) \xrightarrow{s} Pf(a, P; b, Q)
$$

Clearly, the converse does not hold: a person may prefer to die of pneumonia than of cancer, but it does not imply that he wants to die of pneumonia.

#### 2.1.4.7. *I must, I ought to*

To complete this section, we shall briefly analyse some functors from normative motivational class, namely the functors ‘I must’ and ‘I ought to’, to be denoted by $M$ and $O$. Both of them apply to the same type of argument as the functor ‘I can’, i.e. the argument has the form $m(a, P)$, standing for ‘(to) make $a$ to be $P$’. We shall there-

<!-- page 16 -->

MOTIVATIONAL CALCULUS

fore denote by $M[m(a, P)]$ the sentence ‘I must make $a$ to be $P$’, and similarly, $O[m(a, P)]$ will stand for ‘I ought to make $a$ to be $P$’.

It appears that the laws for functors $M$ and $O$ are almost identical, and we shall therefore discuss them jointly.

Thus we have

$$
(66) \quad M[m(a, P) \ \& \ m(b, Q)] \xrightarrow{s} M[m(a, P)] \ \& \ M[m(b, Q)]
$$

and

$$
(67) \quad O[m(a, P) \ \& \ m(b, Q)] \xrightarrow{s} O[m(a, P)] \ \& \ O[m(b, Q)].
$$

As an example, consider the sentence *I must give the children medicine, and put them to sleep*, which implies that the speaker feels that she must do both. The same sentence with ‘I must’ replaced by ‘I ought to’ serves as an illustration of (67).

The converses to (66) and (67) require us to distinguish two cases.

When the actions $m(a, P)$ and $m(b, Q)$ do not exclude one another, we have simply

$$
(68) \quad M[m(a, P)] \ \& \ M[m(b, Q)] \xrightarrow{s} M[m(a, P) \ \& \ m(b, Q)]
$$

and

$$
(69) \quad O[m(a, P)] \ \& \ O[m(b, Q)] \xrightarrow{s} O[m(a, P) \ \& \ m(b, Q)].
$$

The above examples of putting children to sleep and giving them medicine may serve as illustrations of these laws.

When $m(a, P)$ and $m(b, Q)$ exclude one another, we have

$$
(70) \quad M[m(a, P)] \ \& \ M[m(b, Q)] \xrightarrow{s} M[m(a, P) \lor m(b, Q)]
$$

and

$$
(71) \quad O[m(a, P)] \ \& \ O[m(b, Q)] \xrightarrow{s} O[m(a, P) \lor m(b, Q)].
$$

To illustrate these laws consider the sentence *I ought to tell George openly to go to hell, but I ought to be careful not to appear unfriendly*, a dilemma requiring making a choice of action of getting rid of George for good, or putting up with him.

The same sentence with ‘I ought to’ replaced by ‘I must’ illustrates (70).

It would seem that when $m(a, P)$ and $m(b, Q)$ exclude one another, the utterances

$$
M[m(a, P)] \ \& \ M[m(b, Q)]
$$

and

$$
O[m(a, P)] \ \& \ O[m(b, Q)]
$$

signify the existence of a conflict. It is interesting to observe that in the same situation of $m(a, P)$ and $m(b, Q)$ excluding one another, the utterance

$$
O[m(a, P)] \ \& \ M[m(b, Q)]
$$

<!-- page 17 -->

MOTIVATIONAL CALCULUS

indicates how the conflict was solved, i.e. which decision was taken: that one, which is attached to the functor ‘I must’. Consider, for example,

*I ought to go home, but I must stay a little longer in the office*

and

*I ought to stay a little longer in the office, but I must go home.*

The first sentence implies that the speaker decided to remain in the office, while the second, that he decided to go home immediately.

Finally, it is worth considering the negations of functors $M$ and $O$. There are two types of negation: we shall denote by $M'$ and $O'$ the functors ‘I mustn’t’ and ‘I oughtn’t’ (‘I shouldn’t’). These two functors, however, express a restraining force as strong as the compelling force expressed by the corresponding functors $M$ and $O$. Another type of negation is obtained by expressing lack of constraint; thus, we shall denote by $H'$ the functor ‘I don’t have to’.

The functors $M'$ and $O'$ behave differently under conjunction and under alternative. Thus, we have

$$
(72) \quad M'[m(a, P) \lor m(b, Q)] \xrightarrow{s} M'[m(a, P)] \ \& \ M'[m(b, Q)]
$$

and

$$
(73) \quad O'[m(a, P) \lor m(b, Q)] \xrightarrow{s} O'[m(a, P)] \ \& \ O'[m(b, Q)].
$$

To illustrate the fact that ‘restraining’ functors like $M'$ and $O'$ when applied to the alternative imply the conjunction of constraints, consider the sentence$^{13}$

*Neither shalt thou desire thy neighbour’s wife, neither shalt thou covet thy neighbour’s house, his field, or his manservant, or his maidservant, his ox, or his ass, or any thing that is thy neighbour’s.*

For the conjunction, the sentence $M'[m(a, P) \ \& \ m(b, Q)]$ does not imply $M'[m(a, P)]$, nor does it imply $M'[m(b, Q)]$ (and the same is true for $O'$). To illustrate it, consider the sentence *I mustn’t marry Paul and Peter*, which does not mean that the speaker feels that she mustn’t marry Paul (or Peter). The sentence, as it stands, reflects only the speaker’s attitude towards bigamy (at least as regards Paul and Peter).

The use of $M$ and $M'$ (and also $O$ and $O'$) reveals then a symmetry, in the sense that neither

$$
M[m(a, P) \lor m(b, Q)]
$$

nor

$$
M'[m(a, P) \ \& \ m(b, Q)]
$$

$^{13}$ Deuterotomy, Chapter 5: 21.

<!-- page 18 -->

<!-- page 70 -->

MOTIVATIONAL CALCULUS

implies anything about actions $m(a, P)$ or $m(b, Q)$ separately. The implications are conditional: the first sentence implies

*If I don't make $a$ to be $P$, then I must make $b$ to be $Q$*,

while the second implies

*If I make $a$ to be $P$, then I mustn't make $b$ to be $Q$*.

Finally, for the functor $H'$ (‘I don't have to’) we have, first of all

$$
(74) \quad H'[m(a, P)] \xrightarrow{s} \sim M[m(a, P)] \ \& \ \sim M'[m(a, P)],
$$

i.e. the functor $H'$ expresses lack of compelling force or constraint with respect to $m(a, P)$. Thus, (74) is equivalent to the conjunction of two implications

$$
(75) \quad H'[m(a, P)] \xrightarrow{s} \sim M[m(a, P)]
$$

and

$$
(76) \quad H'[m(a, P)] \xrightarrow{s} \sim M'[m(a, P)].
$$

Substituting the conjunction in (75) and using the third person singular, we obtain

$$
(77) \quad H'[m(a, P) \ \& \ m(b, Q)] \xrightarrow{s} \sim M_3[m(a, P) \ \& \ m(b, Q)],
$$

that is, using (66) and de Morgan’s laws,

$$
(78) \quad H'[m(a, P) \ \& \ m(b, Q)] \xrightarrow{s} \sim M_3[m(a, P)] \lor \sim M_3[m(b, Q)].
$$

Similarly, for the alternative we obtain from (76) and (72)

$$
(79) \quad H'[m(a, P) \lor m(b, Q)] \xrightarrow{s} \sim M'_3[m(a, P)] \lor \sim M'_3[m(b, Q)]
$$

which shows the symmetry between the functors $M$ and $M'$.

#### 2.1.4.8. *Concluding remarks*

The semantic implications of this section were expressed in a certain symbolism used for representing sentences containing functors of motivational language. In designing this symbolism, it was necessary to introduce some simplifications, that is, to neglect certain aspects of the sentences being represented, and concentrate only on a few selected aspects. Thus, the only features represented in the symbolism were (a) the particular motivational functor used, and (b) the simple structural information about the argument, specifying whether it is a conjunction, alternative, or negation.

Basically there is no trouble in introducing a more complicated symbolism,$^{14}$ in

$^{14}$ No symbolism, however, can ever be adequate: even the ‘symbolism’ consisting of simply writing down the sentence is not entirely satisfactory for analysing inferences made from utterances, as it fails to capture the intonational features.

<!-- page 19 -->

MOTIVATIONAL CALCULUS

which one can code, for example, tenses of verbs used, invent some special symbols for questions, or represent some specific information about grammatical structure of the considered sentence.

The simplifications in symbolism determine the restrictions of the complexity of semantic implications which can be analysed within the given symbolism. On the other hand, it is precisely because of the restrictions that one obtains a set of laws sufficiently general, and consequently sufficiently regular, to constitute a consistent system.

The system presented above is clearly incomplete, as the main intention was to illustrate the methods of approach to the problem rather than attempt to give a detailed and thorough solution. The considerations can be continued in at least three directions. First, one could try to find further semantic implications for the same functors; second, one could analyse new functors, from motivational language or from outside it. Third, one could introduce a more complex symbolism, trying to capture other features of sentences, and consequently analysing more subtle semantic implications.

Admittedly, the system presented (as any other, more complex) is only an approximation to the reality which it attempts to describe. One ought to remember, though, that an approximation is the condition *sine qua non* for the very existence of a system.

## 2.2. LOGICAL CONSISTENCY OF MOTIVATIONAL CALCULUS

In this section we shall analyse the problem of logical consistency of the system of implications introduced in the preceding section. In order to do that, it will be necessary to outline briefly the problems of consistency in logic, as studied in connection with various logical systems, such as the classical propositional calculus, or different systems of modal logic. This will enable us to formulate the particular problem of consistency which we are investigating, and determine the logical status of the presented set of rules.

### 2.2.1. *Propositional calculus*

We begin with the simplest case, namely that of propositional calculus. In formalizing it, one starts from the concept of a *well formed formula* (wff). Roughly speaking, to determine the set of wff's, one has to supply a method of checking whether a given string of symbols is a wff or not. This may be accomplished in various ways, the most commonly used being the following. First, one specifies the basic set of primitive symbols, together with some definitions which enable us to replace some strings of symbols by others. For instance, one may take as primitive symbols the letters $p$, $q$, $r$, $\ldots$ with or without subscripts, parentheses $)$ and $($, and symbols $\vee$ and $\sim$.

The class of well formed formulas can now be defined by the following three conditions:

---

# §2.2.4. Model interpretation of motivational calculus

<!-- source_file: nowakowska_1973_section_224.md -->

# Transcription (LLM vision OCR)


<!-- page 1 -->

systems, i.e. for sets of consequences $\mathbf{C}(\mathscr{S})$ of axioms $\mathscr{S}$. We shall now extend this concept to the considered case of sets of transformation rules.

Intuitively, we want to require that the rules in $\mathscr{A}_1$ do not introduce any inconsistency into the sets $\mathbf{C}(\mathscr{S})$, that is, $\mathbf{C}(\mathscr{S})$ may be inconsistent only if $\mathscr{S}$ is inconsistent. In other words, we want to define the consistency of transformation rules by requiring that they map consistent sets $\mathscr{S}$ into consistent sets $\mathbf{C}(\mathscr{S})$. Clearly, to make this definition meaningful, one has to have an independent definition of consistency of sets $\mathscr{S}$, other than that applicable to sets $\mathbf{C}(\mathscr{S})$ (the latter being that $\mathbf{C}(\mathscr{S})$ is not to contain any sentence together with its negation).

Thus, we shall say that a set $\mathscr{S}$ of sentences is consistent, if there exists a model for it, in the sense that it describes a possible state of affairs (‘world’).

We can now state the requirement of consistency for our set $\mathscr{A}_1$ of semantic implications: we require namely that the mapping $\mathscr{S} \to \mathbf{C}(\mathscr{S})$ preserve consistency, in the sense that if $\mathscr{S}$ is a consistent set of sentences, so is $\mathbf{C}(\mathscr{S})$.

## 2.2.4. *Model interpretation of motivational calculus*

**a. Introductory remarks.** The model will have the form of a world of hypothetical speakers who use the language to express their thoughts, convictions, beliefs, desires, etc, so that all implications of section 2.1.4 are satisfied. Thus, if $A \xrightarrow{s} B$ is any of the semantic implications of section 2.1.4, the model must be such that whenever $A$ is ‘true’, or ‘satisfied’, so is $B$. This necessitates the introduction of a concept of ‘truth’ of a given sentence for a given person. We shall construct a set-theoretical model of ‘subjective truth’ of a given sentence for a given person in such a way that for any implication $A \xrightarrow{s} B$ of section 2.1.4 and any speaker, if $A$ reflects his subjective truth, so does $B$. Naturally, as sentences $A$ and $B$ may involve various functors, we shall have to construct specific interpretations of ‘subjective truth’ for each functor separately.

Let $\mathscr{U}$ denote the set of speakers, its members to be denoted by the terminal letters of the Latin alphabet, $x$, $y$, $z$, $\ldots$, and let $\mathscr{S}$ denote the class of sentences describing all possible states of affairs of a fragment of reality, and the speaker’s relations with this fragment of reality.

We imagine a particular moment of time, fixed throughout the considerations. Given a speaker $x \in \mathscr{U}$ and a functor $F$, let $\mathscr{S}_{F,x} \subset \mathscr{S}$ be the set of all sentences$^{23}$ $s \in \mathscr{S}$ to which the person $x$ would apply the functor $F$, that is, the class of all sentences $s$ such that $Fs$ reflects the subjective truth of speaker $x$.

Thus, $\mathscr{S}_{K,x}$ is the set of all sentences which $x$ knows to be true (at a given moment of time), $\mathscr{S}_{D,x}$ is the set of all sentences which $x$ doubts are true, $\mathscr{S}_{B',y}$ is the set of all sentences which $y$ doesn't believe are true, and so on.

The rules of section 2.1.4 involving functors which apply to propositional arguments

$^{23}$ Here $F$ stands for any functor of section 2.1.4 applicable to a propositional argument.

<!-- page 2 -->

(hence rules from sections 2.1.4.1 and 2.1.4.2) can now be divided into two categories.

The first category comprises the rules which involve only one functor, such as the rules

$$
\begin{aligned}
(1) \quad & K(p \ \& \ q) \xleftrightarrow{s} Kp \ \& \ Kq \\
(2) \quad & T'p \ \& \ T'q \xrightarrow{s} T'(p \lor q).
\end{aligned}
$$

The second category comprises the rules which involve two or more different functors. Such rules are, for instance,

$$
\begin{aligned}
(3) \quad & T'p \xrightarrow{s} \sim Tp \\
(4) \quad & Cr\,p \xrightarrow{s} \sim T \sim p \\
(5) \quad & Dp \xrightarrow{s} T'p.
\end{aligned}
$$

Each of the rules of the first category may be regarded as asserting some property of the corresponding class $\mathscr{S}_{F,x}$. For instance, rule (1) above asserts that the class $\mathscr{S}_{K,x}$ is closed under the operation of conjunction: given any two sentences $p$, $q$ to which the functor $K$ applies (for a given person), their conjunction has the same property (and vice versa).$^{24}$ Thus, we may express (1) as follows:

> *for every person $x \in \mathscr{U}$ and every pair of sentences $p$, $q$, if $p$, $q \in \mathscr{S}_{K,x}$, then $p \ \& \ q \in \mathscr{S}_{K,x}$, and conversely.*

By the same token, (2) asserts that the set $\mathscr{S}_{T',x}$ has the property that if two sentences belong to this set, so does their alternative. In other words,

> *for every person $x$ and every pair of sentences $p$, $q$, if $p$, $q \in \mathscr{S}_{T',x}$, then $p \lor q \in \mathscr{S}_{T',x}$.*

An analogous interpretation may be attached to the remaining rules of this category.

Next, the rules of the second category, i.e. rules which involve more than one functor, express some relations between corresponding sets of sentences. Thus, rule (3) may be stated as

> *for every person $x \in \mathscr{U}$ and sentence $p$, if $p \in \mathscr{S}_{T',x}$, then $p \notin \mathscr{S}_{T,x}$.*

Rules (4) and (5) may be stated respectively as

> *for every person $x \in \mathscr{U}$ and sentence $p$, if $p \in \mathscr{S}_{Cr,x}$, then $\sim p \notin \mathscr{S}_{T,x}$;*

> *for every person $x \in \mathscr{U}$ and sentence $p$, if $p \in \mathscr{S}_{D,x}$, then $p \in \mathscr{S}_{T',x}$ (that is, $\mathscr{S}_{D,x} \subset \mathscr{S}_{T',x}$).*

A similar interpretation may be given to the semantic implications of section 2.1.4 which involve functors applicable to arguments other than propositional, that is, which are applicable to appropriate verb phrases. The corresponding laws will assert

$^{24}$ In other words, if sentences $Kp$ and $Kq$ reflect the ‘subjective truth’ of person $x$, the same is true for the sentence $K(p \ \& \ q)$ and conversely.

<!-- page 3 -->

<!-- page 3 -->

that the classes of verb phrases considered have some closure properties, or that they are related one to another in some specific way.

The problem of constructing a model for motivational calculus may now be stated as the problem of constructing classes of sentences (or verb phrases) satisfying the properties described by semantic implications from section 2.1.4.

As all the above rephrasings of semantic implications are preceded by the universal quantifier ‘for every person $x$’ it will be sufficient to construct such classes separately for every person $x$.

Accordingly, we shall drop the subscript $x$ from notations in order to simplify them, and restrict consideration to a fixed person $x$. Also for simplicity, the model will be presented in successive steps, covering groups of functors one at a time.

**b.** *Model: epistemic functors.* Formally, the model will be described as an ordered set of six objects

$$
(6) \quad \langle X, P, v_T, v_B, v_{Cr}, v_D \rangle
$$

where $X$ is a fixed nonempty set, to be called the space, $P$ is a probability distribution on $X$, and $v_T$, $v_B$, $v_{Cr}$, $v_D$ are subsets of $X$ satisfying the relation

$$
v_T \subset v_B \cap v_{Cr} \cap v_D
$$

![Fig. 1 — epistemic sets $v_T \subset v_B \cap v_{Cr} \cap v_D$](figures/nowakowska1973/fig1_epistemic_sets.png)

**Fig. 1**

(see fig. 1). We interpret letters $p$, $q$, $\ldots$ in formulas of sections 2.1.4.1 and 2.1.4.2 as sets in $X$. The symbol $\sim$, when applied to symbols $p$, $q$, $\ldots$ will be interpreted as the set-theoretical complementation ‘$^{c}$’; when applied to formulas preceded by functors (such as $\sim Tp$, etc), it will be the logical negation.

Similarly, the symbol $\&$ is interpreted as intersection $\cap$ of sets, if applied to propositional arguments in formulas for semantic implications; otherwise, it will be interpreted as logical conjunction. Finally, the symbol $\lor$ when applied to proposition-

<!-- page 4 -->

MOTIVATIONAL CALCULUS

Finally, the symbol $\lor$ when applied to propositional arguments will be interpreted as set-theoretical union $\cup$, and otherwise as logical alternative. The symbol $\xrightarrow{s}$ will be interpreted as logical implication. Finally, the subscript $3$ is to be neglected, i.e. formulas with this subscript are to be interpreted as analogous formulas without it. The interpretation of symbols $K$, $Cr$, $T$, $T'$, $B$, $B'$, and $D$ is the following:

$$
\begin{aligned}
K\alpha &\equiv_{\mathrm{df}} P(\alpha) = 1 \\
Cr\alpha &\equiv_{\mathrm{df}} \alpha \supset v_{Cr} \\
T\alpha &\equiv_{\mathrm{df}} \alpha \supset v_T \\
T'\alpha &\equiv_{\mathrm{df}} \alpha \subset v_T^{c} \\
B\alpha &\equiv_{\mathrm{df}} \alpha \supset v_B \\
B'\alpha &\equiv_{\mathrm{df}} \alpha \subset v_B^{c} \\
D\alpha &\equiv_{\mathrm{df}} \alpha \subset v_D^{c}
\end{aligned}
$$

Finally, $K'$ is to be applicable only to $\alpha$, $\beta$ such that $\alpha \cap \beta = \emptyset$, $\alpha \cup \beta = X$, and

$$
K'(\alpha, \beta) \equiv_{\mathrm{df}} P(\alpha) > 0 \text{ and } P(\beta) > 0.
$$

Thus, to every person $x$ there corresponds a probability measure $P = P_x$ on $X$ and sets $v_T = v_{T,x}$, $v_B = v_{B,x}$, etc. in $X$. The interpretation of ‘subjective truth’ of a sentence $p$ for a person $x$ is such that $Kp$ is true for $x$ (i.e. $x$ knows that $p$) if $P_x(p) = 1$. Next, $Tp$ is true for $x$ (i.e. $x$ thinks that $p$), if $p \supset v_{T,x}$, while $Dp$ is true for $x$ ($x$ doubts that $p$) if $p \subset v_{D,x}^{c}$, etc.

It is a matter of simple checking that all the semantic implications from sections 2.1.4.1 and 2.1.4.2 involving the above functors are now transformed into true propositions. Let us begin with formulas involving the functors $K$ and $K'$. Thus, formulas (2) and (5) of section 2.1.4.1, that is,

$$
K(p \ \& \ q) \xleftrightarrow{s} Kp \ \& \ Kq
$$

assert, in the above interpretation, that an intersection of two sets has probability one if, and only if, each of these sets has probability one — a well known fact in probability theory.

Law (11), namely $K'(p, q) \xrightarrow{s} \sim Kp$, now asserts that if two sets are disjoint and have positive probabilities, then none of them can have probability one.

Law (15), namely $\sim K'(p, q) \xrightarrow{s} K_3 p \lor K_3 q$, asserts that if for two sets complementing each other it is not true that both have positive probabilities, then one of them must have probability one.

Finally, law (10) is trivially true, and the remaining laws involving only functors $K$ and $K'$ [numbers (12), (13), (14)] are obtained from the already verified ones either by substitution or by contraposition.

Next, observe that we have, in general, for any sets $p$, $q$ and $v$:

<!-- page 5 -->

MOTIVATIONAL CALCULUS

**(i)** *if $p$ and $q$ both contain $v$, so does their intersection, and conversely (see fig. 2);*

**(ii)** *if $p$ and $q$ are both contained in the complement of $v$, so is their union, and conversely (see fig. 3).*

![Fig. 2 — $v$ inside $p \cap q$](figures/nowakowska1973/fig2_v_in_intersection.png)

**Fig. 2**

![Fig. 3 — $p$ and $q$ inside $v^c$](figures/nowakowska1973/fig3_sets_in_v_complement.png)

**Fig. 3**

![Fig. 2 and Fig. 3 together](figures/nowakowska1973/fig2_fig3_intersection_union.png)

Formally, we may write

$$
[v \subset p \text{ and } v \subset q] \Leftrightarrow [v \subset p \cap q]
$$

and

$$
[p \subset v^{c} \text{ and } q \subset v^{c}] \Leftrightarrow [p \cup q \subset v^{c}].
$$

Thus the class of all sets containing a given set $v$ is closed under intersections, and the class of all sets contained in a given set $v^{c}$ is closed under unions.

It follows at once that the pairs of laws (3), (6) and (4), (7), as well as law (24) are satisfied. Indeed, (3) and (6) assert that

$$
Cr(p \ \& \ q) \xleftrightarrow{s} Cr\,p \ \& \ Cr\,q
$$

<!-- page 6 -->

that is, they assert that the class of sets to which $Cr$ applies is closed under intersection, a property valid in view of the interpretation of the functor $Cr$ ($Cr\,p$ if, and only if, $p \supset v_{Cr}$). Laws (4), (7) and (24) assert analogous properties for functors $T$ and $B$.

Next, laws (22), (31) and the first implication in (29), that is, $B'p \ \& \ B'q \xrightarrow{s} B'(p \lor q)$ are satisfied because of (ii) in view of the interpretation of functors $T'$, $B'$, and $D$. For instance, the formula above asserts now that if $p$ and $q$ are both contained in the set $v_B^c$, so is their union $p \cup q$.

There remain formulas involving more than one functor. Thus, (16) asserts that $Cr\,p \xrightarrow{s} \sim T\,\sim p$. In our interpretation, $Cr\,p$ means that $p \supset v_{Cr}$, and since $v_{Cr} \supset v_T$ by assumption (see fig. 1), we have $p \supset v_T$, hence it is not true that $v_T \subset p^c$. This shows that we have $\sim T\,\sim p$.

Next, formula (18) asserts that $Tp \xrightarrow{s} T'\,\sim p$; indeed, $Tp$ means that $p \supset v_T$, which is the same as $p^c \subset v_T^c$, hence $T'\,\sim p$. Similarly, $T'p \xrightarrow{s} \sim Tp$ [law (23)] asserts that if $p \subset v_T^c$, then it is not true that $p \supset v_T$.

Law (25) asserts that $B(p \lor q) \xrightarrow{s} T'(\sim p \ \& \ \sim q)$. Indeed, if $p \cup q \supset v_B$, then also $p \cup q \supset v_T$, hence $(p \cup q)^c \subset v_T^c$. By de Morgan's law we obtain therefore $p^c \cap q^c \subset v_T^c$, which means that $T'(\sim p \ \& \ \sim q)$.

Similarly, $B'p \xrightarrow{s} T\,\sim p$ [law (26)] holds: if $p \subset v_B^c$, then $p \subset v_T^c$, hence $p^c \supset v_T$, which shows that $T\,\sim p$.

There remain two laws, namely (30) and the second part of implication (29), that is, $B'p \ \& \ B'q \xrightarrow{s} B(\sim p \ \& \ \sim q)$ (the remaining laws are consequences of the ones already proved.) Indeed, if $p \subset v_B^c$ and $q \subset v_B^c$, then $(p \cup q) \subset v_B^c$, hence $(p \cup q)^c = (p^c \cap q^c) \supset v_B$, which shows that $B(\sim p \ \& \ \sim q)$.

Finally, (30) asserts that $Dp \xrightarrow{s} T'p$. Indeed, if $p \subset v_D^c$, then $p \subset v_T^c$ (since $v_T \subset v_D$), which is the same as $T'p$.

The above model interpretation may be not too far from reality. Indeed, assume that $P(v_T) = r_T$, $P(v_B) = r_B$, $P(v_{Cr}) = r_{Cr}$, and $P(v_D) = r_D$. We have then $r_T \leqslant r_B$, $r_T \leqslant r_{Cr}$, and $r_T \leqslant r_D$. It appears that a reasonable choice for $r_T$ is $\frac{1}{2}$; then all propositions $p$ for which ‘I think that $p$’ holds, have (subjective) probability at least $\frac{1}{2}$ (i.e. $P(p) \geqslant \frac{1}{2}$). Next, the remaining numbers $r_B$, $r_{Cr}$, and $r_D$ should be selected close to 1; this would ensure that all propositions $p$ which are ‘certain’ or ‘believed’ have sufficiently high subjective probability (at least $r_{Cr}$, and $r_B$ respectively). On the other hand, for the functors $T'$, $B'$ and $D$, whose interpretation is expressed in terms of the inclusion in complements of the sets $v_T$, $v_B$, and $v_D$ respectively, propositions $p$ for which $T'p$, $B'p$, and $Dp$ have subjective probabilities at most $1 - r_T = \frac{1}{2}$, $1 - r_B$, and $1 - r_D$.

**c.** *Model: functor G.* We shall now extend model (6) to show the consistency of the laws for the functor $G$ (‘I am glad that’). Though these laws refer to propositional arguments of the specific form $(a, P)$, to be read ‘$a$ is $P$’, it is clear that no essential change occurred, and we can write these laws as

$$
Gp \xrightarrow{s} K_3 p \lor T_3 p
$$

[law (48)] and

<!-- page 7 -->

# MOTIVATIONAL CALCULUS

$$
G(p \lor q) \xrightarrow{s} G_3 p \ \& \ G_3 q
$$

[law (48)] and [law (49)]. Other laws are simply consequences of the above, with $p$ and $q$ replaced by $(a, P)$, $(b, Q)$, etc.

We shall keep the previous interpretation of symbols $K$, $K_3$, $T$, $T_3$ and constants in the formulas; we add to the model (6) the set $v_G \subset X$ with $v_G \cap v_T = \emptyset$, and define (see fig. 4)

$Gp$ (and also $G_3 p$)

$G_3 q$, $G_3 r$ (but not $Gq$, $Gr$)

![Fig. 4 — functor $G$](figures/nowakowska1973/fig4_functor_G.png)

**Fig. 4**

$$
G\alpha \underset{df}{=} \alpha \supset v_T \text{ and } \alpha \subset v_G^c
$$

$$
G_3 \alpha \underset{df}{=} \alpha \subset v_G^c
$$

(note that now the subscript 3 is not to be neglected). It is a matter of simple checking that the above two laws hold with this interpretation. Indeed, if $Gp$, then $p \supset v_T$, which is the same as $Tp$ in view of the interpretation of the functor $T$. Moreover, $Tp$ is the same as $T_3 p$, which shows that $Gp$ implies $T_3 p$, and consequently, also $K_3 p \lor T_3 p$.

Next, if $G(p \lor q)$, then $(p \cup q) \subset v_G^c$, hence $p \subset v_G^c$ and $q \subset v_G^c$, which shows that $G_3 p$ and $G_3 q$.

**d.** *Interpretation of verb phrases in the model.* We shall now extend the model still further so as to cover the remaining implications of section 2.1.4. Here it will be essential to assign separate interpretations to the symbols $a$ and $P$ appearing in the formulas, as we no longer deal with propositions but with verb phrases, denoted by $m(a, P)$ for the functors $C$, $C'$, $M$, $M'$, $O$, $O'$, and $H'$, and simply by $(a, P)$ for the functors $W$, $W'$, and $Pf$.

Generally, we shall keep the interpretation of the symbols $\&$, $\lor$, $\sim$ as before, i.e. we shall interpret them either as the corresponding logical functors, or as the set-theoretical operations of intersection, union, and complement, depending on the place

<!-- page 8 -->

MOTIVATIONAL CALCULUS

these symbols occupy in the formula. We shall interpret predicates $P$, $Q$, $\ldots$ as sets in $X$. Formally, we extend model (6) by adding the pair $A$, $\mathcal{V}$, where $A$ is a set, and $\mathcal{V}$ is a class of sets $v(a)$, $a \in A$, where each $v(a)$ is a subset of $X$. Symbols $a$, $b$, $\ldots$ in formulas will be interpreted as elements of the set $A$, and symbols $P$, $Q$, $\ldots$ as subsets of $X$. Next, $m(a, P)$, and also $(a, P)$ in formulas for functors $W$, $W'$, and $Pf$, will be interpreted as the set $v(a) \cap P \subset X$.

**e.** *Model: functors $C$ and $C'$.* We start from interpreting the functors $C$ and $C'$. Namely, we shall select a set $v_C \subset X$ and put

$$
C[m(a, P)] \underset{df}{=} v(a) \cap P \supset v_C
$$

$$
C'[m(a, P)] \underset{df}{=} v(a) \cap P \subset v_C^c
$$

$C[m(a,P)]$

$C'[m(b,Q)]$, $C'[m(c,R)]$.

![Fig. 5 — functors $C$ and $C'$](figures/nowakowska1973/fig5_functors_C_Cprime.png)

**Fig. 5**

(see fig. 5). The laws for the functors $C$ and $C'$ (except law (44) which was not included in the system) are now satisfied. Indeed, consider first laws (37)–(39). The left hand side of (37) asserts that the product

$$
(v(a) \cap P) \cap (v(b) \cap Q)
$$

contains the set $v_C$. Then each of the sets $v(a) \cap P$ and $v(b) \cap Q$ must also contain $v_C$, which shows that the right hand side of (37), i.e. $C[m(a, P)] \ \& \ C[m(b, Q)]$ holds. Laws (38) and (39) assert the same property for $P = Q$ and $a = b$, respectively.

Next, law (40) states that if $(v(a) \cap P) \cap (v(b) \cap Q) \neq \emptyset$, then whenever $v(a) \cap P \supset v_C$ and $v(b) \cap Q \supset v_C$, we also have $(v(a) \cap P) \cap (v(b) \cap Q) \supset v_C$, a property obviously satisfied.

Law (42) asserts similarly that if the sets $v(a) \cap P$ and $v(b) \cap Q$ are disjoint, then whenever one of them contains $v_C$, so does their union, a property satisfied whether these sets are disjoint or not,

<!-- page 9 -->

MOTIVATIONAL CALCULUS

Next, (43) simply asserts that if $v(a) \cap P \subset v_C^c$, then it is not true that $v(a) \cap P \supset v_C$. To show that (45) holds, we can argue as follows: the left hand side, $C'[m(a, P) \lor m(b, Q)]$, asserts that the union $(v(a) \cap P) \cup (v(b) \cap R)$ is contained in $v_C^c$. This implies that each of the sets $v(a) \cap P$ and $v(b) \cap Q$ must also be contained in $v_C^c$, which is equivalent to the conjunction $C'[m(a, P)] \ \& \ C'[m(b, Q)]$.

Finally, let us consider laws (46) and (47). Assume that $P \subset Q$. Then $v(a) \cap P \subset v(a) \cap Q$, hence if the first of these sets contains $v_C$ so must the second, and if the second of these sets is contained in $v_C^c$, so must be the first.

**f.** *Model: functors $W$, $W'$, and $Pf$.* Next, we shall extend the model along the same lines so as to show the consistency of laws for the functors $W$, $W'$, and $Pf$. Thus, we add to our model a set $v_W \subset X$ and define (fig. 6)

$W(a,P)$, $W'(b,Q)$, $Pf(a,P;b,Q)$

![Fig. 6 — functors $W$, $W'$, $Pf$](figures/nowakowska1973/fig6_functors_W_Wprime_Pf.png)

**Fig. 6**

$$
W(a, P) \underset{df}{=} v(a) \cap P \supset v_W
$$

$$
W'(a, P) \underset{df}{=} v(a) \cap P \subset v_W^c
$$

$$
Pf(a, P; b, Q) \underset{df}{=} v(a) \cap P \supset v_W \text{ and } v(b) \cap Q \subset v_W^c.
$$

We shall now check the consecutive laws, starting from laws for the functors $W$ and $W'$.

Thus, to prove (56) assume that $W(a, P \ \& \ Q)$, that is, $v(a) \cap (P \cap Q) \supset v_W$. Then each of the sets $v(a)$, $P$, and $Q$ must contain $v_W$, and we have $v(a) \cap P \supset v_W$, $v(a) \cap Q \supset v_W$, which is the same as the conjunction $W(a, P) \ \& \ W(a, Q)$.

Next, if $W(a \ \& \ b, P)$, then $(v(a) \cap v(b)) \cap P \supset v_W$, and the same reasoning yields $v(a) \cap P \supset v_W$, $v(b) \cap P \supset v_W$, which proves (57).

Laws (58) and (59) are proved in an analogous manner. If $W(a, P)$ and $W(a, Q)$, then $v(a) \cap P \supset v_W$ and $v(a) \cap Q \supset v_W$. Consequently, the union of the left hand sides also contains $v_W$, that is, $(v(a) \cap P) \cup (v(a) \cap Q) \supset v_W$. However, $(v(a) \cap P) \cup$

<!-- page 10 -->

MOTIVATIONAL CALCULUS

However, $(v(a) \cap P) \cup (v(a) \cap Q) = v(a) \cap (P \cup Q)$, which shows that $W(a, P \lor Q)$. Similarly, if $W(a, P)$ and $W(b, P)$, then $v(a) \cap P \supset v_W$ and $v(b) \cap P \supset v_W$, hence $(v(a) \cup v(b)) \cap P \supset v_W$, which means that $W(a \lor b, P)$. This completes the proof of (58) and (59).

Next, if $W(a, P)$, then $v(a) \cap P \supset v_W$, hence also $P \supset v_W$. Thus, $P^c \subset v_W^c$, and as $v(a) \cap P^c \subset P^c$, we obtain $v(a) \cap P^c \subset v_W^c$, which is the same as $W'(a, \sim P)$. This proves law (60).

To prove (63) assume that $W'(a, P) \ \& \ W'(b, Q)$. Then $v(a) \cap P \subset v_W^c$ and $v(b) \cap Q \subset v_W^c$, which implies that $(v(a) \cap P) \cup (v(b) \cap Q) \subset v_W^c$, hence $W'[(a, P) \lor (b, Q)]$. Laws (61), (62), and (64) are consequences of (57), (60), and (63).

Turning now to laws concerning the functor $Pf$, assume that the left hand side of (54) holds. This means that $v(a) \cap P \supset v_W$, $v(b) \cap P \subset v_W^c$, $v(a) \cap Q \supset v_W$, $v(b) \cap Q \subset v_W^c$. The first and third inclusions yield $v(a) \cap (P \cup Q) \supset v_W$, while the second and fourth yield $v(b) \cap (P \cup Q) \subset v_W^c$; the last two inclusions, however, are equivalent to $Pf(a, P \lor Q; b, P \lor Q)$, which proves (54).

The proof of (55) is analogous. If $Pf(a, P; b \lor c, P)$ then $v(a) \cap P \supset v_W$ and $(v(b) \cup v(c)) \cap P \subset v_W^c$, we have then from the last inclusion $v(b) \cap P \subset v_W^c$, and $v(c) \cap P \subset v_W^c$. Combined with $v(a) \cap P \supset v_W$ it yields $Pf(a, P; b, P) \ \& \ Pf(a, P; c, P)$.

Finally, the left hand side of (65) simply states the definition of $Pf(a, P; b, P)$; this completes the proof of consistency of laws for the functors $Pf$, $W$, and $W'$.

**g.** *Model: functors $M$, $M'$, $O$, $O'$ and $H'$.* We employ now the same technique for the remaining functors from section 2.1.4. We add to the model two sets, $v_M \subset X$ and $v_O \subset X$, and define

$$
M[m(a, P)] \underset{df}{=} v(a) \cap P \supset v_M
$$

$$
M'[m(a, P)] \underset{df}{=} v(a) \cap P \subset v_M^c
$$

$$
O[m(a, P)] \underset{df}{=} v(a) \cap P \supset v_O
$$

$$
O'[m(a, P)] \underset{df}{=} v(a) \cap P \subset v_O^c
$$

$$
H'[m(a, P)] \underset{df}{=} v(a) \cap P \cap v_M \neq \emptyset \text{ and } v(a) \cap P \cap v_M \neq v_M
$$

![Fig. 7 — $H'[m(a,P)]$](figures/nowakowska1973/fig7_functor_Hprime.png)

**Fig. 7.** $H'[m(a,P)]$.

<!-- page 11 -->

MOTIVATIONAL CALCULUS

(see fig. 7). The verification of laws (66)–(73) is analogous to that of the laws for the functors $W$ and $W'$, and will not be repeated here. Law (74) is almost a restatement of the definitions of $H'$, $M$, and $M'$ above: if $H'[m(a, P)]$, then $v(a) \cap P \cap v_M \neq \emptyset$, hence $v(a) \cap P$ is not contained in $v_M^c$; similarly, $v(a) \cap P \cap v_M \neq v_M$, hence $v(a) \cap P$ does not contain $v_M$. The last two conditions, however, simply mean that not $M[m(a, P)]$ and not $M'[m(a, P)]$. The remaining laws (75)–(79) follow now by substitution from (74).

### 2.2.5. Concluding remarks

To put all the pieces of the model together, we may define it as an ordered 14-tuple

$$
\langle U, X, A, \mathbf{P}, \mathscr{G}, V_T, V_B, V_{Cr}, V_D, V_G, V_C, V_W, V_M, V_O \rangle
$$

where $U$ is the set (of persons), $X$ is a fixed space, $A$ is the set (of objects). Next, $\mathbf{P}$ is the class of probability distributions $P_u$, $u \in U$ on $X$, and $\mathscr{G}$ is a class of sets $v(a)$, $a \in A$, where each $v(a)$ is a subset of $X$.

Each $V_F$ is a class of sets $v_{F,u}$, $u \in U$ (subsets of $X$). These classes satisfy the following conditions: for all $u \in U$

$$
v_{T,u} \subset v_{B,u} \cap v_{Cr,u} \cap v_{D,u}
$$

and

$$
v_{T,u} \cap v_{G,u} = \emptyset.
$$

The considerations of the preceding section were devoted to the interpretation of the symbols appearing in the formulas of motivational calculus in terms of the above model (for a fixed person), and to showing that the particular semantic implications of section 2.1.4 are satisfied in the model.

The basic idea was to identify the arguments appearing in formulas involving the considered functors as sets in $X$, and to interpret the symbols $\&$, $\lor$, and $\sim$ either as corresponding logical functors or as set-theoretical operations, depending on their place in the formula. This identification has been accomplished in two steps. For functors $K$, $Cr$, $T$, $T'$, $B$, $B'$, $D$ and also $G$, the arguments were propositions, and were simply interpreted as subsets of $X$. For the remaining functors, $C$, $C'$, $W$, $W'$, $Pf$, $M$, $M'$, $O$, $O'$, and $H'$, the arguments were interpreted as intersections of sets $v(a)$, $v(b)$, $\ldots$ assigned to objects, and sets $P$, $Q$, $\ldots$ assigned to predicates. In all cases, except for the functor $G$, there was no need for distinguishing between functors in the first and third person singular.

Apart from the functors $K$ and $K'$ which were interpreted in terms of a probability distribution on the underlying space $X$, the remaining functors (except for $G$, $Pf$ and $H'$) were interpreted by choosing a subset $v_F$ for a given functor $F$ and using one of the following two schemes:

$$
(1) \quad F\alpha \underset{df}{\equiv} \alpha \supset v_F
$$

---

# §5.3. Structure of motivationally consistent strings (promise CF)

<!-- source_file: nowakowska_1973_section_53.md -->

# Transcription (LLM vision OCR)

<!-- page 1 -->

with the additional convention that whenever any of the sets (5) is empty, the corresponding condition (6)–(9) is automatically satisfied.

However, for $x \in L_M - L$ it is impossible that all four sets (5) are empty (see assumption (13), section 5.1).

Intuitively speaking, a string is motivationally consistent, if its utterances are not ‘contradicted’ by its actions: every time-result in $\bigcup_k W_k$ is attained$^6$ and every time-result in $\bigcup_k W'_k$ is avoided; moreover, for every $k$ the substring of actions following the $k$-th sentence of it belongs to the set of strings of which one ought to be performed (according to this sentence), and does not belong to the set of strings which (according to this sentence) should not be performed.

As a simple consequence of the above definition we have

**PROPOSITION 1.** *If the string $x$ is motivationally consistent, then the sets $\bigcup_k W_k$ and $\bigcup_k W'_k$ are disjoint.*

Indeed, suppose that $(s', n') \in \bigcup_k W_k \cap \bigcup_k W'_k$. Then $(s', n') \in W_{k'}$, and $(s', n') \in W'_{k''}$ for some $k', k''$ (in other words, $(s', n')$ is asserted as wanted in the sentence $\alpha_{k'}$, and $s'$ is asserted as unwanted in the sentence $\alpha_{k''}$; this implies, naturally, that $k' \neq k''$ in view of assumption (7) of section 5.1).

Suppose that $x$ is motivationally consistent. Then $\pi(x) \in \bigcap_k \hat{R}^{-1}(W_k)$, but

$$
\bigcap_k \hat{R}^{-1}(W_k) \subset \hat{R}^{-1}(W_{k'}) = \bigcap_{(s, n) \in W_{k'}} R^{-1}(s, n) \subset R^{-1}(s', n'),
$$

and we must have $\pi(x) \in R^{-1}(s', n')$.

On the other hand, we also have $\pi(x) \notin \bigcup_k R^{-1}(W'_k)$. Since

$$
\bigcup_k R^{-1}(W'_k) \supset R^{-1}(W'_{k''}) = \bigcup_{(s, n) \in W'_{k''}} R^{-1}(s, n) \supset R^{-1}(s', n'),
$$

we must have $\pi(x) \notin R^{-1}(s', n')$, which gives the contradiction.

### 5.3. STRUCTURE OF MOTIVATIONALLY CONSISTENT STRINGS

#### 5.3.1. *Satisfiable strings of sentences*

Let $\alpha_1, \dots, \alpha_r$ be a finite sequence of elements of $M$, and let $n_0, \dots, n_r \in N$. Denote $k_0 = n_0$, $k_1 = n_0 + \varphi(\alpha_1) + n_1$, $\dots$. We shall say that the system

$$
\text{(1)} \qquad (n_0, \alpha_1, n_1, \dots, \alpha_r, n_r)
$$

---

$^6$ Indeed, $\bigcap_k \hat{R}^{-1}(W_k) = \hat{R}^{-1}(\bigcup_k W_k)$.

<!-- page 2 -->

is *satisfiable* if there exists a sequence $z_0, z_1, \ldots, z_r$ of elements of $D^*$ such that $\varphi(z_j) = n_j$, $j = 1, \ldots, r$,

$$
z_j \varphi(\alpha_{j+1}) z_{j+1} \cdots \varphi(\alpha_r) z_r \in O_{(\alpha_j, k_j)} - O'_{(\alpha_j, k_j)}
$$

for $j = 1, 2, \ldots, r$, and

$$
z_0 \varphi(\alpha_1) z_1 \cdots \varphi(\alpha_r) z_r \in \hat{R}^{-1}\Bigl(\bigcup_{j=1}^{r} W_{(\alpha_j, k_j)}\Bigr) - R^{-1}\Bigl(\bigcup_{j=1}^{r} W'_{(\alpha_j, k_j)}\Bigr).
$$

It follows from this definition that we have

**PROPOSITION 1.** *If $x \in L_M - L$ is a motivationally consistent string whose representation of the verbal part is $x = u_1 \alpha_1 v_1 = u_2 \alpha_2 v_2 = \cdots = u_r \alpha_r v_r$, then the system $(n_0, \alpha_1, n_1, \ldots, \alpha_r, n_r)$ with $n_0 = \varphi(u_0)$, $n_1 = \varphi(u_2) - \varphi(u_1) - \varphi(\alpha_1)$, $\ldots$ is satisfiable.*

In other words, a sequence of sentences (together with the moments of their utterance) is satisfiable if it can be embedded into a string of actions in such a way that the resulting ‘mixed’ string is motivationally consistent. From Proposition 1 of the preceding section it follows that if system (1) is satisfiable, then the sets $\bigcup_{j=1}^{r} W_j$ and $\bigcup_{j=1}^{r} W'_j$ are disjoint. This agrees with the common intuition according to which inconsistent wantings cannot be satisfied.

#### 5.3.2. *Properties of the sets $O_{(\alpha, k)}$*

Let $\alpha \in M$ and $k \in N$, and assume that $O_{(\alpha, k)} \neq \emptyset$.

**DEFINITION 1.** We shall say that the string $z \in O_{(\alpha, k)}$ *discharges the obligation asserted in* $(\alpha, k)$, if the conditions $z = z_1 z_2$ and $\varphi(z_2) > 0$ imply $z_1 \notin O_{(\alpha, k)}$. Let $\bar{O}_{(\alpha, k)}$ be the set of all such strings.

We have

**PROPOSITION 2.** *If $O_{(\alpha, k)} \neq \emptyset$, then $\bar{O}_{(\alpha, k)} \neq \emptyset$.*

Indeed, if we had $\bar{O}_{(\alpha, k)} = \emptyset$, then every string $z \in O_{(\alpha, k)}$ could be reduced to a shorter string $z'$ also belonging to $O_{(\alpha, k)}$. By consecutive reductions we would then obtain $0 \in O_{(\alpha, k)}$, and since for the string $0$ of length $0$ the premise of the condition defining $\bar{O}_{(\alpha, k)}$ is empty, we would have $0 \in \bar{O}_{(\alpha, k)}$, contrary to the supposition. ■

Let

$$
(2) \quad H_O(\alpha, k) = \max\{\varphi(z) : z \in \bar{O}_{(\alpha, k)}\}.
$$

We shall refer to $H_O(\alpha, k)$ as the *O-motivational horizon of* $(\alpha, k)$.

We have

<!-- page 3 -->

**PROPOSITION 3.** *Let $O_{(\alpha, k)} \neq \emptyset$, and assume that $H_O(\alpha, k) = K < \infty$. If $x$ satisfies the conditions $x \notin O_{(\alpha, k)}$ and $\varphi(x) > K$, then $xu \notin O_{(\alpha, k)}$ for every string $u \in D_+^*$.*

**PROOF.** Suppose that $x$ satisfies the assumptions and $xu \in O_{(\alpha, k)}$ for some $u \in D_+^*$. Then

$$
\varphi(xu) = \varphi(x) + \varphi(u) \geq \varphi(x) > K,
$$

hence $xu \notin \bar{O}_{(\alpha, k)}$. There exists therefore $v \in \bar{O}_{(\alpha, k)}$ such that

$$
\text{(3)} \quad xu = vw
$$

for some $w \in D_+^*$. Since $\varphi(x) > K = \max\{\varphi(z) : z \in \bar{O}_{(\alpha, k)}\} \geq \varphi(v)$, it follows from (3) that $x = vw'$ for some $w' \in D_+^*$. By assumption (11) about the set $O_{(\alpha, k)}$ (see Section 5.1), we have then $x \in O_{(\alpha, k)}$, contrary to the assumption. ■

To formulate the next theorem, it is necessary to modify slightly the conventions concerning notation for strings of actions. Let us introduce a special symbol, say $\#$, for a unit pause, and replace in strings of actions all pauses by strings of $\#$ of appropriate lengths. Then $D^*$ will become the monoid over a *finite alphabet*,$^7$ namely $D \cup \{\#\}$. We can now state

**THEOREM 1.** *Assume that the set $D_+^*$ of all non $L$-parasitic strings is a context free language.*

*If $H_O(\alpha, k) < \infty$, then the set $O_{(\alpha, k)}$ is a context-free language.*

**PROOF.** If $O_{(\alpha, k)} = \emptyset$, then $O_{(\alpha, k)}$ is regular, hence context-free. We may assume therefore that $O_{(\alpha, k)} \neq \emptyset$, hence by Proposition 2, also $\bar{O}_{(\alpha, k)} \neq \emptyset$. Denote

$$
\text{(4)} \quad C = \{x : x = uv \text{ for some } u \in \bar{O}_{(\alpha, k)} \text{ and } v \in D^*\}.
$$

We have then

$$
\text{(5)} \quad O_{(\alpha, k)} \subset C.
$$

Indeed, if $x \in O_{(\alpha, k)}$, then $x = uv$ for some $u \in \bar{O}_{(\alpha, k)}$ and $v \in D_+^*$. Assertion (5) follows, since $D_+^* \subset D^*$.

Next, we show that $C$ has the property

$$
\text{(6)} \quad \textit{if } x \in C \textit{, then } xy \in C \textit{ for all } y \in D^*.
$$

Indeed, $x \in C$ means that $x = uv$ for some $u \in \bar{O}_{(\alpha, k)}$, hence $xy = u(vy)$ with $u \in \bar{O}_{(\alpha, k)}$ and $vy \in D^*$, that is, $xy \in C$, which proves (6).

---

$^7$ In other words, our convention of denoting a pause of length $k$ simply by the number $k$ is analogous to the convention used in Chapter 3, where strings of $k$ consecutive letters $a$ were denoted by $a^k$.

<!-- page 4 -->

Define now $\bar{C}$ as in Definition 1. Since $C \supset O_{(\alpha, k)} \neq \emptyset$, we obtain $\bar{C} \neq \emptyset$ by Proposition 2. We shall show that

$$
\text{(7)} \quad \bar{C} \subset \bar{O}_{(\alpha, k)}.
$$

Indeed, suppose that $x \notin \bar{O}_{(\alpha, k)}$ and consider two cases, $x \in O_{(\alpha, k)}$ and $x \notin O_{(\alpha, k)}$.

If $x \in O_{(\alpha, k)}$ and $x \notin \bar{O}_{(\alpha, k)}$, then $x = uv$ with $\varphi(v) > 0$ and $u \in \bar{O}_{(\alpha, k)}$. In this case $x \in C$ in view of (5), but $x \notin \bar{C}$, since $u$ is a proper substring of $x$ and $u \in C$ by definition.

If $x \notin O_{(\alpha, k)}$, we distinguish two cases: (i) there exists no $u \in \bar{O}_{(\alpha, k)}$ such that $x = uv$; (ii) $x = uv$ for some $u \in \bar{O}_{(\alpha, k)}$ and $v \in D^*$. In this case necessarily $\varphi(v) > 0$ and $v \in D^* - D_+^*$, since otherwise we would have $x \in O_{(\alpha, k)}$ by property (11) of section 5.1. In case (i) we have $x \notin C$, hence $x \notin \bar{C}$. In case (ii) we have $x \in C$, but $x \notin \bar{C}$, since again, $u$ is a proper substring of $x$ belonging to $C$ by definition.

Thus, in each case $x \notin \bar{O}_{(\alpha, k)}$ implies $x \notin \bar{C}$, which proves (7). It follows from (7) that

$$
\text{(8)} \quad \max\{\varphi(z) : z \in \bar{C}\} \le \max\{\varphi(z) : z \in \bar{O}_{(\alpha, k)}\} = H_O(\alpha, k) < \infty.
$$

We shall now use Theorem 6 of Chapter 3.2.1.2 to show that $C$ is a regular language. Thus, consider the relation $R_C$ in $D^*$ defined by the requirement that $x R_C y$ if and only if for all $z \in D^*$ the condition $xz \in C$ is equivalent to $yz \in C$. To prove that $C$ is regular, we have to show that the relation $R_C$ has a finite index.

Indeed, if $x, y \in C$, then $x R_C y$, since $xz \in C$ and $yz \in C$ for all $z$ by property (6) above. Thus, all strings in $C$ belong to one equivalence class of $R_C$.

Next, in view of inequality (8), we may apply Proposition 3 to show that all strings $x, y$ with $x \notin C$, $y \notin C$, $\varphi(x) > H_O(\alpha, k)$, $\varphi(y) > H_O(\alpha, k)$ are also in one class. Indeed, in this case $xz \notin C$, $yz \notin C$ for all $z$, hence again $x R_C y$.

There remain only a finite number of strings $x$ not in $C$ with $\varphi(x) \le H_O(\alpha, k)$, which may therefore form only a finite number of $R_C$-equivalence classes. Thus, $C$ is a regular set. To complete the proof it is enough to observe that $O_{(\alpha, k)} = D_+^* \cap C$. Since $D_+^*$ is assumed context-free, by Theorem 2 of Chapter 3.2.1.4, we conclude that $O_{(\alpha, k)}$ is also context-free.

#### 5.3.3. *Properties of the sets $O'_{(\alpha, k)}$*

Opposed to condition (11) of section 5.1 asserting that the sets $O_{(\alpha, k)}$ are invariant under concatenation from the right, condition (12) of section 5.1 states that the sets $O'_{(\alpha, k)}$ are invariant under concatenation both from the right and from the left. The invariance from the left makes the concept of motivational horizon inapplicable for the analysis of sets $O'_{(\alpha, k)}$; other concepts are therefore needed.

<!-- page 5 -->

<!-- page 207 -->

First, to facilitate further reference, let us record in the form of a proposition the following immediate consequence of assumption (12) of section 1.

**PROPOSITION 4.** *If for some $x, y, z \in D_{+}^{*}$ we have $xyz \notin O'_{(\alpha, k)}$, then $y \notin O'_{(\alpha, k)}$.*

Indeed, if we had $y \in O'_{(\alpha, k)}$, then we would have $xyz \in O'_{(\alpha, k)}$ for all $x, z \in D_{+}^{*}$ such that $xyz \in D_{+}^{*}$. ■

We now introduce the following

**DEFINITION 2.** Let $x \in O'_{(\alpha, k)}$. The string $u$ is said to constitute an *offense* in $x$, if

(a) $u \in O'_{(\alpha, k)}$,

(b) $x = w_{1} u w_{2}$ for some $w_{1}, w_{2} \in D_{+}^{*}$,

(c) if $u = z_{1} u' z_{2}$ with $\varphi(z_{1}) + \varphi(z_{2}) > 0$, then $v_{1} u' v_{2} \notin O'_{(\alpha, k)}$ for some $v_{1}, v_{2} \in D_{+}^{*}$.

Moreover, if $w_{1}$ in condition (b) is such that $w_{1} \notin O'_{(\alpha, k)}$, then $u$ is said to constitute the *first offense* in $x$.

It will be convenient to say that $u$ is a *substring* of $x$ if $x = z_{1} u z_{2}$; in the case where $\varphi(z_{1}) + \varphi(z_{2}) > 0$, we say that $u$ is a *proper substring* of $x$.

Thus, Definition 2 above states that $u$ is an offense in $x$ if $u$ is a substring of $x$ such that $u \in O'_{(\alpha, k)}$, and moreover (in view of Proposition 4), no proper substring of $u$ belongs to $O'_{(\alpha, k)}$.

We have

**THEOREM 2.** *If $O'_{(\alpha, k)} \neq D_{+}^{*}$, then every string $x \in O'_{(\alpha, k)}$ contains at least one substring $u$ which constitutes an offense in $x$.*

**PROOF.** Assume the contrary, and let $x \in O'_{(\alpha, k)}$ be a string which contains no offense. Thus, there exists no string $u$ satisfying (a)–(c), i.e. no substring of $x$ satisfying (a) and (c). Since $x$ is its own substring (b), and it satisfies (a), it follows that condition (c) is not satisfied for $u = x$. There exists therefore a string $x_{1}$ such that $x = z_{1} x_{1} z_{2}$ with $\varphi(z_{1}) + \varphi(z_{2}) > 0$, while $v_{1} x_{1} v_{2} \in O'_{(\alpha, k)}$ for all $v_{1}, v_{2} \in D_{+}^{*}$. Putting $v_{1} = v_{2} = 0$ we obtain $x_{1} \in O'_{(\alpha, k)}$; furthermore, $\varphi(x) = \varphi(z_{1}) + \varphi(x_{1}) + \varphi(z_{2}) > \varphi(x_{1})$. Thus, $x$ contains a proper substring $x_{1} \in O'_{(\alpha, k)}$, and if $x$ is to contain no offense, $x_{1}$ cannot satisfy condition (c). Proceeding in this manner we come to the conclusion that $0 \in O'_{(\alpha, k)}$, hence by condition (12) of section 5.1, we must have $v_{1} 0 v_{2} = v_{1} v_{2} \in O'_{(\alpha, k)}$ for all $v_{1}, v_{2} \in D_{+}^{*}$, which means that $O'_{(\alpha, k)} = D_{+}^{*}$, contrary to the assumption of the theorem. ■

Next, we have

**THEOREM 3.** *If the set $O'_{(\alpha, k)}$ has the property*

(9) if $uv \in O'_{(\alpha, k)}$, then $u \in O'_{(\alpha, k)}$ or $v \in O'_{(\alpha, k)}$ (or both),

<!-- page 6 -->

<!-- page 208 -->

then for every $x \in O'_{(\alpha, k)}$ the string $u$ constituting the first offense in $x$ is determined uniquely.

**PROOF.** Assume that $x \in O'_{(\alpha, k)}$, and let

$$
x = w_{1} u w_{2} = w_{1}^{*} u^{*} w_{2}^{*}
$$

be two distinct decompositions of $x$, such that $u$ and $u^{*}$ are the first offenses in $x$. Consider first the case $w_{1}^{*} = w_{1}$. Without loss of generality we may assume $u = u^{*} p$ for some $p \in D_{+}^{*}$ with $\varphi(p) > 0$ (see fig. 1).

![Fig. 1 — string decomposition $w_1=w_1^*$, $u=u^*p$](figures/nowakowska1973/sec53_fig1_string_w1_eq.png)

**Fig. 1**

Then $u^{*}$ constitutes a proper substring of $u$, hence we have $v_{1} u^{*} v_{2} \notin O'_{(\alpha, k)}$ for some $v_{1}, v_{2}$ by condition (c) applied to string $u$. Proposition 4 implies then that $u^{*} \notin O'_{(\alpha, k)}$, contrary to the assumption that $u^{*}$ is an offense in $x$.

Suppose now that $w_{1} \neq w_{1}^{*}$. By symmetry, we may assume that $w_{1} = w_{1}^{*} q$ for some $q \in D_{+}^{*}$ with $\varphi(q) > 0$. In this case either $u^{*}$ is a substring of $q$, or vice versa, $q$ is a substring of $u^{*}$.

In the first case (see fig. 2), $q = u^{*} r$ with $r \in D_{+}^{*}$ and $\varphi(r) \geq 0$.

![Fig. 2 — string decomposition $q=u^*r$](figures/nowakowska1973/sec53_fig2_string_q_ustar.png)

**Fig. 2**

We have then $w_{1} = w_{1}^{*} q = w_{1}^{*} u^{*} r$, hence $u^{*}$ is a substring of $w_{1}$. But $u^{*} \in O'_{(\alpha, k)}$ by assumption, and it follows by (12) of section 5.1 that $z_{1} u^{*} z_{2} \in O'_{(\alpha, k)}$ for all $z_{1}, z_{2}$. In particular, putting $z_{1} = w_{1}^{*}$, $z_{2} = r$ we obtain $w_{1} \in O'_{(\alpha, k)}$, contrary to the assumption that $u$ is the first offense in $x$.

In the second case, we may assume that $u^{*} = q r$ for some $r \in D_{+}^{*}$ with $\varphi(r) > 0$. We again consider two cases. First, $u$ may constitute a substring of $u^{*}$, if $r = u r'$ with some $r'$ such that $\varphi(r') \geq 0$, or we may have $u = r r'$ for some $r'$ with $\varphi(r') > 0$. In the first case (see fig. 3), $u^{*} = q u r'$, and $\varphi(q) + \varphi(r') \geq \varphi(q) > 0$, hence $u$ is a

![Fig. 3 — string decomposition $u^*=qur'$](figures/nowakowska1973/sec53_fig3_string_u_in_ustar.png)

**Fig. 3**

<!-- page 7 -->

proper substring of $u^{*}$. Applying condition (c) for $z_{1} = q$, $z_{2} = r'$, $u' = u$, we come to the conclusion that $yuy' \notin O'_{(\alpha, k)}$ for some $y, y'$. Thus, by Proposition 4, we infer that $u \notin O'_{(\alpha, k)}$, contrary to the assumption.

There remains the case $u = rr'$ with $\varphi(r') > 0$ (see fig. 4).

![Fig. 4 — string decomposition $u=rr'$, $u^*=qr$](figures/nowakowska1973/sec53_fig4_string_u_rrprime.png)

**Fig. 4**

Then $r$ is a proper substring of both $u$ and $u^{*}$. Applying condition (c) to the string $r$ we obtain $yry' \notin O'_{(\alpha, k)}$ for some $y, y'$, hence again by Proposition 4 we infer that $r \notin O'_{(\alpha, k)}$.

We now make use of assumption (9) of the theorem, to infer that we must have $q \in O'_{(\alpha, k)}$, since otherwise we could not have $u^{*} = qr \in O'_{(\alpha, k)}$, as required by condition (a) for $u^{*}$. It follows that $w_{1} = w_{1}^{*} q \in O'_{(\alpha, k)}$, contrary to the assumption that $u$ is the first offense. ■

Thus, under condition (9) we may assign to each string in $O'_{(\alpha, k)}$ the substring of it which constitutes the first offense.

Define

$$
\text{(10)} \quad \bar{O}'_{(\alpha, k)} = \{u : u \text{ is a first offense in some string } x \in O'_{(\alpha, k)}\}.
$$

We can now formulate an analogue to Theorem 1 for sets $O'_{(\alpha, k)}$:

**THEOREM 4.** *Assume that $D_{+}^{*}$ is a context-free language. If the set $O'_{(\alpha, k)}$ satisfies the assumption (9), and*

$$
\text{(11)} \quad \max\{\varphi(z) : z \in \bar{O}'_{(\alpha, k)}\} < \infty,
$$

*then $O'_{(\alpha, k)}$ is a context-free language.*

**PROOF.** As in the proof of Theorem 1, it suffices to represent $O'_{(\alpha, k)}$ as an intersection of $D_{+}^{*}$ and a regular set $C$. In the present case we put

<!-- page 8 -->

$$
\text{(12)} \quad C = \{xyz : x \in D^* - O'_{(\alpha, k)},\; y \in \bar{O}'_{(\alpha, k)},\; z \in D^*\}.
$$

Since each string $u \in O'_{(\alpha, k)}$ can be uniquely decomposed into its part $x \in D_{+}^{*} - O'_{(\alpha, k)}$ preceding the first offense, substring $y \in \bar{O}'_{(\alpha, k)}$ constituting the first offense in $u$, and the subsequent part $z \in D_{+}^{*}$, it follows that $O'_{(\alpha, k)} \subset C$ and $O'_{(\alpha, k)} = C \cap D_{+}^{*}$. Thus, it remains to show that the set $C$ defined above is regular. We shall prove that there exists a finite state automaton capable of accepting all strings in $C$ and no other strings.

Indeed, by (11) all strings in $\bar{O}'_{(\alpha, k)}$ are of a finite length not exceeding a certain bound, say $K$. A string belongs to $C$ if, and only if, it contains a substring from $\bar{O}'_{(\alpha, k)}$. Thus, to determine whether or not a given string is in $C$, it suffices to inspect all its substrings of length not exceeding $K$, and determine whether at least one of them is in $\bar{O}'_{(\alpha, k)}$. Clearly, this can be attained by a finite state automaton $\mathscr{A}$ defined as follows. Identify all internal states of $\mathscr{A}$ with all possible strings of length $\le K$, and take as final states all such strings which contain substrings of $\bar{O}'_{(\alpha, k)}$. The transition function for the automaton $\mathscr{A}$ is defined by the requirements:

(1) once a final state is reached, no subsequent scanned letters produce any change of state;

(2) for non-final states described by strings of length $< K$, the transition is to the state-string obtained by adding the scanned letter on the right;

(3) for non-final states described by strings of length $K$, the transition is to the state-string obtained by erasing the first letter on the left, and adding the scanned letter on the right.

Given that the starting state is identified with the empty string, it is obvious that the automaton $\mathscr{A}$ defined above accepts all strings in $C$ and no other strings. ■

#### 5.3.4. *Comments*

Theorems 1 and 4 assert that under certain conditions, the sets $O_{(\alpha, k)}$ and $O'_{(\alpha, k)}$ are context-free languages.

The notion of a context-free language is a linguistic concept par excellence. On the other hand, $O_{(\alpha, k)}$ and $O'_{(\alpha, k)}$ are sets of strings of actions; their connection with the natural language lies only in that they represent classes of strings of actions which fulfill the obligations expressed when $\alpha$ is uttered at moment $k$. The question arises, therefore, how to interpret the assertions of Theorems 1 and 4.

In a somewhat loose interpretation, perhaps closer to a metaphor than to bounds imposed by technicalities of definitions, one may say that the properties described by Theorems 1 and 4 constitute a formal representation of the observable fact that social norms (especially ethical ones) are, as a rule, formulated without reference to specific situations which might serve as contexts for their applicability. Thus, taking religion as an example, a sin is defined as a specific act, and its presence in a string of actions determines the qualification of this string (with few exceptions), regardless of the

<!-- page 9 -->

preceding and subsequent actions, i.e. regardless of the context in which the sin occurs.

Law may perhaps be thought of as somewhat more flexible, in the sense that it occasionally provides classes of contexts in which a given action constitutes an offense, and classes of contexts in which it is not so. This amounts to specifying strings of actions together with the surrounding circumstances as offenses, rather than isolated actions. Again, however, the presence of a string constituting an offense qualifies the string of actions in which the offense is embedded. The preceding or subsequent actions may serve as a factor determining the punishment, but as a rule, not for the qualification of an offense as such. The most serious offenses, such as murder, rape, arson, theft, pushing drugs, etc., are qualified regardless of the context in which they occur. In this sense, one can say that Theorems 1 and 4 reflect certain general regularities in the treatment of the norms of social order, namely the (relative) universality of contexts to which they apply.

#### 5.3.5. *Structural properties of motivationally consistent strings*

Using the concepts introduced in the preceding sections, one may attempt to give a partial answer to the following question: given that we know which utterances are contained in a string $x \in (D \cup M)^*$, together with the moments of their utterance, and given that we know that $x$ is motivationally consistent, what can be asserted about the structural properties of the string $\pi(x)$? Naturally, not too much can be expected: intuitively, the knowledge that someone uttered certain sentences, and that his actions were consistent with these sentences, allows us to determine the string of actions only to the extent that the person in question did whatever he asserted he ought to do, did not do whatever he asserted he should not do, achieved whatever he stated that he wanted to achieve, and avoided all that he stated he did not want. Depending on the content of the utterances, this may provide more or less information about the string actually performed. For instance, if the only utterances are ‘I do not want to eat fish for lunch’ and ‘I ought to telephone Peter before 3 o’clock’, then all we know about the speaker’s activity during the day, if he is known to have produced a consistent string, is that he phoned Peter and had something other than fish for lunch. The inference concerns only the string of actions until 3 o’clock; the actions which followed cannot be inferred from the above utterances and the knowledge that they were fulfilled.

Mainly in order to facilitate further considerations, it will be convenient to introduce some new notations, and extend somewhat the definition of motivational consistency.

Thus, let

$$
\Lambda = M \times N;
$$

elements of $\Lambda$, to be denoted by $\lambda$, $\lambda'$, $\lambda_1$, $\ldots$ etc., are then pairs $(\alpha, k)$ with $\alpha \in M$, $k \in N$.

Given $\lambda \in \Lambda$, let $W_{\lambda}$, $W'_{\lambda}$, $O_{\lambda}$, and $O'_{\lambda}$ have the same meaning as before. Let $\lambda \in \Lambda$

<!-- page 10 -->

be a pair $(\alpha, k)$, and $x \in L$. We say that $x$ is *consistent* with $\lambda$, if $x = uv$ with $\varphi(u) = k$, and the conditions

$$
\text{(13)} \quad uv \in \hat{R}^{-1}(W_{\lambda}) - R^{-1}(W'_{\lambda})
$$

$$
\text{(14)} \quad v \in O_{\lambda} - O'_{\lambda}
$$

are satisfied.$^8$

Further, given $A \subset \Lambda$, we say that $x \in L$ is *consistent with respect to $A$*, if $x$ is consistent with every $\lambda \in A$.

In the present terminology, a string $u \in L_M - L$ is motivationally consistent (according to the definition in section 5.2), if $\pi(u)$ is consistent with respect to the set $A(u)$ of all pairs $(\alpha, k)$ occurring in $u$.

Let us put, for $A$,

$$
\text{(15)} \quad \psi(A) = \{u \in L : u \text{ is consistent with respect to } A\}.
$$

For further reference, let us record the following

**PROPOSITION 5.** *If $A \subset B$ are two subsets of $\Lambda$, then*

$$
\text{(15)} \quad \psi(B) \subset \psi(A).
$$

We can now formulate the problem posed at the beginning of the present section, and an answer to it, as follows:

Suppose we know that a string $x \in (D \cup M)^*$ contains $A(x) \subset \Lambda$ as the set of its utterances and their moments. Then, if $x$ is motivationally consistent, we may assert that

$$
\pi(x) \in \psi(A(x)).
$$

The problem is thus reduced to describe (to some extent) the structure of strings in the sets $\psi(A)$, or, simpler still, in the sets $\psi(\{\lambda\})$ where $\lambda \in \Lambda$.

Suppose that $\lambda = (\alpha, k)$, and assume first that at least one of the sets $W_{\lambda}$ and $O_{\lambda}$ is nonempty. In section 5.3.3 we defined the $O$-motivational horizon $H_O(\lambda)$ as the maximum of lengths of strings in $\bar{O}_{\lambda}$. If $W_{\lambda} \neq \emptyset$, define similarly the $W$-motivational horizon $H_W(\lambda)$ as

$$
\max \{n : (s, n) \in W_{\lambda}\}
$$

and put

$$
H(\lambda) = \max \{H_O(\lambda), H_W(\lambda)\}.
$$

We may then say that every string $\pi(x) \in \psi(\{\lambda\})$ can be decomposed into the concatenation $uvw$, where $\varphi(u) = k$, $\varphi(v) = H(\lambda) - k$, and $v \in \hat{R}_u^{-1}(W_{\lambda}) \cap O_{\lambda}$.

---

$^8$ As before, we assume that condition (13) is automatically satisfied if $W_{\lambda} = W'_{\lambda} = \emptyset$, and similarly for condition (14).

<!-- page 11 -->

Note that the inference about strings in $\psi(\{\lambda\})$ can, in some cases, reach also into the past, before the moment $k$ of the utterance $\alpha$: not only can one make assertions about the ‘middle’ string $v$, but also one can assert that $u$ is such that $\hat{R}_u^{-1}(W_\lambda) \neq \emptyset$.

To use an obvious example, if someone asserts that he wants to take off his shoes, then he must have put them on some time before.

Now, if the set $W'_\lambda$ is nonempty, the inference about the string $\pi(x)$ cannot go beyond repeating the definition, namely that $\pi(x) \notin R^{-1}(W'_\lambda)$. If $O'_\lambda \neq \emptyset$, we may infer that the substring $vw$, following the utterance $\alpha$ at the moment $k$, satisfies the condition $vw \notin O'_\lambda$. Thus, there exist no $z_1$, $z_2$ such that $vw = z_1 q z_2$, with $q$ constituting the first offense in $O'_\lambda$.

### 5.4. MODELS OF CONFLICT

#### 5.4.1. *Preliminaries*

Let $C \subset \Lambda$ be such that $\psi(C) = \emptyset$, i.e. there exists no string of actions which would satisfy the requirements asserted in the sentences of $C$. Such a situation may be thought of as a general model of a conflict: in view of the impossibility of attaining all goals as expressed in sentences of $C$ by means of actions meeting the restrictions expressed also by sentences of $C$, one is forced to choose a string of actions which only partially satisfies the requirements of $C$.

In other words, the condition $\psi(C) = \emptyset$ means that there is no string $x$ consistent with all $\lambda \in C$, i.e. for any string $x$ there exists at least one $\lambda = (\alpha, k) \in C$ such that $x$ is not consistent with $\lambda$.

The latter means that $x = uv$ with $\varphi(u) = k$ and at least one of the four conditions holds:

$$
\begin{aligned}
\text{(a)}\ & x \notin \hat{R}^{-1}(W_\lambda); & \text{(b)}\ & x \in R^{-1}(W'_\lambda); \\
\text{(c)}\ & v \notin O_\lambda; & \text{(d)}\ & v \in O'_\lambda
\end{aligned}
$$

with the provision that conditions (a)–(d) are not applicable if sets $W_\lambda$, $W'_\lambda$, $O_\lambda$, and $O'_\lambda$ are empty.

Since we will be dealing with strings which are not consistent with some subsets of $\Lambda$, it will be convenient to simplify the matter and assume that for each $\lambda$ exactly one of the sets $W_\lambda$, $W'_\lambda$, $O_\lambda$, and $O'_\lambda$ is nonempty.$^9$

This determines the division of every set $C$ into four subsets, to be denoted by $C_W$, $C_{W'}$, $C_O$, and $C_{O'}$, where

$\lambda \in C_W$ if $W_\lambda \neq \emptyset$,

$\lambda \in C_{W'}$ if $W'_\lambda \neq \emptyset$,

etc.

---

$^9$ This may always be achieved by representing, if necessary, every sentence as a conjunction of ‘atomic’ sentences, each containing only one of the four functors $W$, $W'$, $O$, and $O'$. For an example, see the end of section 5.1.
