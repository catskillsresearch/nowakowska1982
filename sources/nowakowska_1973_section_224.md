---
source_pdf: nowakowska_1973_section_224.pdf
book: Language of Motivation and Language of Actions (Mouton, 1973)
section: 2.2.4 Model interpretation of motivational calculus (pp. 79–89)
ocr_method: cursor-vision-triple-merge
verification_status: draft
figures_dir: figures/nowakowska1973
figures:
  - fig1_epistemic_sets.png
  - fig2_v_in_intersection.png
  - fig3_sets_in_v_complement.png
  - fig4_functor_G.png
  - fig5_functors_C_Cprime.png
  - fig6_functors_W_Wprime_Pf.png
  - fig7_functor_Hprime.png
---

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
