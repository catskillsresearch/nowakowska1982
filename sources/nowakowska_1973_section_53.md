---
source_pdf: nowakowska_1973_section_53.pdf
book: Language of Motivation and Language of Actions (Mouton, 1973)
section: 5.3 Language of actions with embedded verbal parts (pp. 200–210)
ocr_method: cursor-vision-triple-merge
verification_status: draft
figures_dir: figures/nowakowska1973
figures:
  - sec53_fig1_string_w1_eq.png
  - sec53_fig2_string_q_ustar.png
  - sec53_fig3_string_u_in_ustar.png
  - sec53_fig4_string_u_rrprime.png
---

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
