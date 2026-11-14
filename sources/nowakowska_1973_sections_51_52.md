---
source_pdf: nowakowska_1973_sections_51_52.pdf
ocr_method: cursor-vision-triple-merge
verification_status: draft
---

# Transcription (LLM vision OCR)


<!-- page 1 -->

# LANGUAGE OF ACTIONS WITH EMBEDDED VERBAL PARTS

## 5.1. THE ADDITIONAL PRIMITIVE CONCEPTS

The system of five primitive concepts $\langle D, L, \varphi, S, \rho \rangle$ defining language of actions and its semantics will now be enriched by additional primitive concepts, namely $M$, $W$, $W'$, $O$, and $O'$, in order to obtain a model for connecting non-verbal actions with a certain part of language of motivation.

It ought to be pointed out at the very beginning, that the construction presented below will involve considerable simplifications, some of them inherent in the model, and some introduced merely to achieve greater clarity of exposition. These simplifications will be discussed and illustrated.

In what follows we retain the assumptions, interpretation, and notational conventions of Chapter IV.

Thus, we consider the system

$$(1) \quad \langle D, L, M, \varphi, S, \rho, W, W', O, O' \rangle.$$

1 and 2) As before, $D$ is the set of actions, and $L \subset D^*$ is the language of actions, i.e. the set of all physically admissible strings in $D^*$. However, in the present interpretation, we exclude from $D$ actions consisting of the utterance of sentences.$^1$

3) $M$ is a (possibly infinite) set such that

$$(2) \quad D \cap M = \emptyset.$$

The elements of $M$, denoted generally by small initial letters of the Greek alphabet, will be interpreted as sentences involving at least one of the four functors ‘I want’, ‘I ought to’ and their opposites ‘I don’t want’, ‘I shouldn’t’.

Assumption (2) is a formal counterpart of the above mentioned exclusion from the set $D$ of uttering sentences.

4) The function $\varphi$, defined on $D \cup M$, will be interpreted as duration (of an

---

$^1$ In Chapter 4, the interpretation of elements of $D$ was not specified beyond the statement that they are to be treated as actions; consequently, it was possible to treat elements of $D$ also as utterances.

<!-- page 2 -->

# LANGUAGE OF ACTIONS WITH EMBEDDED VERBAL PARTS

action in $D$, or sentence in $M$). However, we do not assume that $\varphi$ is strictly positive$^2$ on $M$ (we retain the assumption that $\varphi(d) > 0$ for $d \in D$).

5 and 6) $S$ and $\rho$ (and also the extended relation $R$) have the same interpretation as in Chapter 4.

7) $W$ is a quaternary relation in $M \times N \times S \times N$, where $N$ is the set of all nonnegative integers. It will be convenient to treat $W$ as a binary relation between pairs $(\alpha, k)$, $\alpha \in M$, $k \in N$ and time-results $(s, n) \in S \times N$, and use the symbol

$$(3) \quad (\alpha, k)\, W\, (s, n)$$

to denote the fact that the quadruplet $(\alpha, k, s, n)$ is in the relation $W$. Symbol (3) will be interpreted as follows: the sentence $\alpha$ uttered at the moment $k$ expresses (among other things) that the time-result $(s, n)$ is wanted by the speaker. For $\alpha \in M$, $k \in N$ denote

$$(4) \quad W_{(\alpha, k)} = \{(s, n) : (\alpha, k)\, W\, (s, n)\};$$

$W_{(\alpha, k)}$ is then the set of all time-results which are asserted as wanted when the sentence $\alpha$ is uttered at the moment $k$ (of course, $W_{(\alpha, k)}$ may be empty).

8) $W'$ is a ternary relation in $M \times N \times S$. We shall write

$$(5) \quad (\alpha, k)\, W'\, s,$$

to denote the fact that the triple $(\alpha, k, s)$ is in $W'$. We interpret (5) as follows: the sentence $\alpha$ uttered at the moment $k$ asserts that the result $s$ is not wanted (‘unwanted’) by the speaker. We define

$$(6) \quad W'_{(\alpha, k)} = \{(s, n) : (\alpha, k)\, W'\, s,\; n \in N\};$$

thus, $W'_{(\alpha, k)}$ is the set of all possible time-results $(s, n)$, where the result $s$ is asserted as ‘unwanted’ when the sentence $\alpha$ is uttered at the moment $k$ (here $n$ may be arbitrary). We assume that

$$(7) \quad W_{(\alpha, k)} \cap W'_{(\alpha, k)} = \emptyset$$

for all $\alpha \in M$, $k \in N$.

9 and 10) $O$ and $O'$ are ternary relations in the set $M \times N \times D^*_+$, where $D^*_+$ is the class of all non $L$-parasitic$^3$ strings in $D^*$. We shall use the symbols

$$(8) \quad (\alpha, k)\, O\, u \quad \text{and} \quad (\alpha, k)\, O'\, u$$

---

$^2$ Depending on the intended interpretation, one can sometimes assume that the durations of times needed to utter certain sentences are negligible compared to the durations of actions.

$^3$ We remind the reader that $u \in D^*$ is $L$-parasitic if $w_1 u w_2 \notin L$ for all $w_1, w_2 \in D$. Thus, $u$ is not $L$-parasitic, if it may appear as a substring in at least one string in $L$ (in particular, strings in $L$ are not $L$-parasitic).

<!-- page 3 -->

# LANGUAGE OF ACTIONS WITH EMBEDDED VERBAL PARTS

to denote the fact that $(\alpha, k, u) \in O$ and $(\alpha, k, u) \in O'$, respectively. Further, let

$$(9) \quad O_{(\alpha, k)} = \{u \in D^*_+ : (\alpha, k)\, O\, u\}$$

and

$$(10) \quad O'_{(\alpha, k)} = \{u \in D^*_+ : (\alpha, k)\, O'\, u\}.$$

We shall interpret the relations $O$ and $O'$ as follows: whenever the sentence $\alpha$ is uttered at the moment $k$, it asserts that the subsequent string of actions ought to be chosen from $O_{(\alpha, k)}$ and should not be chosen from $O'_{(\alpha, k)}$.

We assume that for all $\alpha \in M$, $k \in N$, $u, v, w \in D^*_+$:

$$(11) \quad \text{if } u \in O_{(\alpha, k)} \text{ and } uv \in D^*_+, \text{ then } uv \in O_{(\alpha, k)};$$

$$(12) \quad \text{if } v \in O'_{(\alpha, k)} \text{ and } uvw \in D^*_+, \text{ then } uvw \in O'_{(\alpha, k)}.$$

It follows that the sets $O_{(\alpha, k)}$ and $O'_{(\alpha, k)}$ are not necessarily disjoint.

Finally, as a formal expression of the intended interpretation of elements of $M$ as sentences involving at least one of the four functors ‘I want’, ‘I don’t want’, ‘I ought’, and ‘I shouldn’t’, we assume that

$$(13) \quad \text{for any } \alpha \in M,\, k \in N,\, \text{at least one of the sets } W_{(\alpha, k)},\, W'_{(\alpha, k)},\, O_{(\alpha, k)} \text{ and } O'_{(\alpha, k)} \text{ is nonempty.}$$

**COMMENTS AND EXAMPLES.** As already pointed out, the suggested system involves considerable simplifications of the real interrelations between utterances and non-verbal actions. The simplifications specifically connected with language of actions have already been discussed in Chapter 4, and will not be repeated here. Further simplifications are due to the fact that only four of the motivational functors are considered, and moreover, even those four are treated in an oversimplified manner.

It may be argued, however, that this does not impose such a serious restriction as might appear at first glance. The point is that in studying various possible relations between utterances and actions and their results, one can distinguish four basic ‘extreme’ types of such relations, all others being a certain mixture of these four.

Thus, sentences with a given functor (not necessarily one of the four discussed in this chapter) may refer primarily to the space of results, or to the space of actions. On the other hand, they may have strong time connotations, or be ‘timeless.’ This gives roughly two dichotomous classifications, and the considered four functors are, in some approximation, representatives of the obtained four classes.

Thus, functors ‘I want’ and ‘I don’t want’ refer primarily to the results, and not to strings of actions, while ‘I ought to’ and ‘I shouldn’t’ refer primarily to strings of actions, and not to the results.

Of course, it is easy to produce examples of the use of the first two functors for actions, or of the second two for results; nevertheless, the accepted division seems to correspond to a general semantic intuition.

<!-- page 4 -->

# LANGUAGE OF ACTIONS WITH EMBEDDED VERBAL PARTS

Second, the positive functors ‘I want’ and ‘I ought to’ refer to more specific moments of time than their opposites ‘I don't want’ and ‘I shouldn't’. Here also one can easily point out examples against such a division, but it appears that it nevertheless reflects some general semantic intuition.

As a result of these two dichotomies, we consider four types of relations between utterances and actions or results, accepting such properties of these relations which appear plausible.

A relation between utterances and time-results is exemplified by the relation $W$ (‘I want’). A sentence, uttered at a given moment, determines the set of time-results towards which the speaker's attitude is expressed by the corresponding functor (in this case ‘I want’; the formal definition of such a set is given by formula (4)).

In this category of functors one could include also ‘I like’, ‘I prefer’, ‘I would like’, etc. As examples, consider sentences such as ‘I want to see them both sometime next week’, ‘I would like my steak well done’, etc., where the reference to time, even if not explicit, may be to some extent inferred, hence leading to the determination of the sets of form (4).

Second, the relations between utterances and results, regardless of their times of occurrences, are exemplified by $W'$ (‘I don't want’). A sentence determines then a set of results, which can subsequently be transformed to a set of time-results, whose moments of occurrence are unrestricted; formula (6) gives the definition of such a set of time-results.

As an example, we may consider a sentence such as ‘I don't want to become a sailor’; here there is no specific time-limit concerning the result ‘becoming a sailor’. Of course, it is possible to formulate a sentence with the functor ‘I don't want’ referring to a specific time-result, but this, as a rule, involves mentioning the time explicitly (‘I don't want to go to the cinema tonight’).

The assumption about the relations $W$ and $W'$ (assumption (7)) states that the same sentence uttered at the same time is not self-contradictory, in the sense that it cannot state that a result $s$ is undesired (‘unwanted’), and that a time-result of the form $(s, n)$ is wanted.

In practical situations, in order to satisfy this assumption, one might have to interpret appropriately the concept of a result $s$. Thus, in sentences of the form ‘I want the object $A$ because of $a$, and I don't want this object because of $b$’, there would be two different results $s$, namely (wanted) object $A$ with properties $a$, and (unwanted) object $A$ with properties $b$.

Finally, the relations between utterances and strings of actions may be more strongly related to time (as exemplified by the functor ‘I ought to’), or be more timeless (as exemplified by the functor ‘I shouldn't’).

The sentences involving these functors are interpreted as asserting a certain promise (or: obligation), namely to do something, or refrain from doing something. Conditions (11) and (12) imposed on the sets $O_{(\alpha, k)}$ and $O'_{(\alpha, k)}$ respectively, reflect the intuition that the obligation to do something is fulfilled as soon as it is done,

<!-- page 5 -->

# LANGUAGE OF ACTIONS WITH EMBEDDED VERBAL PARTS

and no subsequent actions can change this state of affairs (assumption (11)), while the obligation not to do something can only be broken, but never completely fulfilled. To use an extreme example, consider the utterance ‘I ought to mail this letter before noon today’. Then a string of actions consisting of eating breakfast, mailing the letter, and (say) robbing a bank, would fulfill the obligations stated in the above sentence. The point of assumption (11) is that, in the above case, ‘robbing a bank’ may be replaced by any other string of actions, without affecting the status of the string from the point of view of fulfilling the obligation asserted in the sentence.

On the other hand, it is assumed (assumption (12)) that there is no moment at which the obligation asserted in a sentence involving the functor ‘I shouldn’t’ is discharged. To use an example, consider the sentence ‘I shouldn’t steal’. Then any string involving stealing, no matter what the actions preceding or following the theft, breaks the obligation of the sentence.

Of course, it would also be easy to include in the considerations sentences with ‘I shouldn’t’ referring to a specific time, such as ‘I should not drink alcohol today’, where the obligation asserted can be discharged in a definite time. The properties of strings breaking the obligations would then be analogous to those of strings which fulfill the obligations imposed by sentences with ‘I ought to’.

The case of such sentences was, however, excluded from consideration in order to avoid complications of a purely technical, and not conceptual, character.

Finally, it ought to be remarked that in this model, $\alpha$, $\beta$, $\ldots$ stand for composite sentences, which may involve several functors, each referring to possibly different objects. In order to determine which particular results or strings of actions are in the relations $W$, $W'$, $O$, and $O'$ with a given sentence, one can use the rules developed in Chapter 2.

To use a simple example, the sentence ‘Since I want to inform John about $x$ as soon as possible, I ought to write to him immediately, but since I do not want anyone else to know about $x$, I should write a letter and not a postcard.’

This sentence, call it $\alpha$, is in the relation $W$ with time-results such as ‘John knows about $x$ at time $t'$’; in the relation $W'$ with results such as ‘Peter knows about $x$’; in the relation $O$ with strings of actions involving writing a letter to John and mailing it, and finally, in relation $O'$ with strings of actions such as writing and mailing a postcard to John.

Clearly, $\alpha$ can be decomposed into the conjunction of simple sentences such as ‘I want to inform John about $x$’, ‘I don’t want anyone to know about $x$’, ‘I ought to write a letter to John’, ‘I ought to mail a letter to John’, ‘I should not write a postcard to John’, etc.

<!-- page 6 -->

# LANGUAGE OF ACTIONS WITH EMBEDDED VERBAL PARTS

## 5.2. CONSISTENCY BETWEEN VERBAL AND NON-VERBAL ACTIONS

### 5.2.1. Preliminary concepts

As in Chapter 4, we denote by $(D \cup M)^*$ the monoid of all finite strings of elements of $D \cup M$, with inserted pauses.

We assume that the function $\varphi$ is extended from $D \cup M$ to $(D \cup M)^*$ in an analogous way, as it was done in Chapter 4.

We now define the mapping
$$\pi: (D \cup M)^* \to D^*$$
as follows. Let $x \in (D \cup M)^*$; then $x$ is of the form
$$(1) \quad c_1 d_1 c_2 d_2 \ldots c_r d_r c_{r+1}$$
for some $r$, where $d_1, \ldots, d_r$ are actions in $D$ (not necessarily distinct), and each $c_k$ is a string in the monoid $M^*$ (where $M^*$ is the set of all strings of alternating sentences of $M$ and pauses).$^4$

For $x$ of the form (1), we put
$$(2) \quad \pi(x) = \varphi(c_1) d_1 \varphi(c_2) d_2 \ldots \varphi(c_r) d_r \varphi(c_{r+1});$$
thus, $\pi(x) \in D^*$.

Obviously, $\pi$ is a homomorphism, that is
$$\pi(xy) = \pi(x)\pi(y)$$
for all $x, y \in (D \cup M)^*$.

Next, denote
$$(3) \quad \pi^{-1}(L) = L_M \subset (D \cup M)^*$$
where $L \subset D^*$ is the language of actions.$^5$

Thus, elements of $L_M$ are physically admissible strings involving both physical (non-verbal) actions and utterances of sentences in $M$. The restrictions concern only the former (elements of $D$): a string $x \in (D \cup M)^*$ is in $L_M$ if, after disregarding the utterances in $x$, i.e. considering only $\pi(x)$, one obtains an admissible string of actions (an element of $L$). The utterances in $x$ may be unrelated to actions or unrelated among themselves.

For the purpose of formulating the definition of motivational consistency, it will be necessary to distinguish also the verbal parts of strings $x \in (D \cup M)^*$. Theoretically, this could be attained by constructing a homomorphism $(D \cup M)^* \to M^*$ analogous to the one above.

---

$^4$ Thus, each $c_j$ is a string of the form $n_0 a_1 n_1 \ldots a_k n_k$ for $n_0, \ldots, n_k \in N$ and $a_1, \ldots, a_k \in M$.

$^5$ Roughly speaking, if $x$ is a string in $(D \cup M)^*$, then $\pi(x)$ represents its non-verbal part (the behavioural part of $x$). With some simplification, $\pi(x)$ comprises those elements of $x$ which might be allowed as evidence in an English court.

<!-- page 7 -->

# LANGUAGE OF ACTIONS WITH EMBEDDED VERBAL PARTS

to the homomorphism $\pi$. It will, however, be more convenient to proceed differently, and define the *representation of the verbal part* of $x \in L_M - L$ as a (finite) sequence of decompositions

$$(4) \quad x = u_1 \alpha_1 v_1 = u_2 \alpha_2 v_2 = \dots$$

defined inductively as follows:

(a) $u_1 \alpha_1 v_1$ is the (unique) decomposition with $\alpha_1 \in M$, $u_1 \in D^*$;

(b) if $x = u_k \alpha_k v_k$ is already defined, and $v_k \in D^*$, then sequence (4) ends at the $k$-th decomposition. Otherwise, $x = u_{k+1} \alpha_{k+1} v_{k+1}$ is defined by the requirement $\alpha_{k+1} \in M$, $u_{k+1} = u_k \alpha_k z$ with $z \in D^*$.

Thus, sequence (4) contains as many decompositions as there are elements of $M$ in $x$, and $\alpha_1, \alpha_2, \ldots$ denote the successive sentences of $M$ uttered in $x$.

### 5.2.2. *Motivational consistency*

Consider now a string $x \in L_M - L$ and let

$$x = u_1 \alpha_1 v_1 = u_2 \alpha_2 v_2 = \cdots$$

be the decomposition of its verbal part. Then $\pi(u_k)$ and $\pi(v_k)$ are strings of non-verbal actions performed before and after uttering the $k$-th sentence of $x$, and

$$\pi(x) = \pi(u_k)\,\varphi(\alpha_k)\,\pi(v_k)$$

for all $k$. Moreover, the $k$-th sentence $\alpha_k$ is uttered at the moment $\varphi(u_k)$. Since $\pi(x) \in L$ by definition, $\pi(u_k)$ and $\pi(v_k)$ are parts of strings in $L$; they are not $L$-parasitic.

For simplicity denote

$$(5) \quad \begin{cases} W_k = W_{(\alpha_k,\,\varphi(u_k))}, \quad W'_k = W'_{(\alpha_k,\,\varphi(u_k))} \\ O_k = O_{(\alpha_k,\,\varphi(u_k))}, \quad O'_k = O'_{(\alpha_k,\,\varphi(u_k))} \end{cases}$$

Thus, $W_k$ is the set of all time-results asserted as wanted in the $k$-th successive utterance in the string $x$, etc.

**DEFINITION 1.** *The string $x \in L_M - L$ is said to be motivationally consistent if the following four conditions hold:*

$$(6) \quad \pi(x) \in \bigcap_k \hat{R}^{-1}(W_k);$$

$$(7) \quad \pi(x) \notin \bigcup_k R^{-1}(W'_k);$$

$$(8) \quad \pi(v_k) \in O_k, \quad k = 1, 2, \ldots$$

$$(9) \quad \pi(v_k) \notin O'_k, \quad k = 1, 2, \ldots$$

<!-- page 8 -->

# LANGUAGE OF ACTIONS WITH EMBEDDED VERBAL PARTS

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
