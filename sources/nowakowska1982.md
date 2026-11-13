---
source_pdf: nowakowska1982.pdf
ocr_method: cursor-vision-triple-merge
verification_status: draft-with-editorial-symbol-fixes
editorial_notes: |
  Patched known 1980s typesetting/OCR traps and print typos (Google notes):
  - p.144–145: pause # and duration φ kept as LaTeX \# / \varphi (not =If / qJ).
  - p.149: ≠ ∅, ∩, L \ R^{-1} kept as LaTeX (not =1= (/), (), L ",-R-I).
  - p.150: strongly attainable uses ⋂ (print wrongly has ⋃).
  - p.153–154: ≽_soc / ≻_x / B kept as LaTeX (not ~ soc / »soe / J3).
  - p.159–160: T ⊆ L (print T ∈ L); (a) if xy ∈ L (print “is”); hats on T̂, Û kept.
  - p.169–171: automaton tuple normalized to ⟨U,B,Θ,D,#,τ,π⟩ to match prose;
    u_j = π(u_{j-1}, b_{j-1}, d_j) (print n_{j-1} typo).
---

# Transcription (LLM vision OCR)


<!-- page 1 -->

MARIA NOWAKOWSKA

# A FORMAL THEORY OF ACTIONS: SYNTAX AND SEMANTICS OF BEHAVIOUR

## 1. INTRODUCTION

The theory which follows is of an interdisciplinary character. It integrates within one system the psychological, linguistic, logical, situational and decisional aspects of behaviour. In short, it is a system which unifies thought, action and situation.

This theory was introduced first in [5] and subsequently developed and applied in [6–12]. It explores the idea that behaviour, verbal or not, exhibits close analogies with language and consequently, may be analysed by methods of mathematical linguistics. Elementary actions are treated as “words” in a certain vocabulary, and admissible strings of actions — as expressions in a ‘language of actions’. Furthermore, outcomes of strings of actions may be regarded as ‘meanings’ in the so defined language of actions, thus constituting its semantics.

Any situation determines, and is actually characterized by, the class of all possible and/or admissible actions which can be performed in it. Thus, each actor who faces a situation, must act within a system of constraints imposed by it, i.e. within the language of actions specific for this situation. The actor has to decide which course of actions to choose in order to achieve a given goal or goals. Therefore, a formal theory of actions comprises the predecisional, decisional and post-decisional aspects of behaviour, and constitutes in fact an extension and complementation of decision theory, in the sense that it covers the situational and dynamic aspects of decision making.

It is worth while stressing that the idea of extending the concept of language to the case of actions and non-verbal behaviour, preceded by at least 5 years a similar programme announced in 1976 by J. Piaget during the Psychological Congress in Paris. It is equally important to stress that the unification in one system of thought and action, the

---

W. Gasparski *et al.* (eds.), *Praxiological Studies*

© PWN—Polish Scientific Publishers—Warszawa 1983

<!-- page 2 -->

introduction of the concepts of linguistic representation of motivation in the decision process, showing the rules of approximate reasoning as rules of inference from the natural language, were introduced for the first time in the literature in [5]. The unifying role of this theory lies also in the fact that it becomes possible to consider ‘mixed’ strings containing verbal and non-verbal behaviour, to analyse the relations between, on the one hand, the class of sentences (verbal actions), in which plans and goals are formulated, actions are explained and justified, etc., and on the other hand — the subsequent strings of actions, motivational horizon, satisfiability, motivational consistency, and so on. In short, it becomes possible to analyse various classes of constraints imposed by utterances on subsequent non-verbal actions.

## 2. THE SYSTEM AND ITS INTERPRETATION

According to the above general intuition, the primitive concepts of the system may be taken as a sixtuplet

$$
\langle D, \#, \varphi, L, S, R \rangle
$$

(1)

with the following interpretation.

The set $D$ consists of elementary actions, with one action $\#$ distinguished, to be interpreted as ‘pause’ (any action which is outside the scope of interest for the description of a given situation being analysed). The function $\varphi$ represents the duration of an action, i.e. $\varphi(d)$ is the time needed to perform $d$. For simplicity it is assumed that $\varphi(\#)=1$, the longer pauses being represented by concatenations $\# \# \ldots \#$.

Composite actions will be, by definition, strings of elementary actions $d_1 d_2 \ldots d_n$. Which actions should be taken in a particular context as elementary and which as composite, is largely a matter of convenience for the particular goal one has in mind when applying the system (1) to a description of real situations.

In the approach presented, the starting point is the recognition of a formal analogy between the set of composite actions and language, as stated at the beginning. Accordingly, in the class $D^*$ of all finite strings of elementary actions, one distinguishes those which are admissible in some specified sense ; these strings constitute, by definition,

<!-- page 3 -->

the language of actions $L$ so that $L$ is a subset of $D^*$. Admissibility of a string may be interpreted in a number of ways, depending on the goal of analysis. Thus, $L$ may be interpreted as the set of strings of actions which are:

(1) physically admissible, that is, physically possible to perform. This leads to a structural analysis of various specific action situations, in particular those studied in the psychology of work.

(2) psychologically admissible for a given person. The class of all such ‘languages of actions’ may constitute a basis for creating a special personality theory, in which the concept of personality would be explicated and taxonomized in terms of ‘grammatical rules’ for various languages of actions.

(3) socially admissible, i.e. consistent with a given social role. Here the analysis might provide the structural characterization and taxonomy of social roles.

(4) organizationally admissible, i.e. acceptable in a given organization. This analysis might lead to a foundation of organization theory based on a linguistic theory of actions. As opposed to the ‘language of social roles’, based mostly on intuitive acceptance or rejection of a given string as consistent or inconsistent with the considered social role, here the criteria for a string of actions to belong to $L$ are expressed formally by the norms, regulations and customs of a given organization.

(5) admissible for a given object. The idea here is that each object generates a set of appropriate strings of actions, admissible in view of the structure of the object. In other words, one can speak of actions which are ‘grammatical’ for a given object, and those which are not grammatical (as an example, one can think here of an object such as a computer, and the actions of operating it).

In the case of a certain configuration of objects related in some ways among themselves (by relations such as being a part of, domination, etc.), there arises a problem of relations between the ‘languages’ and these objects, possibly expressible in terms of set-theoretical operations. It might seem that the configurations of larger numbers of objects, with a complicated relational structure, would impose more constraints on the generated actions, and hence lead to a smaller class of admissible strings of actions, than the ‘looser’ con-

<!-- page 4 -->

figurations, with a smaller number of objects. Easy examples, however, show that it need not be so in general.

A particular case of a configuration of objects is the environment ; it therefore generates a set of appropriate actions. All other actions, from outside this set, are therefore diagnostic in the sense that they represent those aspects of activity which are related to internal factors of the acting person, his motivation, plan of actions, etc.

Analogously, a problem is also a particular configuration of objects (stimuli), and generates its own set of actions — solutions (possibly this set is empty, or consists of one element only). Thus, one can consider ‘grammars’ of problems, that is, algorithms of solving them.

(6) admissible in a given methodology or theory. This interpretation applies especially when one treats scientific activity within the framework of system (1). One can, for instance, interpret scientific methods as sets of well defined and structured procedures (i.e. strings of actions). This allows the consideration of every method as a separate language of actions $L$, or alternatively, its treatment as a ‘sublanguage’ of a universal language of actions $L$ of a given theory or set of theories. Such an approach permits the formalization of a theory of research.

The remaining two primitive concepts of system (1) have the following interpretation. An action, composite or not, leads generally to certain results (outcomes) ; accordingly, the set of all outcomes which are of interest in a given context will be denoted by $S$. The pairs $(s, t)$, where $s \in S$ and $t$ is a moment of time, will be referred to as time-results, and $(s, t)$ will be interpreted as an occurrence of $s$ at time $t$. The connection between actions and results will be expressed by postulating that each string of actions in $L$ leads to the occurrence of some (usually more than one) time-results. The formal counterpart here is the relation $R$, the last primitive concept of system (1), holding between strings of actions in $L$ and time-results $(s, t)$. The symbol $uR(s, t)$, where $u \in L$, $s \in S$ and $t$ is a time moment means that performing $u$ leads to the occurrence of $s$ at the time $t$ (counting from the moment of originating the string $u$). Naturally, one string of actions may lead to several time-results, and similarly, one time-result may be brought about by various strings of actions, so that the relation $R$ is, in general, not one-to-one.

<!-- page 5 -->

## 3. THE MAIN DIRECTIONS OF RESEARCH

The formal analysis of system (1) can be carried out independently of the different possible interpretations (though it is, of course, strongly guided by them). The main lines of research, of which some will be discussed in more detail in subsequent paragraphs, are :

(a) analysis of the structure of language of actions $L$, through the application of some concepts borrowed directly from formal linguistics (generative grammars, distributional classes, parasitic strings, etc.). These concepts acquire then an action-theoretical interpretation and become useful tools in explicating the ‘grammatical’ features of action situations.

In particular, parasitic strings (roughly: those strings which are neither admissible, nor can constitute fragments of admissible strings) provide valuable information about the structure of $L$. For instance, where $L$ is the language of actions consisting of strings which are ‘psychologically admissible’ for a given person, the parasitic strings reflect the person’s ‘inner constraints’, which prevents him behaving in certain ways. One therefore obtains a formal description of behavioural characteristics of personality.

(b) The analysis of attainability of some outcomes, or generally, some configurations of outcomes (composite goals). If a given goal is attainable (i.e. there is at least one string of actions leading to this goal), the natural topics of study are various types of effectiveness and optimality. If a given composite goal is not attainable, but various partial attainments are possible, one obtains a model of internal conflict of motives.

A rather unexpected result here is that a relatively simple conflict of four competing motives which cannot (say, because of situational constraints) be satisfied jointly, can take on one of 113 non-equivalent forms, depending on which of the pairs of triplets of motives are jointly satisfiable, and which are not.

(c) The analysis of verbal behaviour and its relation to non-verbal behaviour. Here one distinguishes in the ‘vocabulary of actions’ $D$ a subset consisting of actions having the form of utterances. By restricting the latter to those in which a person evaluates, explains, justifies,

<!-- page 6 -->

etc. his past or future actions, one obtains a fragment of natural language, which constitutes a linguistic representation of motivation.

The principal lines of research here are :

(c1) A decision model based on the assumption that choice is determined by evaluations of the alternatives on various scales of ‘motivational space’ (e.g. the SEU model, connecting decisions with subjective probabilities and utilities is a special case here). Even leaving both the nature of the scales and decision function unspecified, one can apply the impossibility theorem of K. J. Arrow [1] by treating the decision as ‘social choice’, and particular evaluations as ‘votes’. In this way one obtains certain very general deductive consequences concerning the rules of decision making, corresponding to some ways of solving conflicts known in dynamic psychology.

(c2) A motivational calculus, being a set of rules of inference from those utterances in natural language which involve motivational functors, such as ‘I want’, ‘I ought to’, ‘I am glad that’, ‘I know’, etc. These rules make it possible, in turn, to formalize the inference about motivation, using principles analogous to those in the logical theory of enthymemes and sorites (i.e. tacit premises).

(c3) The exploration of structural aspects of the behaviour consistent with certain motivational utterances, e.g. those asserting a promise. Here one can prove that under some additional assumptions, the set of all strings of actions satisfying a promise is a context-free language in the sense of Chomsky. In some sense, this theorem reflects the ‘context-freeness’ of certain social norms.

Generally, the analysis of motivational consistency of verbal and non-verbal behaviour leads to a formal theory of behavioural planning, where the elaboration of a plan of actions is identified with the generation of a sentence (string of actions) in generative grammars.

(d) The analysis of ethical valuations of strings of actions leading to ethically diverse outcomes. A hypothesis here is that two principal strategies of such valuations, from which others derive, are : ‘puristic’ ones, where only the ethically worst outcome is taken into account, and ‘liberal’ ones, based on the concept of appropriate ‘averaging’. Whether the second strategy is applicable depends on whether the conditions for the existence of conjoint measurement in the particular

<!-- page 7 -->

context are satisfied ; whether it is actually applied depends, among other things, on the personality of the judging subject.

(e) The formal system of actions outlined above may be easily adapted to cover the case of joint actions of many persons, both co-operative and conflicting. Research in this direction leads, among other things, to the establishment of foundations for a formal theory of organization.

## 4. ALGEBRA OF GOALS AND ALGEBRA OF MEANS : ATTAINABILITY AND CONFLICTS OF MOTIVES

The first notions which one can express within the formal framework of system (1) are those of attainability. Thus, let

$$
R^{-1}(s, t) = \{u \in L : uR(s, t)\} \tag{2}
$$

be the set of all strings of actions in $L$ which bring about the time-result $(s, t)$. The time-result $(s, t)$ is therefore attainable, if $R^{-1}(s, t) \neq \varnothing$ ; otherwise it is not attainable.

One is usually interested in attaining some goal ; the latter may be expressed as a configuration of time-results. If $(s, t)$ and $(s', t')$ are two time-results, then their alternative $(s, t) \lor (s', t')$ and conjunction $(s, t) \& (s', t')$ are interpreted respectively as ‘occurrence of $s$ at time $t$ or (resp. and) occurrence of $s'$ at time $t'$’. Negation $\sim(s, t)$ is meant as ‘non-occurrence of $s$ at time $t$’. Clearly, the set of all strings of actions leading to $(s, t) \lor (s', t')$ is the union $R^{-1}(s, t) \cup R^{-1}(s', t')$, the set of strings of actions leading to $(s, t) \& (s', t')$ is the intersection $R^{-1}(s, t) \cap R^{-1}(s', t')$ and the set of strings leading to $\sim(s, t)$ is the complement $L \setminus R^{-1}(s, t)$. This allows the following algebraic approach to the problem of attainability of composite goals. Let $f(x_1, \dots, x_n)$ be a propositional function of $n$ variables, involving only the functors $\lor$, $\&$ and $\sim$, and let $C = \{(s_1, t_1), \dots, (s_n, t_n)\}$ be a set of time-results. Substituting in $f$ the time-results $(s_i, t_i)$ in place of arguments $x_i$ one obtains a composite goal $f(C)$, i.e. a configuration of time-results. On the other hand, substituting in $f$ the sets $R^{-1}(s_i, t_i)$ in place of arguments $x_i$, and replacing the functors $\sim$, $\lor$ and $\&$ by the operations of negation, unions and intersections one obtains the

<!-- page 8 -->

set, say $R^{-1}(f(C))$, of all strings of actions leading to the composite goal $f(C)$.

In particular, taking $f(x_1, \dots, x_n) = x_1 \lor \dots \lor x_n$ or $f(x_1, \dots, x_n) = x_1 \& \dots \& x_n$ one obtains as $f(C)$ the goals ‘at least one time-result in $C$’ and ‘all time-results in $C$’, while the corresponding acts $R^{-1}(f(C))$ become in these cases $\bigcup R^{-1}(s_i, t_i)$ and $\bigcap R^{-1}(s_i, t_i)$.

If $\bigcup R^{-1}(s_i, t_i) \neq \varnothing$, one may say that the set is weakly attainable (i.e. one can attain at least one of its time-results), while if $\bigcap R^{-1}(s_i, t_i) \neq \varnothing$, the set $C$ is strongly attainable, i.e., one can attain all its time-results.

A situation of particular interest for psychology occurs if all results in $C$ are in some sense desirable (i.e., a person is motivated to attain them), while $C$ is attainable weakly but not strongly. This enforces a choice, involving resignation from some of the desired time-results, and thus creates an internal conflict of motives.

Clearly, the information that $C$ is attainable weakly but not strongly does not characterize the conflict sufficiently, since there are numerous subsets of $C$ which may or may not be jointly attainable. Thus, a potential taxonomy of conflicts may be obtained by studying those subsets of $C$ which are strongly attainable, in particular, the maximal among such subsets. This idea provides an unexpectedly rich taxonomy of conflicts ; even in the case of four time-results (aims, motives) not attainable jointly there are as many as 113 types of conflicts, depending on which of the combinations of time-results are attainable and which are not.

In psychological applications, the most typical scheme is a conflict of four motives, which may be generally described as :

— occurrence of an event which one wants to occur ;

— non occurrence of an event which one wants to avoid ;

— performing of an action which one ought to perform ;

— not performing an action which one should not perform.

This allows the characterization of internal conflicts of the type ‘approach-approach’, ‘approach-avoidance’, and ‘avoidance-avoidance’, as well as conflicts within the id domain, or between the id and Superego domains, in dynamic psychology.

It is interesting to compare the 113 types of conflicts theoretically possible with the number of those for which it is possible to find real

<!-- page 9 -->

**151** · A FORMAL THEORY OF ACTIONS

life examples. The latter class is very limited ; it contains only a few conflicts, and the attempt to find examples of situations (in psychology) of a conflict of a given type leads to situations artificial and difficult to imagine. Thus, despite the richness of real situations, and the theoretical possibility of 113 categories, there actually seem to be only a very limited number of types of internal conflicts.

This limitation is probably related to the restrictions imposed by ‘grammars of situations’, and by learning, which lead to the tendency to reduce all situations to ‘binary’ conflicts.

Of course, this limitation concerns only psychological conflicts ; in other cases, e.g. planning or solving organizational problems (where the conflict lies in the lack of joint satisfiability of some four conditions), one can easily point out examples of all 113 types of conflicts.

If a given time-result, or a composite goal $f(C)$ is attainable, then there may usually be more than one way of achieving it, i.e. the set $R^{-1}(f(C))$ may consist of more than one element. In such cases, it is of some interest to impose appropriate criteria of optimality, or valuations on strings of actions, so as to be able to select those which are ‘best’ in some sense or other. Such a construction is of importance both for normative purposes, when the system is used to describe some action situation, and one is interested in the best ways of attaining a certain goal, and also as one studies actual behaviour in real situations, comparing it to optimal behaviour.

One of such criteria is provided by praxiology ; roughly, it tells to attain a given goal by performing only those actions which are essential (economy of effort), and by strings of actions with the shortest duration (economy of time). Accordingly, in the set $R^{-1}(f(C))$ of all strings of actions which bring about the goal $f(C)$, one may distinguish the subsets $\text{Prax}\,f(C)$ and $\text{Prax min}\,f(C)$. The first consists of those strings which are not ‘economically dominated’, and lead to $f(C)$, i.e.

$$
\text{Prax}\,f(C) = \{u \in R^{-1}(f(C));\ \text{there is no } u' \in R^{-1}(f(C))\ \text{with } u \prec u'\ \text{where } u \prec u'\ \text{if } u'\ \text{results from } u\ \text{by crossing out some of its actions and replacing them by } \#\}.
$$

Similarly, one may define

$$
\text{Prax min}\,f(C) = \{u \in \text{Prax}\,f(C)\ :\ \text{there is no } u' \in \text{Prax}\,f(C)\ \text{with } \varphi(u') < \varphi(u)\},
$$

<!-- page 10 -->

where $\varphi(u)$ is the duration of a string, defined as $\varphi(d_1 \ldots d_n) = \varphi(d_1) + \ldots + \varphi(d_n)$.

## 5. MOTIVATION AND CHOICE

In the analysis of the relations between verbal and non-verbal behaviour, the starting point is the analysis of those utterances which explain, justify, evaluate, etc. the decisions which one plans to take, or has already taken. If one abstracts here from those fragments of utterances which concern the specific aspects of the situations described, there remain sentence-schemes characterized by the use of certain functors. The semantic classification of these functors, which may be called motivational, leads to partitioning them into the following categories :

(a) epistemic functors, such as ‘I know that’, ‘I believe that’, etc.,

(b) emotional functors, such as ‘I am glad that’, etc.,

(c) proper motivational functors, such as ‘I want’, ‘I prefer’, etc.,

(d) deontic functors, such as ‘I ought to’, ‘I must’, etc.,

(e) intensional functors, such as ‘very’, ‘hardly’, etc.

Next, one may postulate that there exists a certain number of scales, for which the above functors form a linguistic representation. These scales, by definition, constitute the motivational space. It may be assumed that in decision situations, various options are evaluated on the scales of this space, and that the final decision depends on these evaluations through the appropriate choice function.

Various decisional models suggested in psychology, such as SEU model, or Atkinson’s model of achievement motivation [2] fall under this general scheme.

To describe the structure of a decision model, one can make the following hypotheses.

HYPOTHESIS 1. The scales of motivational space with the lowest degree of generality which cannot be decomposed into subscales correspond to the basic units of self-perception.

HYPOTHESIS 2. In various stimulus situations, the role of different scales of motivational space may be different, with some of the scales

<!-- page 11 -->

**153** · A FORMAL THEORY OF ACTIONS

dominating ; which scale dominates depends here both on the subject and on the situation.

The arguments for Hypothesis 2 are, firstly, the experiments of Tversky [14], which indicate that in their decisions people often take into account only one aspect of the alternative without trying (or without being able to try) to make the choice based on weighing up various aspects.

Secondly, one can show that Hypothesis 2 is, in some sense, immanent, using the impossibility theorem of Arrow. The argument here goes as follows.

In his original formulation [1], Arrow’s theorem concerns the social choice, i.e. situations where each of the members of a society (a group, such as Parliament, etc.) votes, or otherwise expresses his preferences among the set of options, say $A$, $B$, $C$, $\ldots$, like candidates, variants of a budget, etc. The problem is the existence of a social choice function, i.e. a function which would adequately, in a ‘democratic’ way, express the preference of society. ‘Democracy’ is explicated here in the form of a set of postulates, whose names derive from the above interpretation. It is clear, however, that the situation described is analogous to that in individual decision making : the evaluations on scales of motivational space correspond to preferences by members of the society, and the final decision corresponds to the social choice.

The social choice function (final preference) is required to satisfy the following conditions, in which $\succsim_x$ stands for the preference of the person $x$, and $\succsim_{\mathrm{soc}}$ stands for the social preference. Formally, this function assigns the relation $\succsim_{\mathrm{soc}}$ to the set of relations $\succsim_x$, $\succsim_y$, $\ldots$ (all these relations are assumed to be transitive and connected in the set of options $A$, $B$, $C$, $\ldots$). The symbols $\succ_{\mathrm{soc}}$, $\sim_{\mathrm{soc}}$, $\succ_x$, $\sim_x$ stand for the strict preference or indifference of the society and person $x$ respectively.

(1) *Lack of dictator.* No member of the society is to be a dictator, i.e. a person whose preference dominates over the preferences of the other members of the society (formally, $x$ is a dictator, with respect to options $A$ and $B$, if $A \succ_x B$ implies $A \succ_{\mathrm{soc}} B$, regardless of the preferences $\succsim_y$, $\succsim_z$, $\ldots$).

(2) *Sovereignity.* The society may decide that $A \succ_{\mathrm{soc}} B$, and it may

<!-- page 12 -->

decide that $B \succ_{\mathrm{soc}} A$, by an appropriate vote (i.e. it is not so that $A \succ_{\mathrm{soc}} B$ even if for all persons it is $B \succ_x A$).

(3) *Consistency between individual and social choice.* Suppose that for a certain set of preferences the social preference is $A \succ_{\mathrm{soc}} B$, and suppose that for some reason the voting is repeated. In the second vote, all persons who voted $A \succ_x B$ vote in the same way, while some of the persons who previously voted $B \succ_x A$ changed their mind, and vote $A \succ_x B$. Then $A \succ_{\mathrm{soc}} B$ also in the second vote.

Rules which do not satisfy this condition are hard to imagine : they would have to be such that when the number of votes of $A$ over $B$ increases, the social choice changes from $B$ to $A$.

(4) *Independence from irrelevant options.* Suppose that as a result of voting is $A \succ_{\mathrm{soc}} B$. Suppose that for some reason the vote is repeated, allowing for one more option $C$, and suppose that this option is the least desired for all members of the society (i.e. all those, who previously voted $A \succ_x B$ vote now $A \succ_x B \succ_x C$, while all those who previously voted $B \succ_x A$ now vote $B \succ_x A \succ_x C$). Then in the second vote it is $A \succ_{\mathrm{soc}} B$ again.

(5) *Freedom.* At least three persons take part in the voting, and there are at least three options, $A$, $B$, $C$, which everyone may order in any way such as $A \succ_x B \succ_x C$, $C \succ_x A \sim_x B$, etc.

Arrow’s theorem asserts that there is no decision function which satisfies all the above postulates, i.e. that these postulates are inconsistent.

The consequences, for the individual choice function based on evaluations on scales of the motivational space are the following. Since the individual choice function has the structure of social choice function, it must violate at least one of the above five postulates. It appears that the postulates which are most likely to be violated are (1) lack of dictator ; (2) sovereignity, and (3) independence from irrelevant options. The other postulates seem to be always satisfied, at least in the decisions of rational persons.

One can now try to characterize in psychological terms the persons whose choice functions do not satisfy postulates (1), (2) and (3) of Arrow’s theorem.

When postulate (1) (lack of dictator) is violated, the decision

<!-- page 13 -->

**155** · A FORMAL THEORY OF ACTIONS

function is dictatorial, in the sense that one psychological continuum dominates over all others, so that the final decision is governed by the evaluations on this continuum only.

There are two natural candidates for such a dominating continuum, namely the scales representing the id and the scales representing the Superego. Thus, one can expect that among persons who do not satisfy postulate $(1)$ there will be two subgroups : persons, whose dominating continuum belongs to the Superego family (represented by functors such as ‘I must’, ‘I ought to’ and so on), and persons with a dominating continuum of the id type represented by functors such as ‘I want’, ‘prefer’, etc. The first of these groups will consist of persons generally described as reliable, responsible, righteous, etc., while the second will comprise ‘hedonists’. In clinical cases, the first persons will be compulsive, the second — psychopathic.

In turn, there may exist persons for whom the decision function does not satisfy postulate $(2)$ of sovereignity. Thus, their decisions at least with respect to some options are imposed. This means that the choice coincides with a certain accepted standard, even in those cases when all orderings on psychological scales are against this choice. It seems that only extreme cases can be found in this category, i.e. persons with a pathologically weak personality, whose apparent strength is derived from blind obedience : SS-men may serve here as examples.

Finally, there may exist persons whose choice function does not satisfy the postulate $(4)$ of independence from irrelevant options. From the psychological point of view this group will comprise neurotics, who are prone to changing their desisions in cases when some options become blocked or added, even when those options are not preferred. In extreme cases one may cite here the ‘all or nothing’ attitude of some neurotics.

The above groups represent cases where the choice function does not satisfy the postulates $(1)$, $(2)$ or $(4)$, but provides transitive and connected preferences among the options. In other words, the essence of Arrow’s theorem, as applied to the case under discussion, is that the linear ordering of options is possible only at the cost of giving up one of the postulates $(1)$, $(2)$ or $(4)$. There remains a possible group

<!-- page 14 -->

of persons whose choice function does not yield a linear ordering of options : either this relation is not transitive, or it is not connected (in which case one obtains only a partial order).

One cannot say much about this group of persons, except that, as indicated by the experiments of Tversky [14], persons with intransitive preferences are perhaps more numerous than one might think.

One should point out that the ease with which the above conclusions were obtained is connected with the negative character of Arrow's theorem. Indeed, the only assumptions concerning choice situations stated that in case of joint individual evaluations, the resultant evaluation is somehow obtained from the evaluations on particular scales of motivational space. In other words, the evaluation is built out of some evaluations, each concerning one aspect of the choice options.

Therefore one can assert something about the character of the choice function without the necessity of empirical tests to verify the assertions made, nor even without the necessity of making precise the arguments which enter the choice function.

## 6. MOTIVATIONAL CALCULUS

The intuitive background for the construction of motivational calculus, which describes the schemes of inference from utterances in the natural language, is the fact that there exists a sufficiently common feeling of correctness of such inference.

The basic primitive concept on which the construction of inference schemes of motivational calculus is built is that of the inadmissibility of a sentence. Intuitively, an expression is inadmissible, if there is no context in which it may be meaningfully applied, or if it could be applied only in very unusual circumstances. This concept allows us to define the notion of semantic implication : $A \to_s B$ ($A$ implies semantically $B$) if the sentence ‘$A$ and not $B$’ is inadmissible.

The motivational calculus consists of a number of semantic implications concerning the sentences containing motivational functors (see the preceding paragraph). These implications allow us to make inferences from sentences in the natural language, e.g. the implication which allows us to infer from the sentence ‘I am glad that $p$’, that the speaker either knows that $p$, or thinks that $p$; (symbolically, $G_p \to_s Kp \lor Tp$). The whole set of semantic implications of moti-

<!-- page 15 -->

vational calculus will not be reproduced here. It is only worth mentioning that one can prove the logical consistency of this set by constructing a set-theoretical model in which the functors and their arguments are interpreted in terms of sets [9].

In order to achieve greater generality, the traditional way of listing the primitives and laying down the rules of construction of composite sentences was deliberately omitted in the construction of this motivational calculus. It should be clear, however, that giving such rules would restrict the considerations to a specific language, and would also require a specification of the sense of motivational functors (the latter task is still not completely solved for any single functor — though there are some results in this direction, e.g. Hintikka's [4] — let alone for the whole set of functors at once). It appeared more promising to provide directly a set of inference rules, and prove the consistency of this set.

One can argue that such an approach is closer to the natural language, since laying down the construction rules for composite sentences would allow long sentences, acceptable logically, but not linguistically.

The knowledge of the laws of motivational calculus makes it possible to formulate laws of motivational consistency, by combining decisions (actions) with utterances. Such laws allow us to determine the classes of conclusions, utterances, or actions which are consistent with a given utterance, hence also allow us to make some prediction about behaviour on the basis of a person's utterance.

Another possibility is to use the laws of motivational consistency and motivational calculus for direct inferences about motivation. Knowing the person's utterances and his decisions or actions, and assuming that he is motivationally consistent, the problem lies in adding tacit premises to his utterances in such a way that his decision becomes motivationally consistent with the combined utterances (tacit or not). In cases of this kind, the added premises reflect the (un-uttered) motive of a person. Clearly the less freedom there is in such an addition of premises, the more certain is the inference about the person's motives.

The rules outlined above may provide formal methods of inference in psychological diagnosis.

It is also worth while mentioning that the study of the language

<!-- page 16 -->

of motivation and motivational calculus, based on common and every-day sense and intuition, is a necessary theoretical prerequisite for the construction of a model of the language user.

## 7. MOTIVATIONAL CONSISTENCY AND STRUCTURAL PROPERTIES OF SETS OF STRINGS OF ACTIONS WHICH FULFILL OR BREAK A PROMISE

One of the basic elements of the description of a person's behaviour is the motivational consistency (or its lack), understood in the most common sense as the consistency between the person's utterances and actions. This element of description provides an important clue to the personality of the person evaluated.

Motivational consistency, a foundation of prosocial training, can manifest itself in various ways, such as truthfulness, keeping promises, etc., or as the ability to give reliable and convincing explanation of one's behaviour.

There is no need to stress the importance of this concept for interpersonal relations, in science as well as outside it.

Clearly, to determine whether a given behaviour is motivationally consistent with a given utterance requires a separate analysis in each case. There arises an interesting problem, namely to what extent one may characterize the structural aspects of the behaviour which is consistent (or inconsistent) with a given utterance ? In other words, the problem is to answer the question whether the class of all behaviour consistent (or inconsistent) with a given utterance can be characterized through its structural properties.

Some results on this subject are given in this section ; the presentation requires the usage of certain notions from mathematical linguistics, such as generative grammar, regular and context free language, etc. these notions can be found, for instance, in Chomsky [3]).

The basic ideas can be presented as follows : Suppose that we consider the actions of a certain fixed person, and that this person, prior to the beginning of the string of actions, uttered a certain sentence which contained a promise. At first, it will be assumed that

<!-- page 17 -->

this promise is of a positive character, concerning a specific moment of time, e.g. ‘I shall phone him tonight before 7 o’clock’. Now, each string of actions of this person may be classified to one of two categories : satisfying the promise and breaking the promise. The object of investigations will be the first of these sets, that is, the class of all strings of actions which satisfy a given promise.

Let us denote this set by $T$, and assume that $T$ satisfies the following condition :

(a) if $xy \in L$, then $x \in T$ implies that $xy \in T$.

This condition expresses the following requirement : if a certain string of actions $x$ satisfies the promise (is in $T$), then any continuation of this string $xy$ (as long as it is possible, i.e. belongs to $L$), also has the same property, i.e. belongs to $T$. Thus, condition (a) states that a promise can be fulfilled, and once this is done, no subsequent actions can change this fact. This, of course, is an idealization, and one can easily point out examples of promises which do not have this property (e.g. ‘I shall send him flowers for every birthday’). In the considerations below, condition (a) will be assumed, however, as a fair approximation to reality.

Before formulating the theorem it is necessary to introduce certain auxiliary definitions.

Namely we shall say that the sequence $x \in T$ only satisfies the promise if the conditions $x = x_1 x_2$ with $\varphi(x_2) > 0$ imply that $x_1 \notin T$.

Let $\hat{T}$ stand for the set of all strings which have the above property. In some sense, the set $\hat{T}$ consists of all those strings which fulfill the promise at their termination but not before.

Let $h(T) = \max \{ \varphi(x) : x \in \hat{T} \}$. The number $h(T)$ will be called the motivational horizon of the promise.

The characterization of the sets satisfying the promise can now be formulated as follows :

**THEOREM.** Suppose that $L$ is a context free language, and that $T \subseteq L$ satisfies the condition (a). If $h(T) < \infty$, then $T$ is also a context free language.

The complete proof may be found in [5], and will be omitted here.

<!-- page 18 -->

Let us now turn to promises of a negative character, which do not refer to any specific moment of time (e.g. promises which start from ‘I shall never ...’). This time it will be more convenient to distinguish the set of all strings of actions which break the promise, to be denoted by $U$.

Let us assume that

(b) if $xyz \in L$, then the condition $y \in U$ implies $xyz \in U$.

The condition (b) differs from (a) by allowing concatenations also from the left. This corresponds to the ‘timelessness’ of the considered negative promises: they can be broken, but not fulfilled, hence if a string of actions breaks a promise, the same holds for any string which contains the former as a part.

Let $z$ be an element of $U$, i.e. a string which breaks a promise. If $z = uvw$ for some $u$, $v$, $w$ with $v \in U$ and $u \notin U$, then $v$ is called the first offense in $z$. Let $\hat{U}$ be the set of all first offenses in the strings of $U$, and let $k(U) = \max \{ \varphi(x) : x \in \hat{U} \}$.

One can then prove a theorem analogous to that which characterizes the sets of strings which fulfill a promise :

**THEOREM.** If $L$ is a context free language, and $U$ satisfies the condition (b) with $k(U) < \infty$, then $U$ is also a context free language.

In a somewhat loose interpretation, perhaps closer to a metaphor than to bounds imposed by technicalities of definitions, one may say that the properties described by the above two theorems constitute a formal representation of the observable fact that social norms (especially ethical ones) are, as a rule, formulated without specific reference to specific situations which might serve as contexts of their applicability. Thus, taking religion as an example, a sin is defined as a specific act, and its presence in a string of actions determines the qualification of this string (with few exceptions) regardless of the preceding and subsequent actions, i.e. regardless of the context in which the sin occurs.

The law may perhaps be thought of as somewhat more flexible, in the sense that occasionally provides classes of contexts in which a given action constitutes an offense, and classes of contexts in which

<!-- page 19 -->

it is not so. This amounts to specifying strings of actions together with surrounding circumstances as offenses, rather than isolated actions. Again, however, the presence of a string constituting an offense qualifies the string of actions in which the offense is embedded. The preceding or subsequent actions may serve as a factor determining the punishment, but as a rule, not for a qualification of an offense as such. The most serious offenses, such as murder, rape, arson, theft, etc. are qualified regardless of the context in which they occur. In this sense one can say, that the above theorems reflect certain general regularities in the treatment of social norms, namely the relative universality of contexts to which they apply. These results may, therefore, be of some interest for deontic logic.

## 8. PLANS AND GENERATIVE GRAMMARS

The system of actions presented here may serve as a foundation of a formal theory of planning behaviour.

The basic idea consists of applying the concept of generative grammar.

Suppose that we are interested in achieving a certain composite goal $f(C)$, i.e. a configuration of time-results. In such cases, it is necessary to perform one of the strings of actions in the set $R^{-1}(f(C))$. This set, in turn, may be treated as a certain language, and one can try to study the grammar generating this language.

Now, for a description of a grammar of a given language (see, for instance, Chomsky [3]) one has to specify its meta-alphabet, and a set of production rules, in such a way that the class of all strings in the terminal alphabet (in this case : the alphabet of actions) which can be generated by the production rules coincides with the class of all strings of the given language.

In the case of the language $R^{-1}(f(C))$, the terminal alphabet coincides with the alphabet of actions $D$. The process of generating strings in $R^{-1}f(C)$ is identical with the process of successive stages of elaboration of the plan how to achieve $f(C)$. The role of meta-alphabet is played by the descriptions of actions or classes of actions. The production rules depend, of course, on the specific situation one wants to describe.

<!-- page 20 -->

Formally, to each element of the set $D^*$ of all strings of actions one can assign its description, to be referred to as ‘label’ of the string of actions. Then the plan may be identified with the subset of the set of labels, corresponding to the strings from $R^{-1}(f(C))$ : the smaller this subset is, the more elaborate is the plan. In particular, in case of a one-element subset, the plan describes the actions in complete detail, i.e. it specifies in which order actions are to be performed.

The production rules, i.e. the replacement of some labels by other labels with more detailed descriptions of actions can be obtained if one uses the concept of motivational consistency : the label $a$, may be replaced by a composite label $b_1, \ldots, b_n$, if in each context, two strings which differ only to the extent that one contains $a$ and the other contains $b_1 \ldots b_n$ are both equally consistent or equally inconsistent motivationally.

## 9. GENERALIZATION: APPLICATION TO ORGANIZATION THEORY

The system (1) may be easily generalized so as to cover the case of simultaneous actions of several persons. Such an extension has the form

$$
\langle D, \#, \varphi, K, \alpha, S, R \rangle
$$

where $D$, $\#$, and $\varphi$ are the alphabet of actions, ‘pause’ and duration function, as before. Here $K$ stands for a set of persons, consisting of, say $k$ elements. Next, $\alpha$ is the set of $k$-tuples of strings of actions $(u_1, \ldots, u_k)$, such that $\varphi(u_1) = \cdots = \varphi(u_k)$; the intended interpretation here is that a $k$-tuple $(u_1, \ldots, u_k)$ is in $\alpha$ if it is possible to perform strings of it simultaneously, $u_1$ by the first person, $u_2$ by the second person, and so on. The word ‘possible’ may again be interpreted in several ways, as in the interpretation of symbol $L$ in the system for a single person (as physical admissibility, psychological admissibility, etc.). The remaining two primitive concepts, $S$ and $R$, are as before sets of results, and relation or ‘causation’, except that, of course, $R$ connects now the time-results $(s, t)$ with the $k$-tuples in $\alpha$ : the symbol $(u_1, \ldots, u_k) R(s, t)$ is to be interpreted that the simultaneous per-

<!-- page 21 -->

formance of the strings $(u_1, \ldots, u_k)$ by persons in $K$ leads to the occurrence of the time-result $(s, t)$.

Now, this system may be applied to a formal description of an organization, understood as an institutionalized set of persons whose aim is to achieve certain specific tasks.

Thus, the description of an institution consists of specifying :

1. System $\langle D, \#, \varphi, K, \alpha, S, R \rangle$,

2. set of relations $P_1, P_2, \ldots$ describing the internal structure of the set $K$.

To give some examples, $P_1, P_2, \ldots$ may be relations such as dominance in hierarchy (i.e. the relation specifying who can give orders, instructions, etc. to whom), the relations describing the organizational structure, i.e. specifying which decisions may be taken by which subsets of members of $K$, the relation of reporting and so on.

The most promising aspect of the operation of an organization which can be described in these terms is how one organization governs the actions of another. Thus, imagine that we are considering two institutions, one superior with respect to the other, say $A$ (superior) and $B$ (subordinate). ‘Governing’ takes the form of influencing $B$ by $A$, i.e. ‘causing’ $B$ to attain some specific goals. Clearly, the concept of an institution need not be treated literally here; $A$ and $B$ may be parts of the same institution, e.g. two departments, etc.

The elements of the description relevant in this case will be the sets $\alpha_1, S_1, R_1$ and $\alpha_2, S_2, R_2$ for the organizations $A$ and $B$ respectively.

The governing of $B$ by $A$ occurs through instructions, which modify the operation of $B$ in some way. Naturally, the internal structure of both $A$ and $B$ may also be based on some instructions, but for the present purpose this aspect may be neglected.

Formally, therefore, we may reduce the considerations to the system $\langle \alpha_1, S_1, R_1, \alpha_2, S_2, R_2, I, V, \varphi \rangle$, where the first six concepts are already specified, and :

(1) $I \subset S_1$ is a set, whose elements will be interpreted as instructions issued by $A$ directing $B$. The inclusion $I \subset S_1$ means that these instructions are treated as results of the operation of organization $A$.

(2) $V$ is a subset of the set of all finite strings formed out of instructions from $I$ and pause $\#$. The sequence of the form $i_1 \# \# \# \# i_2 \# \# \# i_3 \# \ldots$ is to be interpreted as issuing the

<!-- page 22 -->

instruction $i_1$, then — after an appropriate pause — issuing the instruction $i_2$ and so on. The set $V$ contains only the meaningful strings of instructions, where meaningfullness is to be understood as follows : each instruction requires that some time-results are to be made to occur by the subjected institution $B$, and for a meaningful string of instructions, these time-results must be jointly capable of occurring.

Finally, $\varphi$ is a function which to each string in $V$ assigns a subset of $\alpha_2$. This subset, to be denoted by $\alpha_2(v)$ for the string $v$, is to be interpreted as the set of actions of the institution $B$ which are consistent with the instructions $v$.

Intuitively, each string of instructions imposes some restrictions on the set of actions which may be performed by the institution $B$. These restrictions may be of a varied nature, the most important of them being :

(a) the instruction may specify the goal $f(C)$ to be attained, by the whole institution, or by a subset of its employees, etc. In this case, one may say that the subset assigned by function is simply $R_2^{-1}(f(C))$, i.e. a set of all strings of actions which lead to the goal $f(C)$,

(b) the instruction may impose some restrictions on the organizational structure of $B$, i.e. it may eliminate some sets of simultaneous strings of actions as not ‘admissible’, that is, inconsistent with new constraints. Such constraints need not be treated as organizational only ; they may result from remowing some instruments from institution $B$ and so on.

The basic definitions, allowing the classification of instructions are now the following : let $u$, $v$ be two strings of instructions, and $\alpha_2(u)$ and $\alpha_2(v)$ be the corresponding sets of simultaneous strings of actions of institution $B$. Then $u$ and $v$ may be said to be equivalent, if $\alpha_2(u) = \alpha_2(v)$; next, $u$ is an unnecessary repetition of $v$, if $\alpha_2(v) = \alpha_2(vu)$; $u$ imposes additional restrictions with respect to $v$, if $\alpha_2(v) \supset \alpha_2(vu)$, and it releases the restrictions, if the inclusion is opposite. Finally, if $\alpha_2(u)$ is neither contained, nor contains $\alpha_2(vu)$, then $u$ is independent of $v$.

If $\alpha_2(u_1) \supset \alpha_2(u_1, u_2)$, then one can call instructions $u_1$, $u_2$ monotone : the next one restricts further the set of available strings of actions of institution $B$.

Within the framework of these concepts one can pose various

<!-- page 23 -->

questions on organizational theory, and attempt to solve them : under some appropriate optimality criteria, which types of instructions are most effective or efficient ? What proportion of tactical instructions is optimal for attaining a certain goal? A tactical instruction may be defined as one which restricts the range of goals, without restricting the set of ways of achieving these goals. What is the proper proportion of tactical instructions for an organization of a given complexity of structure ?

Assuming that one is dealing with more than two institutions, another class of questions concerns such concepts as their hierarchization, equivalence with respect to some goals, or with respect to their structure, etc. One can also consider operations affecting institutions, such as their combining or splitting.

Another possible interpretation of the considerations of this paragraph may be the following. The set $V$ of admissible string of instructions forms a certain ‘language’ (being a set of strings of some elements) ; the ‘alphabet’ here consists of instructions. The ‘words’ of this language are assigned sets of the form $\alpha_2(v)$, which may be interpreted as ‘meanings’ of these words. However, these meanings may again be interpreted as in some sense ‘languages’, except that their strings are running parallel. In this sense, the instructions define certain abstract languages, hence they themselves are elements of a meta-language with respect to the languages $\alpha_2(v)$. In some simplification one may therefore say that the language of instructions constitutes a meta-language for the languages of actions consistent with these instructions. Alternatively, the languages $\alpha_2(v)$ may be thought of as constituting the semantics of the language of instructions.

## 10. OTHER INTERPRETATIONS OF $\alpha$

It is worth stressing that the set $\alpha$ may be treated also as a ‘multi-dimensional’ language, which describes the interrelations between some types of events, not necessarily actions performed by humans. Thus, for example, one can think of a film as a parallel string of pictures, a string of music or dialogues, and a string of other sound effects. Such a ‘language’ of admissible triplets of strings in a film has its own rules of syntax, which may be called the ‘grammar’ of film. The same

<!-- page 24 -->

interpretation of course also applies to book illustrations, operating instructions for some equipment which combine verbal and non-verbal elements and so on. In each case one can think of a specific ‘grammar’, and investigate its properties and rules, in order to achieve some type of optimality.

## 11. APPLICATIONS TO COMMUNICATION THEORY

The theory of actions can be used for the construction of a formal theory of dialogues. The successive utterances, as well as the periods of silence (listening to the other speaker) may be treated as strings of actions, and a dialogue is interpreted as simultaneous strings of such actions, one performed by one person, and the second by another. The main problem consists of formulating conditions for such a pair of parallel strings to constitute a dialogue. The paper [10] suggests several necessary conditions, some of them of a syntactic, and some of a semantic character. In the latter case, the conditions are expressed in terms of fuzzy sets (see [15]), and assert, roughly speaking, that the subsequent utterance ought to belong in a degree exceeding a certain minimum, to an appropriate fuzzy set defined by the preceding utterances.

This idea is especially fruitful when applied to the theory of eristic dialogues, which may then be represented as positional games, in which each of the utterances or “moves” causes a change in the ‘position’ of the opponent in the semantic space. For details of the construction, see [10].

## 12. APPLICATIONS TO PSYCHOLOGY

The ideas presented below concern developmental psychology. Generally, in this domain one can distinguish three groups of problems concerning :

(1) the system of theoretical concepts describing the process of development (different stadia) ;

(2) the system of concepts explaining the psychological development of a person ;

<!-- page 25 -->

(3) the system of concepts describing influences on the process of development (rearing, education).

As regards (1), using the linguistic intuitions underlying the system of action theory, one can describe development as

(a) learning wider classes of words of the language of actions, i.e. learning the ‘languages’ of wider classes of objects ;

(b) learning more and more complex grammars of these languages, i.e. longer and more complicated strings of actions ;

(c) learning to create new grammatical rules (development of abilities and creativity).

Quite independently of the above methods of description of development, its taxonomization, etc., one can proceed in a different way, namely by constructing an abstract ‘stadial language’, starting from those stadia of development which have so far been distinguished by various researchers.

According to Przetacznikowa [13] there exist jointly $18$ systems of stadia, containing altogether $61$ stadia. Thus, development may be described as simultaneously running $18$ strings of successive stadia. The scheme of this representation, for simplicity reduced to three systems (instead of $18$) may be visualized as follows :

$$
\begin{aligned}
&\qquad\qquad\big\vert\qquad\qquad\qquad\quad\big\vert \\[-0.25em]
\text{System 1} &\colon\; A \;\Big\vert\; B \;\Big\vert\; C \;\Big\vert\; D \\[0.4em]
&\qquad\qquad\big\vert\qquad\qquad\qquad\quad\big\vert \\[-0.25em]
\text{System 2} &\colon\; K \;\Big\vert\; L \;\Big\vert\; M \\[0.4em]
&\qquad\qquad\big\vert\qquad\qquad\qquad\quad\big\vert \\[-0.25em]
\text{System 3} &\colon\; P \;\Big\vert\; Q \;\Big\vert\; R \;\Big\vert\; S \;\Big\vert\; T
\end{aligned}
$$

Thus, at each moment of time, the development is described as a string of symbols of stadia, such as $AKQ$ and $CLR$ and the two moments marked in the above picture. Here the whole ‘alphabet’ consists of $61$ symbols (‘letters’), and each ‘word’ has $18$ words, since there are $18$ stadial systems distinguished.

The sequence of observations of a child at different moments can now be represented as strings of ‘words’, or ‘sentences’ in an abstract ‘stadial language’.

Since the individual systems of stadia are not independent logically or statistically, certain words cannot appear at all, while some words may appear more often than other words.

<!-- page 26 -->

The same concerns the ‘sentences’ of stadial language. Consequently, one may speak of a ‘grammar’ of words and a ‘grammar’ of sentences.

The first is related to the fact that certain words are not possible, while some other combinations of letters correspond only to pathological situations.

The ‘grammar’ of sentences is related to the fact that certain stadia are interrelated, have a certain average duration, and finally, that within one string they generally follow a certain order.

The study of the structural properties of ‘words’ and ‘sentences’ of the so-defined stadial language can help in explication of the logical relations between stadia distinguished by various authors, while the study of the statistical properties of this language provides a statistical characterization of normal harmonious development.

There are certain difficulties connected with the fact that particular stadia are not too sharply defined ; moreover, the determination of the stadium of a child may not be exact, for lack of tools of measurement, errors in assessment, etc.

To solve this difficulty, one can apply the theory of fuzzy sets (see [15]). This application would consist of assuming that the ‘words’ as defined above form the so-called ideal types, and that at each moment the set of children which belong to this ideal type is a fuzzy set. In other words, each child would belong to various types in various degrees (perhaps in the zero degree, or in the full degree).

The fuzzy set, such as $CLR$, etc., would in this case be the product of three fuzzy sets, each corresponding to a stadium on one of the strings. In other words (see [15]), the degree of belonging to the fuzzy set $CLR$ would equal to the minimum of the degrees to which a given child belongs to sets $C$, $L$ and $R$ on particular strings.

As regards the ways of determining the degree of belonging to a given fuzzy set of developmental strings, one could use conventional methods, e.g. test scores, determining this degree as a function of the test score.

One should mention that the stadial language, as outlined here, is not restricted to developmental psychology ; it can be used for the description of any changes and evolutions, provided one can distinguish

<!-- page 27 -->

stadia. Thus, it may serve as a model of development of organizations, scientific teams, scientific disciplines, etc.

## 13. INTERPRETATION OF ACTION THEORY IN TERMS OF AUTOMATA

A question arises whether or not it is possible to interpret the basic notions of the formal theory of actions in terms of a theory of automata, and if so, whether such an interpretation yield any cognitive profit. The answer is positive to both questions ; below, we give a sketch of such an interpretation. The primitive notion here is an automaton, understood as a system

$$
\langle U, B, \Theta, D, \#, \tau, \pi \rangle
$$

with the following interpretation of the concepts.

The set $U$ is the set of internal states of the automaton ; in concrete cases these are simply the states of the considered fragment of reality. In general, the elements of $U$ are vectors, whose coordinates describe what is happening to the particular object under study.

It is assumed that any element $u$ in $U$ contains all information of interest in the particular case, i.e. that the description of the state is complete for the purpose of analysis.

Next, $B$ is the set of ‘stimuli’, which acts on the ‘operator’ of the automaton. These stimuli are, in general, all information which may influence his decision is some way. In particular, the stimuli may be information about the state of the world, partial or complete (so that in special cases elements of $B$ may be elements of $U$, or subsets of $U$).

The element $\Theta$ is a distinguished element of $B$, interpreted as ‘null stimulus’, i.e. lack of stimulus.

As in action theory, $D$ is the set of possible actions of the operator. For simplicity, let us assume that each action takes one unit of time ; one can always extend the system by adding the function expressing the duration of actions, if such a need arises. The action $\#$ is interpreted as before, as any action which does not belong to the domain of interest (so that $\#$ may be treated as ‘pause’).

The last two concepts describe the capacity for actions of the operator, and their outcome. Formally, $\tau$ is a relation in the set

<!-- page 28 -->

$U \times B \times D$, with the property that for any $u$ and $b$ there exists $d$ such that $(u, b, d)$ is in $\tau$. This means that for any pair consisting of the state of the world and a stimulus, there exists at least one admissible action (i.e. action admissible in the context $u, b$). As before, admissibility of an action may be interpreted in a number of ways, as physical, psychological, sociological, organizational, etc. admissibility.

Instead of relation $\tau$, it will be more convenient to consider a function $\tau$, which maps the set $U \times B$ into the set $2^D \setminus \{\emptyset\}$, i.e. which assigns to every pair $(u, b)$ a non-empty subset of $D$. This set will be denoted by $\tau(u, b)$.

Finally, the last primitive notion, $\pi$, is a function which describes the transitions ; thus, $\pi : U \times B \times D \to U$, and $\pi$ is defined only for those triplets $(u, b, d)$, for which $d \in \tau(u, b)$. The interpretation of this function is such that if at a time when the state of the automaton is $u$, and stimulus is $b$, one performs the action $d$, then the automaton will pass to the state $\pi(u, b, d)$.

In this terminology one can now define the concepts of the formal theory of actions discussed above.

In general the automaton describes the following situation : The operator observes the state of the automaton (partially or completely) and possibly observes also some other events (stimuli). Next, he selects an action, from the set of admissible actions in a given situation, and performs it, causing the transition of the automaton to another state. Then the situation is repeated.

The aim of the operator may be identified with a subset of $U \times N$, where $N$, as before, is a set of time moments. Thus, the aim is to manipulate the automaton, by choosing successive actions, in such a way as to reach an internal state $u$ at time $n$, where $(u, n)$ belongs to the subset of $U \times N$ which describes the goal.

One can now define the language of actions (which was a primitive concept in the theory of actions). It simply consists of all strings of actions which are admissible : more precisely, $d_1 d_2 \ldots d_n$ belongs to the language of actions, if the following conditions are satisfied :

(1) there exists $u_0 \in U$ and $b_0 \in B$ such that

$$d_1 \in \tau(u_0, b_0),$$

(2) for $j = 1, 2, \ldots, n-1$ there exist $b_j$ such that

<!-- page 29 -->

$$d_{j+1} \in \tau(u_j, b_j),$$

where $u_j = \pi(u_{j-1}, b_{j-1}, d_j)$.

Finally, the relation $R$, which is a primitive notion of the formal theory of actions, may also be defined in terms of the concepts concerning the automaton. Namely, in terms of the preceding definition (i.e. if $d_1 d_2 \ldots d_n$ is a string of actions which is admissible for the operator), any $(u_j, j)$ is in relation $R$ with the string of actions $d_1 d_2 \ldots d_n$.

As may be seen, the present system allows us to define all primitive notions from the formal theory of actions in terms of this system. In these definitions the primitives $\Theta$ and ‘pause’ $\#$ were not used ; they would be needed for definitions of other notions.

Such an interpretation seems of some interest by itself, and moreover, it allows a better access to nondeterministic situations (which appear to be difficult to capture in terms of a formal theory of actions). On the other hand, it seems that the sketched interpretation in terms of automata theory leads to a loss of linguistic intuitions ; also, there appear some difficulties in treating jointly verbal and non-verbal actions.

It may also be argued that the linguistic intuitions underlying the formal theory of actions are of special importance for the social sciences. These intuitions, as already explained, are based on the idea of extended language, in which the behaviour also has a linguistic character, i.e. operates with units of actions, units of situation, admissible strings of actions, etc. In other words, this system is based on the assumption of the existence of a syntax and semantic of behaviour. It also postulates that learning natural languages, and learning behaviour have certain analogies in the systems of laws which describe them.

It is worth stressing that a system of actions allows a great flexibility of interpretation, depending on the type and level of generality of the units of behaviour or situation, and the type of admissibility of strings of actions.

It is also necessary to stress, that the behaviour of a single person is described not by one language of actions, but by sets and hierarchies of languages of actions, for various classes of situations, or by multi-dimensional languages of actions, with the whole system of admissibility eliminating from the class of strings those which do not satisfy various (ordered or not) criteria of admissibility.

<!-- page 30 -->

## 14. MODELING OF PSYCHOLOGICAL DEVELOPMENT IN THE PROCESS OF EDUCATION

In this case, explanation will refer to the following stochastic automaton

$$
\langle U, D_x, D_y, p, q \rangle,
$$

where $x$ and $y$ stand respectively for the subject (pupil) and teacher ($y$).

The meaning of symbols, and the description of the operation of this automaton are as follows.

As before $U$ is the set of states, in this case the levels of knowledge of the pupil $x$, or alternatively, the levels of his psychological development. Next, $D_y$ is the set of actions available to the teacher $y$, in the form of stimuli, reward, punishments, exercises, etc. while $D_x$ is the class of possible reactions of pupil $x$ to these actions.

The basic idea here is that person $y$ observes the reactions of person $x$ to the preceding stimuli, and choses appropriately subsequent actions, causing the transition to another state.

Accordingly, the two remaining concepts, namely $p$ and $q$, describe the probabilities of a reaction to the stimulus, and the transition probability.

Formally, $p$ is—for any state $u \in U$ and stimulus $d_y \in D_y$, a probability distribution on the set $D_x$ of reactions ; the value $p(u, d_y, d_x)$ is the probability that reaction $d_x$ will occur if the state is $u$, and the applied action is $d_y$.

Similarly, for any state $u \in U$ and stimulus $d_y \in D_y$, $q$ is a probability distribution on the set $U$ of states; $q(u, d_y; u')$ is the probability of transition to state $u'$ if the present state is $u$ and the applied action is $d_y$.

The aim of education is to cause the person $x$ to reach a certain state, say $u^*$, describing the end of the process of development, attaining some level of proficiency, etc.

The teaching is sequential: in any step, the teacher $y$, knowing the preceding reactions of $x$, hence having some indirect information about his state $u$, chooses the stimulus $d_y$, which causes the next reaction and possibly transition to another state.

The problem consists of the choice of an optimal method of teach-

<!-- page 31 -->

**173** · A FORMAL THEORY OF ACTIONS

ing, i.e. such a strategy of choice of stimuli, which gives the highest probability of reaching the desired state $u^*$.

Of particular interest here is the special case of eristic dialogue, i.e. convincing and change of opinion ; the stimuli and reactions are of the same type, namely they are utterances in the dialogue. The difference consists in the fact that in the dialogue we have a symmetry of participants, while in the present model the roles of $x$ and $y$ are not symmetric.

When generalizing this model to the case of teaching not a single person but a group of persons (e.g. a class), one can include here — by appropriate interpretation — the teaching of certain prosocial behaviours, or the elimination of antisocial ones. Such a model would, however, require enriching with respect not only to the number of persons, but also — which is an essential change — the introduction of the concept of reward or punishment for certain behaviours, and the modification of transition probabilities, depending on the preceding rewards and punishments.

Such models, as more general than the classical learning model of Estes, would be very difficult to submit to theoretical analysis.

Returning to the terminology of action theory, the psychological development of a person was defined, in a sense, in two dimensions : syntactic and semantic. The syntactic aspect consists of learning more and more complex languages of actions, in particular of many persons, and learning ‘higher order grammars’, understood as rules for forming new languages of actions. For the description of the level of social development, it is essential in particular to be able to specify the knowledge of the grammatical rules of the languages of many persons, hence the languages of organizations, social groups, etc.

An important aspect of development in its syntactic aspect is the acquisition of ‘praxiological’ properties of actions, such as efficiency, economicity or reliability.

The semantic aspect of development is described by the content and complexity of aims, as well as plans, which consist of designing sequences of actions in order to bring about some goal.

The semantic of actions, understood in this sense (aims, plans and roles) determines the degree of complexity of languages of actions.

Socialization, in its semantic aspect, is understood as the high

<!-- page 32 -->

valuation of a certain class of aims (plans, roles) generated by various normative structures. It appears that the two basic mechanisms of socialization are learning motivational consistency, and learning co-operation, or social transactions, i.e. the exchange of a certain type of psychological or material goods.

## 15. GRAMMAR OF PSYCHOLOGICAL TRAITS

Finally, it is worth while mentioning one more way of describing behaviour (strings of actions), namely in terms of traits. Traits determine behaviour, both in the sense of choice of goals, and in the sense of means of achieving them. Using the linguistic interpretation of actions, traits may therefore concern both the semantic and syntactic aspects of behaviour.

The existence of various relations between actions in different stimulus situations implies the existence of a certain specific ‘logic’, or ‘grammar’ of psychological traits.

When one looks at various structural aspects of the co-appearence of traits, one can distinguish at least two types of relations between them. Firstly, some relations may be of purely tautological character, since some traits are defined as conjunctions of other traits. Thus, if trait $X$ is defined as the conjunction of traits $a, b, c, \ldots$, then every person who has trait $X$ also has trait $a$.

Secondly, some traits may be logically independent, but there may exist a statistical relation between them. Using an example from outside psychology, sex and colour-blindness are logically independent, in the sense that all four combinations are possible, but they are statistically very strongly dependent.

The above two approaches concerned a fixed time. It is interesting also to consider traits in their dynamic aspect, i.e. analyse which traits are a necessary prerequisite for the later development of other traits, and which actions should be undertaken to maximize the probability of forming a given trait or traits (or else, minimize the probability of forming some other, undesirable traits). A complete description would, naturally, require the knowledge of such probabilities, in which case one could apply the theory of directing development from the preceding section.

<!-- page 33 -->

In considerable simplification, the ‘grammar of traits’ may be identified with the rules of transition along the edges of a certain graph. At each node of the graph, there exists, as a rule, a certain number of possibilities of transition. Which of these will actually occur, is determined by a combination of various factors, of which the most important are genetic traits, and educational actions undertaken by parents, teachers, etc., which determine the probabilities of future transitions.

The terminal nodes of the graph correspond to sets of traits characterizing mature human being. Thus, the educational process may be interpreted (see Przetacznikowa [13]) as a choice of strategy for influencing the child so as to maximize the probability of reaching a node which corresponds to a socially desirable set of traits.

With the ‘linguistic’ interpretation of such a process, the paths in the graph represent linguistic expressions, and their terminal nodes — the meanings of these expressions.

## 16. SOME FURTHER PERSPECTIVES

At the end it is worthwhile to sketch briefly an adaptation of the action theory outlined in this paper to the case of fuzzy sets. The basic idea consists of replacing the relation $R$ which connects strings of actions with time-results, by a fuzzy relation. One can also treat $L$ as a fuzzy subset of $D^*$ ; thus, each string of actions would be admissible in a certain degree not necessarily $1$ or $0$. Whether $L$ is treated as a fuzzy set or not, the most important extension is obtained by treating $R$ as a fuzzy relation, i.e. as a fuzzy set in $L \times S \times N$. Thus, relation $R$ is described by membership function $f_R(u, s, n)$, which expresses the degree to which performing string of actions $u$ brings the time-result $(s, n)$. In particular cases, this degree may simply be equal to the probability of occurrence of $(s, n)$ if $u$ is performed. The role of sets $R^{-1}(s, n)$ of strings which lead to $(s, n)$ will be played now by sets $R_{\alpha}^{-1}(s, n)$ of those strings for which $f_R(u, s, n) \geqslant \alpha$, i.e. strings which bring about the time-result $(s, n)$ in the degree at least $\alpha$.

Since each of the sets $R_{\alpha}^{-1}(s, n)$ is nonfuzzy, one can apply the whole conceptual structure as explained in the preceding sections. Thus, $R_{\alpha}^{-1}(s, n) \cap R_{\alpha}^{-1}(s', n')$ is the set of all those strings of actions which

<!-- page 34 -->

bring both results $(s, n)$ and $(s', n')$ in the degree at least $a$. In a similar way one may interpret the unions, and generally build sets of strings, which bring about a given composite goal $f(C)$ in the degree at least $a$. The formalism is here analogous to that outlined already for the non-fuzzy case, with the exception of the following interesting possibility. For a composite goal $f(C)$, which is a certain configuration of time-results, some of them are more and some are less important. Thus, in the construction of $R_a^{-1}(f(C))$, i.e. set of strings of actions which bring about the goal $f(C)$ in the degree at least $a$, in the components of the form $R_{a_1}^{-1}(s, n)$, $R_{a_2}^{-1}(s', n')$, $\ldots$ not all numbers $a_1, a_2, \ldots$ need to be equal. For some more essential time-results one can take higher $a_i$, and lower for others.

Similarly, for praxiological sets, instead of ‘most economical’ strings of actions, one will get the whole family of sets for various levels $a$.

It appears that the further development of action theory in this direction, taking into account fuzzy or probabilistic relations, is most promising.

In fact, such an approach was developed, and may be found in [12].

## BIBLIOGRAPHY

[1] Arrow, K. J.: *Social Choice and Individual Values*, Wiley, New York, 1963.

[2] Atkinson, J. W.: *An Introduction to Motivation*, Van Nostrand, Princeton, 1963.

[3] Chomsky, N.: *Syntactic Structures*, Mouton, The Hague, 1957.

[4] Hintikka, J.: *Knowledge and Belief*, Cornell University Press, Ithaca, 1962.

[5] Nowakowska, M.: *Language of Motivation and Language of Actions*, Mouton, The Hague, 1973.

[6] Nowakowska, M.: ‘A formal theory of actions’, *Behavioral Science* **18**, 1973, 393–416.

[7] Nowakowska, M.: *Teoria działania : próba formalizacji* (*Action Theory : An Attempt of Formalization*), PWN, Warszawa, 1973.

[8] Nowakowska, M.: ‘Algebra celów i algebra sposobów’ (‘Algebra of goals and algebra of means’), *Prakseologia* **1**, 1975.

[9] Nowakowska, M.: ‘Motivationskalkül’. In : G. Eberlein, W. Leinfellner, W. Kroeber-Riel (eds.) *Forschungslogik der Sozialwissenschaften*, Bertelsmann, Düsseldorf, 1974.

<!-- page 35 -->

**177** · A FORMAL THEORY OF ACTIONS

[10] Nowakowska, M. : ‘Towards formal theory of dialogues’, *Semiotics* **17** (4) 1976.

[11] Nowakowska, M. : *Teoria badań : ujęcia modelowe (Theories of Research : Modelling approaches)*, PWN, Warszawa, 1977. English edition in preparation.

[12] Nowakowska, M. : ‘Cybernetics and social systems’. In : R. Trappl (ed.), *Cybernetics — A Sourcebook*, Campus Verlag (in press).

[13] Przetacznikowa, M. : *Podstawy rozwoju dzieci i młodzieży (The Foundations of Development of Children and Adolescents)*, PZWS, Warszawa, 1973.

[14] Tversky, A. : ‘Intransitivity of preferences’, *Psychological Review* **76** (1) 1969.

[15] Zadeh, L. A. : ‘Fuzzy sets’, *Information and Control* **8**, 1965.
