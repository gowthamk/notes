---
layout: post
title:  "Codeec Formalization"
---

##Introduction##

This post is an improved version of [previous](https://www.cs.purdue.edu/sss/projects/catalyst/2014/04/11/Codeec-Logic.html)
post on reasoning in Codeec. We reproduce the informal discussion on
knowledge representation from previous post, along with more formal
description of the system, problem and our current solution. 

<div>
\[
\newcommand{\ALT}{~|~} 
\newcommand{\spec}{\forall \overline{a}. \phi
    \Rightarrow \psi} 
\newcommand{\cf}[1]{CoordFree(#1)}
\newcommand{\llbracket}{[\![} 
\newcommand{\rrbracket}{]\!]}
\newcommand{\conj}{\wedge}
\newcommand{\disj}{\vee}
\newcommand{\specs}{\overline{spec}}
\newcommand{\Conj}{\bigwedge}
\]
</div>

###Formalization###

Recall that a replicated datatype is an abstract datatype which is
replicated across a (geo-)distributed system such that each node in
the system owns an _instance_ of the datatype. A source (eg:user)
performs effectful actions on the datatype at possibly different
instances of the datatype. Owing to practical concerns, such effects
cannot be propagated to other instances instantaneously; so, different
instances of the datatype cannot be kept consistent.  Instead, it can
be assumed that such effects propagate to all instances eventually,
such that different instances of the datatype can reach consistency
eventually.  In this work, we only deal with such eventually
consistent replicated datatypes; so, we assume that any action
performed at one instance of the replicated datatype is bound to be
propagated to all instances eventually.

The starting point of our formalization is the replicated datatype
specification ($$F_T$$, where $$T$$ is the datatype that was
replicated) from Burkhardt et al.'s paper. We would ideally like to
extend actions of $$F_T$$ with consistency specifications, examples of
which are abound in the paper. For instance, we would like to specify
that _withdraw_ operations on _BankAccount_ replicated datatype are
totally ordered:

$$
  \forall (a,b : Action), isWithdraw(a) \conj isWithdraw(b)
  \Rightarrow vis(a,b) \disj vis(b,a)
$$

or that when a _getBalance_ sees a _withdraw_ operation, it should
also see all operations that were seen by the _withdraw_ operation
(this is to ensure that _getBalance_ does not show negative balance):

$$
  \forall (a,b,c : Action), vis(a,b) \conj isWithdraw(b) \conj
  isGetBalance(c) \conj vis(b,c) \Rightarrow vis(a,c)
$$

However, to keep things simple we start with a simple system, where
the abstract datatype being replicated defines only one action.
This obviates the need for predicates, such as _isWithdraw_, to
distinguish among actions in consistency specifications. Consequently,
we define an extended version ($$F^1_T$$) of replicated datatype
specification ($$F_T$$) as:
<div>
$$F^1_T = (F_T,\specs)$$
</div>

Where $$\specs$$ is a set of specifications on the only action defined
by $$F_T$$. A specification of an action is a formula in first-order
logic that defines a pre-condition that needs to be true before the
action can effect. Specifications are drawn from a restricted grammar
defined below:
(This is the same grammar as defined by KC 
[here](http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/04/15/Analyzing-Codeec-Consistency-Specification.html)):

$$ 
 \begin{array}{rcl} 
    a,b,x & \in & Action \\ 
    lspec & := & \spec \\ 
    \phi & := & True \ALT vis(a,b) \ALT so(a,b) \ALT inVis(a) \ALT inSo(a)
       \ALT \phi \odot \phi \\ 
    \psi & := & inVis(a) \ALT \psi \odot \psi \\
    \odot & := & \wedge \ALT \vee \\ 
 \end{array}
$$

Visibility (_vis_) and session-order (_so_) relations are binary
relations over actions. _vis(a,b)_ should be read as _action a is
visible to action b_, and _so(a,b)_ should be read as _action a
preceedes action b in session-order_. Both relations are asymmetric
(i.e., anti-symmetric and irreflexive):

$$
  \begin{array}{c}
    \forall a,b:Action, vis(a,b) \Rightarrow \neg vis(b,a)\\
    \forall a,b:Action, so(a,b) \Rightarrow \neg so(b,a)
  \end{array}
$$

It should be noted that relations _vis_ and _so_ were directly taken
from the paper, where they are part of the operational context of the
replicated datatype specification ($$F_T$$). 


We define a context $$\Gamma$$ that encapsulates aforementioned axioms
over _vis_ and _so_ relations. Now, the given set of specficiations
$$\specs$$ is consistent if and only if the following formula is
invalid:

$$
  \begin{array}{c}
    \Gamma, \Conj specs \vdash false
  \end{array}
$$

If $$spec$$ is a specification, and $$A$$ is an instance of the sole
action defined on our replicated datatype ($$F_T$$), then predicate
$$isVis(x)$$ is elaborated to $$vis(x,A)$$.

Let us define $$known$$ as the largest set of actions whose existence
can be known by the current instance. As noted previously, an action
can be known if it can reach current action via visiblity and
session-order edges. Formally:

$$
  \begin{array}{c}
     \forall a:Action, vis(a,A) \Rightarrow known(a)\\
     \forall a:Action, so(a,A) \Rightarrow known(a)\\
     \forall a,b:Action, vis(a,b) \wedge known(b) \Rightarrow
       known(a)\\
     \forall a,b:Action, so(a,b) \wedge known(b) \Rightarrow known(a)\\
  \end{array}
$$

Recall our observation that TO(A) could not be checked locally only
because we do not _know_ of existence of all $$a:Action$$ such that
$$vis(A,a)$$. To state it conversely, if we perform the TO(A) check
locally on only _known_ actions, it is not equivalent to performing
the TO(A) check on the universe of all actions. To state it formally,
under the context ($$\Gamma$$) extended with the definition of
_known_, the following formula is __invalid__:

> $$(\forall a: Action, vis(A,a) \vee vis(a,A)) \Leftrightarrow$$
> $$(\forall a: Action, known(a) \wedge (vis(A,a) \vee vis(a,A)))$$

We name the above judgement as _known_ judgement of TO(A).  In
general, __a specification can be checked locally if and only if the
_known_ judgement for the specification is valid__. For a
specification of form $$\forall \overline{a:Action}. \phi$$, we define
its _known_ judgement as:

-----
<div>
\[
  \begin{array}{lclcl}
    \Gamma, known & \vdash & (\spec
    & \Leftrightarrow & 
    \forall \overline{a}. \bigwedge_{a}{known(a)} \wedge \phi
      \Rightarrow \psi)\\
  \end{array}
\]
</div>
-----

To understand the intuition behind the _known_ judgement, observe
that:

+ The original specification (left side of $$\Rightarrow$$) quantifies
  over entire universe of actions ($$\forall \overline{a}. ...).
+ The _known_ projection of the specification (right side of
  $$\Rightarrow$$) effectively quantifies only over actions in the
  _known_ set, which is the set of all actions whose existence can be
  known by the current action.

Therefore, the _known_ judgement asserts that the specification
formula has same semantics when its free variables range over the
entire universe of actions, and when its free variables range only
over _known_ actions. In other words, the specification, when checked
locally using _known_ actions, yeilds same result as in the case when
it is checked for the universe of all actions.

Now, consider the Causal Order (CO) specification on action A
given below:

New representation of knowledge
===============================

Observe that, albeit the set _known_ contains all actions that are
directly or transitively visible to A, or in session order with A, it
does not store whether there exist any _vis_ or _so_ relationships
among the known actions. In other words, _known_ contains all nodes of
$$(vis \cup so)^{+}$$ graph, but not its edges. With this _known_ set,
our current formulation of _known_ judgement, as shown above, only
lets us deduce that it is possible to check the pre-condition of A
locally. The _known_ set may not, in most cases, have sufficient
information to actually carry out the check. 

In order to remedy this, we extend our knowledge to include not only
_what_ actions can be known, but also _how_ they can be known. More
concretely, we redefine the _known_ set, which currently includes the
vertices of DAGs representing _vis_ and _so_ relations, to represent
their edges, instead. The new fomulation of _known_ is given below:

> Let $$L \in \{VIS,SO\}$$ denote labels of edges in visibilty and
> session-order relations.
> Let $$B$$ denote an uninterpreted sort that admits equality.
> Let $$edgeId : L \times Action \times Action \rightarrow B$$ be a
> function that maps edges of _vis_ and _so_ relations to their unique
> IDs. That is, $$edgeId$$ is injective function.
> We define $$known_{\rightarrow_{}} : B \rightarrow bool$$, which determines if an
> edge is known or not. Read as _known edge_, or _known relation_.

For the current action A, the largest _known_ set is constructed by
recursively traversing _vis_ and _so_ edges:

$$
  \begin{array}{c}
    \forall a, vis(a,A) \Rightarrow known_{\rightarrow_{}}(edgeId(VIS,a,A)\\
    \forall a, so(a,A) \Rightarrow known_{\rightarrow_{}}(edgeId(SO,a,A))\\
    \forall a,b, vis(a,b) \wedge known_{\rightarrow_{}}(edgeId(\_,b,\_))
    \Rightarrow known_{\rightarrow_{}}(edgeId(VIS,a,b))\\
    \forall a,b, so(a,b) \wedge known_{\rightarrow_{}}(edgeId(\_,b,\_))
    \Rightarrow known_{\rightarrow_{}}(edgeId(SO,a,b))\\
  \end{array}
$$

To simplify presentation, we write $$known_{\rightarrow_{}}(vis(a,b))$$ 
as a shorthand for $$known_{\rightarrow_{}}(edgeId(vis(a,b))$$.

Observe that $$\forall a,b, known_{\rightarrow_{}}(vis(a,b)) \Rightarrow
vis(a,b)$$, but the converse is not true. Therefore,
$$known_{\rightarrow_{}}(vis(a,b)) = true$$ should be interpreted as:

-------------------
<div>
Action a is visible to action b, and the fact is known (at the
current instance).
</div>
-------------------

Similarly, $$known_{\rightarrow_{}}(edgeId(VIS,a,b)) = false$$ should be interpreted as:

-------------------
<div>
It is not known (at the current instance) whether action A is
visible to action B.
</div>
-------------------

We define a function $$\alpha_{k_{\rightarrow}}$$, called _interpretation modulo
knowledge_, on the syntax of specification formulas as the following:

$$
  \begin{array}{lcl}
    \alpha_{k_{\rightarrow}} (\forall \overline{a}. \phi \Rightarrow \psi) & = & \forall
      \overline{a}. \alpha_{k_{\rightarrow}} (\phi) \Rightarrow \alpha_{k_{\rightarrow}} (\psi)\\
    \alpha_{k_{\rightarrow}} (True) & = & True \\
    \alpha_{k_{\rightarrow}} (vis(x,y)) & = & known_{\rightarrow_{}} (vis(x,y))\\
    \alpha_{k_{\rightarrow}} (so(x,y)) & = & known_{\rightarrow_{}} (so(x,y))\\
    \alpha_{k_{\rightarrow}} (\phi_1 \odot \phi_2) & = & \alpha_{k_{\rightarrow}} (\phi_1)
    \odot \alpha_{k_{\rightarrow}} (\phi_2)\\
    \alpha_{k_{\rightarrow}} (\psi_1 \odot \psi_2) & = & \alpha_{k_{\rightarrow}} (\psi_1)
    \odot \alpha_{k_{\rightarrow}} (\psi_2)\\
  \end{array}
$$

Where, $$\odot \in \{\wedge, \vee, \Rightarrow \}$$. Function
$$\alpha_{k_{\rightarrow}}$$ is analogous to abstraction function in theory of
abstract interpretation. It interprets a given specification formula
in terms of the available knowledge. 

We now define locally checkable specification as following:

---------

__Locally Checkable Specification__ is a specification, which is
valid if and only if it is _known_ to be valid. Formally, a
specification ($$spec$$)  is locally checkable if and only if the
following is valid:

$$\Gamma, known_{\rightarrow_{}} \vdash spec \Leftrightarrow \alpha_{k_{\rightarrow}}(spec)$$
<br />

--------

Theorem relating locally checkable specification to coordination
freedom:

---------
__Theorem__ A locally checkable specification is coordination free:
<div>
$$
\begin{array}{c}
  \Gamma, known_{\rightarrow_{}}, known_{\bullet_{}} \vdash 
    (spec \Leftrightarrow \alpha_{k_{\rightarrow_{}}}(spec)) 
    \Rightarrow
    (spec \Leftrightarrow \alpha_{k_{\bullet_{}}}(spec)) 
\end{array}
$$
</div>
---------


Minimal Knowledge Set
=====================

Observe that if a specification is locally checkable, then
$$known_{\rightarrow_{}}$$ contains sufficient knowledge to check the
specification locally. We have defined $$known_{\rightarrow_{}}$$ as
the largest set of knowledge that is accessible to an instance. But,
do we require the entire accessible knowledge to check all locally
checkable specifications?  Not necessarily. For eg, consider the
following _Read-Your-Writes (RYW)_ specification:

$$
  RYW \triangleq \forall a. inSo(a) \Rightarrow inVis(a)
$$

Clearly, RYW is locally checkable specification. But we do not require
the knowledge of all accessible _vis_ and _so_ edges to check this
specification. Infact, the knowledge of only those _vis_ and _so_
edges that are incident on the current action (A) is sufficient to
check the specification. That is, the following
$$known_{\rightarrow_{}}$$ set is sufficient to check RYW:

$$
  \begin{array}{c}
    \forall a, vis(a,A) \Rightarrow known_{\rightarrow_{}}(vis(a,A)\\
    \forall a, so(a,A) \Rightarrow known_{\rightarrow_{}}(vis(a,A))\\
  \end{array}
$$

The above _known_ set is the _minimal knowledge set_ required to check
RYW locally.

Consider the causal order (CO) specification:

$$
  \forall a,b. vis(a,b) \conj inVis(b) \Rightarrow inVis(a)
$$

In order to check CO spec, it is necessary and sufficient to keep
track of causal visibilty relation as our knowledge:

$$
  \begin{array}{c}
    \forall a, vis(a,A) \Rightarrow known_{\rightarrow_{}}(vis(a,A)\\
    \forall a,b, vis(a,b) \wedge known_{\rightarrow_{}}(vis(b,\_))
      \Rightarrow known_{\rightarrow_{}}(vis(a,b))\\
  \end{array}
$$


Looking at the definition of minimal knowledge set of RYW and CO, one
might come up with a method similar to $$CoordFree$$ analysis method
to calculate the minimal knowledge set. Such a method observes the
formula, and iteratively increases the depth of the $$(vis \cup
so)^+$$ covered in the knowledge set. However, such a method need not
necessarily produce minimal knowledge set, as the following
specification demonstrates:

$$
  \forall a,b,c,d. isVis(a) \conj isVis(b) \conj vis(c,a) \conj vis
  (d,a) \\
  \quad \quad \conj isWithdraw(c) \conj isWithdraw(d) \conj (vis(c,d) \disj
  vis(d,c)) \Rightarrow isVis(c) \conj isVis(d)
$$

Assuming that withdraw operation has total order (TO) specification,
one of the conjuncts in the premise of the above spec:

$$
  (vis(c,d) \disj vis(d,c))
$$

is trivially true. Nevertheless, the iterative method of calculating
minimal knowledge set would have extended the depth of the graph
covered to 3 in order to track visibility relation for actions c and
d. This is not necessary.

The reason behind this problem is that we do not take into account,
the invariants guaranteed by actions that are visible (hence, already
executed at some instance). In this case, when _c_ and _d_ are
_withdraw_ actions visible to the current action, they should have
been totally ordered, already. So, there is no need to check the
invariant again. To capture this, we define a _rely_ set that
captures all the invariants on actions that we know exist. For eg, if
we _know_ that two withdraw actions _x_ and _y_ are visible to the
current action, then we can _rely_ on them being totally ordered:

$$
  \begin{array}{lcl}
    known_{\rightarrow_{}}(vis/so(x,\_)) \conj
    known_{\rightarrow_{}}(vis/so(y,\_)) & \Rightarrow & rely(vis(x,y))
        \disj rely(vis(y,x))\\
    \conj isWithdraw(x) \conj isWithdraw(y) & & \\
  \end{array}
$$


$$\alpha_{k_{\rightarrow}}(spec)$$ tells us how to actually
carry out the check. 

Scratch
========
$$\forall a. vis(a,A) \disj vis(A,a)$$

$$\alpha_{k_{\rightarrow}}(TO) = 
  \forall a. known_{\rightarrow_{}}(vis(a,A)) \disj known_{\rightarrow_{}}(vis(A,a))
$$

$$\forall a,b. vis(a,b) \conj vis(b,A) \Rightarrow vis(a,A)$$
$$\alpha_{k_{\rightarrow}}(Cau)
    =
  \forall a. known_{\rightarrow_{}}(vis(a,b)) \conj known_{\rightarrow_{}}(vis(b,A)) \Rightarrow 
    known_{\rightarrow_{}}(vis(a,A))
$$
