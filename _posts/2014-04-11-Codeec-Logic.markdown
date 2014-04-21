---
layout: post
title:  "Catalyst style reasoning in Codeec"
---

Introduction
=============

This post is primarily a notepad. We trying to answer following two
questions:

+ How do we construct _vis_, _so_ and _ar_ relations ([Burkhardt et
  al., POPL'14](http://research.microsoft.com/apps/pubs/default.aspx?id=201602) -
  referred to as "the paper" in this post) using Catalyst
  infrastructure.
+ Are there catalyst equivalents for multiple operations on relations
  used in the paper?
+ What are precise semantics of _known_ set?
    + Static Semantics - How is it used in the specification checking
      phase?
    + Dynamic Semantics - How does it manifest in an execution?
+ Examples of _known_ sets for multiple specifications from the paper.



Visibility and Session Order as Structural  Relations
======================================================

Structural relations, as the name indicates, are defined over a
structure (algebraic structure, to be precise). Since _vis_ and _so_
are relations over an execution, it is imperative that we represent
execution as an algebraic structure. We concretize this intuition by
representing execution as the following algebraic datastructure:

{% highlight haskell %}

-- An execution tree
data ExecTree = ExecTree { action   :: Action,
                           visTo    :: [ExecTree],         -- list of executions, 
                                   -- one each for every outgoing visibility edge
                           nextInSo :: Maybe (ExecTree)}   -- The next execution in 
                                   -- program order

-- An execution, with one execution tree for each session
data Exec = [ExecTree]

{% endhighlight %}

Let us assume the following parametric relations on auxiliary datatypes:
    
    (ROpt R)(Maybe x) = R(x) | NONE = {()};
    (RMem R) (l) = (* usual definition of parametric membership 
                    relation over lists *)

Set of all actions is the following structural relation:

    RAct-top (ExecTree {action,...}) = {(action)}; 
    RAct = RAct-top *; (* Will use Rmem and Ropt to construct the set *)

Consider One-step _vis_ relation (RVis-step), which relates an action
(_a1_)in one replica to a unique action in every other replica that
first sees _a1_. The relation can be defined as following:

    RVis-step-top (ExecTree {action, visTo, ...}) = {(action)} X 
                                          (RMem RAct-top)(visTo)
    RVis-step = RVis-step-top *;

Now, the visibility relation:

    RVis-top (ExecTree {action, visTo, ...}) = {(action)} X (RMem RAct)(visTo)
    RVis = RVis-top *;

A simple session-order relation that relates an action to its
succeeding action in the same session:

    RSo-succ-top (ExecTree {action, nextInSo, ...}) = {(action)} X 
                                                (ROpt RAct-top)(nextInSo)
    RSo-succ = RSo-succ-top *;

Now, the session order relation:

    RSo-top (ExecTree {action, nextInSo, ...}) = {(action)} X 
                                                (ROpt RAct)(nextInSo)
    RSo = RSo-top *;

Let us not consider arbitration relation (_RAr_) yet. We shall get
back to arbitration when we are satisfied with rest of the
formalization.

The relations we constructed so far are non-parametric. They are
simply sets of (tuples of) actions. However, we definitely need their
parametric versions (i.e., _(RVis R)_ instead of just _RVis_, and so
on). This is because actions have attributes, and we would like to
parametrize our definitions on relations that relate actions to
attributes.

Relation Composition Constructs from The Paper
=============================================

+ Transitive closure is directly supported by Catalyst.
+ Union, Intersection, Difference, and Subset are also directly supported. 
+ Binary relation composition is represented using semi-colon in the
  paper (eg: vis; so). How do we represent such composition? Although
  surface syntax of catalyst provides no direct way of representing
  (R1;R2), for arbitrary relations R1 and R2, the internal bind syntax
  of Catalyst is capable of representing such composition. Here
  is how we represent (RVis; RSo) in bind syntax:

          (RVis; RSo)(e) = bind(RVis(e), \(a1,a2). {(a1)} X 
                              bind( bind (RSo(e), \(a3,a4).REq(a2,a3)X{(a4)}),
                                    \(a3,a4).{(a4)}))

  Where, `REq(x,y) = {(x)} - ({(x)} - {(y)})`.
  The above definition can be made to look intuitive by introducing
  new syntactic sugar.
+ Inverse of a relation can be defined trivially using bind:

            RVis-inv(e) = bind (RVis(e), \(a1,a2). {(a2,a1)}).

In summary, all relational constructs used in the paper are already
supported by catalyst, either directly, or indirectly using bind
syntax.

Knowledge Representation - Known Set
=====================================

Example 1
==========

Consider the following simple specification, which imposes total order
on all actions:

> $$\forall a0,a1 : Action, vis(a0,a1) \vee vis(a1,a0) $$

Let us name the spec as TO. Consider an action A (referred as the
_current action_) over a replicated datatype D with TO as its spec.
If we instantiate TO with A (i.e., TO(A)), the resultant assertion
is equivalent to the following:

> $$\forall a1: Action , vis(A,a1) \vee vis(a1,A)$$

The above assertion actually states the pre-condition that needs to be
satisfied before the action can take effect. Consider an instance
(referred to as the _current instance_) of the replicated datatype D,
which is tasked with executing an occurance of the action A on D. The
instance is faced with following questions:

1. Is it possible to check A's pre-condition locally (i.e., without
   global coordination)? More formally, does there exist an oracle
   that would answer YES, if A's pre-condition can be checked locally,
   and NO otherwise?
2. If it is possible to check the pre-condition locally, how should
   the check be carried out? Formally, can the oracle provide
   constructive proof if its answer is YES?
3. If it is not possible to check locally, what are the semantics of A? 

For the current example (TO(A)), it is not possible to discharge the
pre-condition of A locally. Why? By meticulous book-keeping, the
instance can answer what actions are directly, or transitively,
visible to the current action, but it has no way of knowing what
actions the current action is visible to, unless it asks other
instances. That is, discharging the pre-condition requires global
coordination. 

Formalization Attempt
=====================

We now formalize the intuition stated in the previous paragraph.
Henceforth, we assume that specifications are drawn from the below
grammar:

$$
  \begin{array}{lcl}
    spec & ::= & \forall \overline{a:Action}. \phi\\
    \phi & ::= & vis(x,y) \mid so(x,y) \mid \phi
      \wedge \phi \mid \phi \vee \phi \mid \phi \Rightarrow \phi\\
  \end{array}
$$

We assume that visibility (_vis_) and session-order (_so_) relations
are asymmetric (i.e., anti-symmetric and irreflexive):

$$
  \begin{array}{c}
    \forall a,b:Action, vis(a,b) \Rightarrow \neg vis(b,a)\\
    \forall a,b:Action, so(a,b) \Rightarrow \neg so(b,a)
  \end{array}
$$

We define a context $$\Gamma$$ that encapsulates aforementioned axioms
over _vis_ and _so_ relations. Let $$S$$ denote a set of all
specifications in the system. We say that the system is consistent if
and only if the following formula is invalid:

$$
  \begin{array}{c}
    \Gamma, S \vdash false
  \end{array}
$$

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
$$
  \begin{array}{c}
    \Gamma, known \vdash \forall \overline{a:Action}. \phi 
    \Leftrightarrow
    \forall \overline{a:Action}. \bigwedge_{a_i}{known(a_i)} \wedge \phi
  \end{array}
$$

-----

To understand the intuition behind the _known_ judgement, observe
that:

+ The original specification (left side of $$\Rightarrow$$) quantifies
  over entire universe of actions ($$\forall \overline{a:Action}.
  \phi$$).
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

__Side Note:__
For the TO(A) specification, one might also have arrived at the
conclusion that it cannot be checked locally, only by analyzing the
syntax of the specification; The specification formula contains
predicate $$vis(A,a)$$, which asserts the visibility of the current
action (A). Since this cannot be known locally, the formula cannot be
decided locally. Although the reasoning works for this example, the
syntactic method fails for the following formula:

> $$ \forall a:Action, vis(a,A) \wedge vis(a,b) \Rightarrow vis(b,A) $$

It might be possible to extend the syntactic method to deal with
formulas such as above, but we chose to ignore this currently.

Example 2
=========

Now, consider the Causal Order (CO) specification on action A
given below:

> $$CO(A) = \forall a,b : Action, vis(a,b) \wedge vis(b,A) \Rightarrow vis(a,A)$$

With CO, unlike with TO, reasoning with _known_ set will let us
conclude that it is possible to know about the existence of all such
actions (a and b), which is required to soundly check the
pre-condition of A.  That is, following formula is valid:

$$
  \begin{array}{c}
    \Gamma, known \vdash CO(A) & \Leftrightarrow & \forall a,b : Action, known(a) \wedge
        known(b) \\
     & & \quad \quad \wedge (vis(a,b) \wedge vis(b,A) \Rightarrow vis(a,A))\\
  \end{array}
$$

The intuitive reason behind the validity of _known_ judgement for
CO(A) is as following: Given that causal order is the transitive
closure of session-order and visiblity relations (i.e., $$co = (vis
\cup so)^{+}$$), any action that causally preceedes the current action
is reachable via edges of _vis_ and _so_ relations. But, all actions
that are reachable via _vis_ and _so_ edges from the current action
are already _known_. Therefore, CO(A) can be checked locally.

Observe that, albeit the set _known_ contains all actions that are
directly or transitively visible to A, or in session order with A, it
does not store whether there exist any _vis_ or _so_ relationships
among the known actions. In other words, _known_ contains all nodes of
$$(vis \cup so)^{+}$$ graph, but not its edges. With this _known_ set,
our current formulation of _known_ judgement, as shown above, only
lets us deduce that it is possible to check the pre-condition of A
locally. The _known_ set may not, in most cases, have sufficient
information to actually carry out the check. Take CO(A) specification,
for example. The knowledge of all actions (and only actions) that are
directly or transitively reachable via _vis_ edges is not sufficient
to answer which among them are directly visible to A (i.e., A's
instance saw their effect), and which are not yet directly visible
(i.e., A's instance is yet to see their effect), but are visible only
to the directly visible actions of A. The instance cannot check the
specfication, and cannot decide whether to wait or to proceed, unless
it can make this distinction.

As a more serious example, consider the following Weak Total Order
(WTO) specification:

> $$WTO(A) = \forall (a,b : Action), vis(a,A) \wedge vis(b,A)
> \Rightarrow vis(a,b) \vee vis(b,a)$$

Its _known_ judgement is as following:

$$
  \begin{array}{lcl}
    \Gamma, known \vdash WTO(A) & \Leftrightarrow & \forall (a,b : Action), known(a) \wedge
      known(b)\\
           & & \quad \quad \wedge (vis(a,A) \wedge vis(b,A) \Rightarrow vis(a,b) \vee
      vis(b,a))\\
  \end{array}
$$

Using the same definition of _known_ set as the previous example, the
above formula is clearly valid. Therefore, WTO(A) can be discharged
locally, as expected. However, is our knowledge accumulated through
_known_ set sufficient to check the WTO(A) specification locally? The
answer is no. Although we know about existence of all _a_'s and _b_'s
that are visible to the current action (i.e., _vis(a,A)_ and
_vis(b,A)_), our knowledge is not enough to determine if _a_ is
visible to _b_ (i.e., _vis(a,b)_). As noted previously, we do not know
of any relations that might exist among actions of the _known_ set.
Clearly, our formulation of _known_ does not give us any clues on how
to check specifications locally. Formally, an oracle that relies on
the _known_ judgement formulated above can answer if a specification
can be checked locally, but cannot generate a constructive proof if
its answer is YES. 

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
> We define $$known : B \rightarrow bool$$, which determines if an
> edge is known or not.

For the current action A, the largest _known_ set is constructed by
recursively traversing _vis_ and _so_ edges:

$$
  \begin{array}{c}
    \forall a:Action, vis(a,A) \Rightarrow known(edgeId(VIS,a,A)\\
    \forall a:Action, so(a,A) \Rightarrow known(edgeId(SO,a,A))\\
    \forall a,b:Action, vis(a,b) \wedge known(edgeId(\_,b,\_))
    \Rightarrow known(edgeId(VIS,a,b))\\
    \forall a,b:Action, so(a,b) \wedge known(edgeId(\_,b,\_))
    \Rightarrow known(edgeId(SO,a,b))\\
  \end{array}
$$

Observe that $$\forall a,b:Action, known(edgeId(VIS,a,b)) \Rightarrow
vis(a,b)$$, but the converse is not true. Therefore,
$$known(edgeId(VIS,a,b)) = true$$ should be interpreted as:

    Action a is visible to action b, and the fact is known (at the
    current instance).

Similarly, $$known(edgeId(VIS,a,b)) = false$$ should be interpreted as:

    It is not known (at the current instance) whether action A is
    visible to action B.

We define a function $$\alpha_{k_{}}$$, called _interpretation modulo
knowledge_, on the syntax of specification formulas as the following:

$$
  \begin{array}{lcl}
    \alpha_{k_{}} (\forall \overline{a:Action}. \phi) & = & \forall
      \overline{a:Action}. \alpha_{k_{}} (\phi)\\
    \alpha_{k_{}} (vis(x,y)) & = & known (edgeId(VIS,x,y))\\
    \alpha_{k_{}} (so(x,y)) & = & known (edgeId(SO,x,y))\\
    \alpha_{k_{}} (\phi_1 \odot \phi_2) & = & \alpha_{k_{}} (\phi_1)
    \odot \alpha_{k_{}} (\phi_2)\\
  \end{array}
$$

Where, $$\odot \in \{\wedge, \vee, \Rightarrow \}$$. Function
$$\alpha_{k_{}}$$ interprets a given specification formula in terms of
the available knowledge. Let $$\Gamma$$ denote the context containing
the new definition of _known_ as stated above, and definitions of _vis_
and _so_ as asymmetric relations over actions. The relationship
between a specification formula ($$spec$$) and its interpretation modulo
knowledge ($$\alpha_{k_{}}(spec)$$) is as captured by the following
valid formula:

---------
$$
  \begin{array}{c}
     \Gamma, known \vdash \alpha_{k_{}}(spec) \Rightarrow spec\\
  \end{array}
$$
---------

That is, <u>if a specification is <em>known</em> to hold, then the
specification holds.</u> However, the converse, may not be true as
demonstrated by the the total order specification ($$TO(A)$$) defined as
following:

> $$\forall a: Action, vis(A,a) \vee vis(a,A)$$

Its interpretation modulo knowledge ($$\alpha_{k_{}}(TO(A))$$) is
given below:

> $$\forall a: Action, known(edgeId(VIS,A,a)) \vee known(edgeId(VIS,a,A)$$

Even with the maximum knowledge (i.e., the largest _known_ set defined
previously), $$TO(A) \Rightarrow \alpha_{k_{}}(TO(A))$$ does not
hold, as $$vis(A,a)$$ does not imply $$known(edgeId(VIS,A,a))$$. That
is, a total order specification can be valid, even when it is not
_known_ to be valid. This is what makes it impossible to check TO(A)
locally.

The above observation, leads us directly to our main hypothesis:

+ __Locally Checkable Specification__ is a specification, which is
  valid if and only if it is _known_ to be valid. Formally, a
  specification ($$spec$$)  is locally checkable if and only if the
  following is valid:

  $$\Gamma, known \vdash spec \Leftrightarrow \alpha_{k_{}}(spec)$$

In our example, CO(A) can be checked locally, as the following
formula is valid:

> $$\forall a,b : Action, vis(a,b) \wedge vis(b,A) \Rightarrow vis(a,A)$$ <br />
> $$\quad \quad \quad \Leftrightarrow $$ <br />
> $$\forall a,b : Action, known(edgeId(VIS,a,b)) \wedge
> known(edgeId(VIS,b,A)) \Rightarrow known(edgeId(VIS,a,A))$$ <br />

Given that our knowledge includes the transitive closure of visibility
relation:

> $$ \forall a:Action, vis(a,A) \Rightarrow known(edgeId(VIS,a,A))$$ <br />
> $$ \forall a,b:Action, vis(a,b) \wedge known(edgeId(VIS,b,A))
> \Rightarrow known(edgeId(VIS,a,b))$$ <br /> 


Scratch
==========
Observe that the above definition of minimal _known_ set to check CO(A)
is syntactically close to the definition of CO(A) itself. Infact, we
hypothesize that there exists an algorithm to calculate the minimal
_known_ set from the syntax of the specification itself, provided that
it is possible to check the specification locally (This can be checked
with maximal _known_ set). Discussion on this is deferred to a later
time.

With the new formulation of _known_ set, and the concept of minimal
_known_ set, we can now answer what data needs to be recorded in
order to have enough knowledge to check the specification locally.
However, we haven't yet answered the question of how to actually
perform the check.


Consider the following simple specification known as Read-Your-Writes
(RYW) in the paper:

> An operation sees all previous operations by the same session. That
> is, $$soo \subseteq vis$$.

If we instantiate RYW with A (i.e., RYW(A)), the resultant assertion
is equivalent to the following:

> $$\forall a \in Actions, soo(a,A) \Rightarrow vis(a,A)$$
