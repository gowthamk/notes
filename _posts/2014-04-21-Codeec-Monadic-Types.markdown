---
layout: post
title:  "Monadic Types for Codeec"
--- 
A replicated datatype is an abstract datatype which is replicated
across a (geo-)distributed system such that each node in the system
owns an _instance_ of the datatype. A source (eg:user) performs
effectful actions on the datatype at possibly different instances of
the datatype. Owing to practical concerns, such effects cannot be
propagated to other instances instantaneously; so, different instances
of the datatype cannot be kept consistent.  Instead, it can be assumed
that such effects propagate to all instances eventually, such that
different instances of the datatype can reach consistency eventually.
In this work, we only deal with such eventually consistent replicated
datatypes; so, we assume that any action performed at one instance of
the replicated datatype is bound to be propagated to all instances
eventually.

Recall that the specification of an abstract datatype is a collection
of all operations allowed on the datatype, along with their abstract
description, usually written as their types. For example, ML signature
`STACK` with an abstract `type t`, and types for `push` and `pop`
operations is a specification of abstract datatype _Stack_. When such
an abstract datatype is replicated across multiple physical locations,
the usual correctness specifications may not be sufficient to ensure
the consistency of its observable behaviour. Therefore, it is required
that the specification of a replicated abstract datatype describe the
conditions required for its observable behaviour to converge
eventually. We call such specifications as consistency specifications.
Consistency specifications can be analyzed to determine whether an
action requires global coordination among all replicas of the datatype
to ensure the consistency of its observable behaviour. When such
coordination is not required, consistency specification of an action
determines the conditions over the local state (of a replica) that
need to be true in order for the action to consistently take effect.

In this writeup, we provide some examples of how such consistency
specifications can be written as types over the actions of the
replicated datatype. We also describe how consistency specifications
can be checked for the coordination freedom (_CoordFree_) property, as
described above, by formulating the problem as type checkign problem.
We use Burkhardt et al.'s formalism (specifically, _vis_ and _so_
relations) to describe the _operational context_ of an action. Please
refer to the [previous writeup]() for the introduction.


Example 1
=========

Consider an integer counter abstract datatype with encapsulated
state, offering two functions: 

{% highlight haskell %}
    read :: State Int Int
    increment :: State unit Int
{% endhighlight %}

In the above type specification, `State a b` is a monad that
represents computations over a state of type `a` returning a value of
type `b`. The functional equivalent of the computational type `State
a b` is the following type:

    forall a,b. a -> (a * b)

So, functional equivalent of type of `read`, which reads an integer
value from the state and returns the value along with the new state,
is given below:

    read :: Int -> (Int * Int)

Indeed, the `read` is expected to return a new state which is same as
its old state. Similarly, the functional equivalent of type of `increment`
is given below:

    increment :: Int -> (unit * Int)

Function `increment` takes the current state (an integer), and returns
a new state, where the integer is incremented by one.

A state monadic computation can be constructed by _binding_ `read`s and
`increment`s, which represents a trace of actions. For example, following
haskell code:

{% highlight haskell %}
    do {
      i <- read
      increment 
      j <- read
    }
{% endhighlight %}

which expands to:

{% highlight haskell %}
    bind (bind (read, fn i => increment), fn () => read)
{% endhighlight %}

represents a sequential trace of actions on integer register data
type. Due to sequential semantics, the value (j) read by the second
`read` action in the trace is always greater than the value (i) read
by the first `read`. This monotonic reads invariant is a consistency
property of integer counter.

Now, let us consider the integer register datatype in a distributed
setting, where the integer state is replicated across multiple
physical nodes. Actions, such as `increment` are issued at any one of the
physical nodes, and are gradually propagated to all other nodes in the
distributed system. In other words, actions performed on one replica
of integer counter eventually become visible to some action on every
other replica of the counter. Let monadic computation shown
above model the series of actions perfomed by an agent (eg: user) on
the replicated integer counter. We call such computation as a session.
As per our model of the system, the agent can issue each action of the
session at a different replica of the integer counter. Under this
setting, the invariant that j is always greater than i does not hold,
as the agent can issue first two actions of the session one replica,
but read the state (i.e., issue third action) at a different replica,
which hasn't seen the effects of first two actions.

In order to constrain such anamoly and preserve the monotonous reads
invaraint, we can constrain `read` action such that it takes effect if
and only if all actions that precede the `read` action in current
session are visible to the `read` action. Let _inVis_ be a unary
predicate on actions such that for any action _x_, _inVis(x)_ if and
only if _x_ is visible to the `read` action. Similarly, we define
a unary predicate _inSo_ for _so_ relation. Now, the consistency
specification for `read` (i.e., specfication of `read` that guarantees
the consistency of integer counter's observable behaviour) can be
defined as following:

$$
  \forall a. \forall x : State a int. inSo(x) \Rightarrow inVis(x)
$$

Since all actions of integer counter ADT are in state monad, we
quantified over actions of state monad. Instead, we can define a
monad called `IntCtrAct` that is effectively a state monad specialized
to hide the state of integer counter. The integer counter ADT that
uses `IntCtrAct` is given below:

{% highlight haskell %}
    read :: IntCtrAct int
    increment :: IntCtrAct unit
{% endhighlight %}

`IntCtrAct a` is an action over integer counter that produces a value
of type `a`. Using `IntCtrAct` monad, and eliding the type variable
using underscore, we re-write the consistency spec of `read` as
following:

$$
  \forall x : IntCtrAct \_. inSo(x) \Rightarrow inVis(x)
$$

Which straightforwardly states that all integer counter actions that
precede the `read` action in current session must be visible to the
`read` action.

Consistency specification as a type
===================================

Observe that the consistency specification of `read` makes assertions
over its dynamic context defined in terms of _vis_ and _so_ relations.
This situation is analogous to the specification of reference and
de-reference operations into program heap by treating the heap as an
abstract map. The type-based approaches to write such specifications
ascribe monadic types to such operations which conveniently treat heap
as a hidden state encapsulated by the monad. We take the similar
approach to write consistency specifications as types. We define a
concurrent context monad (CCT), which encapsulates the concurrent
context defined in terms of _vis_ and _so_ relations. We extend the
result type of each action, such as `read`, with an `effect` type that
explicitly denotes the effect produced by the action. We then write
the consistency specification of the action as a post-condition over
the effect denoting the fact that the action took effect, while
satisfying the consistency specification.

Here is how we model effects:

{% highlight haskell %}
  {-# LANGUAGE GADTs #-}
  {-# LANGUAGE DataKinds #-}

  data EffectKind = Read | Increment

  data Effect :: EffectKind -> * = 
      Rd :: id -> Effect Read
      Inc :: id -> Effect Increment 
{% endhighlight %}

Let us take the example of `read` operation. Let us define `Ctxt` as a
record type modeling the context: 

{% highlight haskell %}
  type Ctxt = {Rvis :: {Effect a * Effect a}, 
               Rso :: {Effect a * Effect a},
               Rsa :: {Effect a} }
{% endhighlight %}

We would write the type of read as following:

{% highlight haskell %}

    read :: CCT Int (Effect Read) {\ef.\ctxt. ctxt.Rso(ef) ⊆ ctxt.Rvis(ef)}

{% endhighlight %}

Let us denote the refinement as p. Also, for a relation $$R$$, let 
$$univ(R) \triangleq dom(R) \cup range(R)$$. The functional equivalent
of the above type is as following:

{% highlight haskell %}
    read :: {c :: Ctxt | ∀ef :: (Effect Read). 
                        ef ∉ (univ(Rso) U dom(Rvis))
                     /\ p ef ({Rso = c.Rso U (univ(c.Rso) X {(rd)}), 
                               Rvis = c.Rvis}) } 
    -> {x::int * rd::Effect * 
                       {c' :: Ctxt | p rd c'
                                  /\ c'.Rso = c.Rso U (univ(c.Rso) X {(rd)})
                                  /\ c.Rvis ⊆ c'.Rvis}}
{% endhighlight %}

Let us define a functions $$ext$$ on contexts, and $$wp$$ on
propositions parametrized on effects, in the following way:

{% highlight haskell %}
    ext ::∀(a::EffectKind). Ctxt -> Effect a -> Ctxt
    ext = fn c => fn rd => {Rso = c.Rso U (univ(c.Rso) X {(rd)}), Rvis = c.Rvis}

    wp :: ∀(a::EffectKind). (Effect a -> Ctxt -> Prop) -> Ctxt -> Prop
    wp = fn p => fn c => ∀ef:a. ef ∉ (univ(Rso) U dom(Rvis)) /\ p ef (ext c) 
{% endhighlight %}

Using these functions, we re-write the type of read as:

{% highlight haskell %}
    read :: {c :: Ctxt | wp p c} -> {int * {rd :: Effect} * 
                      {c' :: Ctxt | p rd c' /\ c' = ext(c)}}
{% endhighlight %}

<!--
  Following is the type of bind:
  {% highlight haskell %}
      bind :: ∀(a,b). ∀(ext1,ext2). ∀(p1,p2). CST a ext1 (∃<ef1>.p1) -> (a -> CST b ext2 (∃<ef2>.p2)) 
                    -> CST b (ext2 o ext1) (\c'. ∃<ef1,ef2>. ∃c. c' = ext2 c /\ p1 c' /\ p2 c)
  {% endhighlight %}
-->

The type of bind :

{% highlight haskell %}
    bind :: ∀(a,b). ∀(es1,es2). ∀(p1,p2). 
      {m1 :: CST a | Ref(m1) = es1 ∧ p1 ctxt(m1)} -> 
      {a -> {m2 :: CST b | Ref(m1) = es2 ∧ p2 ctxt(m2)}} ->
      {m3 :: CST b | Ref(m3) = es1 ∪ es2 
                   ∧ es1 X es2 ⊆ ctxt(m3).Rso 
                   ∧ p1 ctxt(m3) ∧ p2 ctxt(m3)}
{% endhighlight %}

{% highlight haskell %}
    bind :: ∀(a,b). ∀(es1,es2). ∀(p1,p2). 
      m1 :: CST a es1 p1 -> 
      {a -> {m2 :: CST b es2 p2}} ->
      {m3 :: CST b (es1 ∪ es2) (\x.  es1 X es2 ⊆ x.Rso 
                                   ∧ p1 x ∧ p2 x)}
{% endhighlight %}

Assumptions : (thread specific) Rso is a total order
\forall a,b. Rso (a,b) ∨ Rso(b,a) 
{% highlight haskell %}
    pre :: Effect Set -> (Ctxt -> Prop) -> Ctxt -> Prop
    pre es p = \x. (es is closed under x.Rvis)
                 ∧ (es is closed under x.Rso)
                 ∧ (p x)

    post :: Effect Set -> (Ctxt -> Prop) -> Ctxt -> Ctxt -> Prop
    post es p = \x.\x'. (x'.Rso = x.Rso)
                      ∧ (x.Rvis ⊆ x'.Rvis)
                      ∧ (p x')
{% endhighlight %}

Let `CST b me ms` be a well-formed type under a context Γ. The
functional equivalent of the type under the context Γ is as following:

{% highlight haskell %}
    {c :: Ctxt | pre me ms c} -> {b * {es::Effect Set | es = me} 
                                  * {c' :: Ctxt | post es ms c c'}
{% endhighlight %}

Note: Effects don't admit equality. Therefore, e1 is only equal to
itself, but nothing else.

Here are read and increment:

{% highlight haskell %}
    read :: ∃(ef :: Effect). CST int {(ef)} (\x. sort(ef) = RD 
                         ∧ σ([\ef'.sort(ef') = INC],x.Rso(ef)) ⊆ x.Rvis(ef))
    increment :: ∃(ef :: Effect). CST unit {(ef)} (\x. sort(ef) = INC)
{% endhighlight %}

And, here is an example program:

{% highlight ocaml %}
      val (ef1,m1) = read
      val (ef2,m2) = increment
      val m3 = bind {(ef1),(ef2)} m1 (fn _ => m2)
{% endhighlight %}

whose type is :

{% highlight haskell %}
    CST unit {(ef1),(ef2)} (\x. {(ef1,ef2)} ⊆ x.Rso 
                              ∧ sort(ef1) = RD 
                              ∧ σ(\ef'.sort(ef') = INC],
                                  x.Rso(ef1)) ⊆ x.Rvis(ef))
                              ∧ sort(ef2) = INC
{% endhighlight %}

Notes:
=====
We say a set S is closed under a binary relation R iff 
  ∀x1,x2. x1 ∈ S ∧ R(x1,x2) ⇒ x2 ∈ S

Scratch
=========

(\ctxt. wp (\ef1. \c1. post1 ef1 c1 /\ wp post2 c1) ctxt )
When we say an action A becomes visible
to action B, we mean that action B operates on a state over which the
effect A has already been perfomed. 

