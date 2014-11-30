---
layout: post
title:  "Codeec Z3 Encoding"
--- 

#Introduction#

This post is a followup post of KC's [Is The Context
Ready?] [is-ctxt-ready] post. I use the definitions and conventions
from the previous post. The focus of this post is to define the
problem of determining maximal and minimal _known_ sets and describe an
iterative refinement algorithm to solve the problem.

#The Known Set#

The previous post introduces the notion of _known_ set as a set the
includes the current action, and all actions that are visible to the
current action. Recall that a coordination-free Codeec specification
of an action is actually its pre-condition that requires certain
actions to be visible in order to make progress. Consequently,
checking if the specification is valid at run-time is equivalent to
checking if known set has required actions.

As an example, consider the causal visibility specification (cau) over
an action $$a$$:

{% highlight Scheme %}
    (define-fun cau ((a Action)) Bool (forall ((c Action) (b action)) 
      (=> (and (vis c b) (vis b a)) (vis c a))))
{% endhighlight %}


Consider the scenario shown in the figure below (green lines indicate
visibility):

![CausalVis]({{ site.baseurl }}/assets/cau-1.jpg)

Since the action Q is visible to R and R is visible to P. However, Q
is also visible to P. Therefore, all actions that P needs to be _know_
are already _known_. Hence the spec is valid, as demonstrated by the
following z3 encoding:
[http://rise4fun.com/Z3/ZDLg](http://rise4fun.com/Z3/ZDLg).

Now consider the following scenario:

![CausalVis]({{ site.baseurl }}/assets/cau-2.jpg)

Known set of the current action (P) is {P,Q,R,S}.  The action T, which
can be reached from the current action (P) via causal visibility
edges, is not yet visible (i.e., _known_) to the current action.
Therefore, causal visibility spec fails in this setting. A
straightforward way to satisfy the spec is for the implementation to
stall the execution of P till T becomes visible.  This approach works
as T is eventually bound to become visible to the current action (P).
However, this approach requires waiting for arbitrary amounts of time.
An alternative is the _ignorance is bliss_ policy described in
previous writeup. Basically, we try to find if there is a subset of
known actions (referred to as the _sub-known_ set) which satisfy the
spec. In other words, we try to find a model for the sub-known set
such that it includes the current action and is closed under causal
visibility relation. The Z3 encoding of this question for current
scenario is here:
[http://rise4fun.com/Z3/CWKw](http://rise4fun.com/Z3/CWKw).

Z3 produces a singleton set containing the current action as model for
sub-known set. This is not surprising as such a set is the smallest
sub-set of known set that is closed under causal visibility relation.
However, we are interested in not the smallest, but the largest
sub-set of known set that is closed under causal visibility. This is
because we would like to make available to current action as many
actions as possible. 

In order to produce a largest sub-known set, we follow an iterative
refinement procedure, where we ask Z3 for a larger sub-known set in
each iteration. We start by asking Z3 to produce a set that contains
atleast one element more than what the current sub-known contains:
[http://rise4fun.com/Z3/8KYv](http://rise4fun.com/Z3/8KYv).

<!-- http://rise4fun.com/Z3/WD2E -->


[is-ctxt-ready]: http://multimlton.cs.purdue.edu/mML/Notes/research/notes/2014/05/03/isContextReady.html
