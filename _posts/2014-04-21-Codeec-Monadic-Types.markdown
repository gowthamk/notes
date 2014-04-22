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

Consider an integer register abstract datatype with encapsulated
state, offering two functions: 

{% highlight haskell %}
    read :: State Int Int
    write :: Int -> State unit Int
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
its old state. Similarly, the functional equivalent of type of `write`
is given below:

    write :: Int -> Int -> (unit * Int)

Function `write` takes an integer (x) and the current state (an
integer), and returns a new state (an integer equal to x).

A state monadic computation can be constructed by _binding_ `read`s and
`writes`, which represents a trace of actions. For example, following
haskell code:

{% highlight haskell %}
  do {
    
  }
{% endhighlight %}
