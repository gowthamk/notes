---
layout: post
title:  "Comparing Catalyst Type Inference to Popeye's"
--- 

Introduction
------------

In this document, I shall first outline the similarities, and
fundamental differences between the dependent type inference problem
solved by Popeye (He Zhu's PLDI'15 submission) to that being attempted
in Catalyst. Next, I will briefly discuss main ideas underlying
Popeye's type inference mechanism and their applicability in the
context of Catalyst's inference problem. The aim is to identify ideas,
techniques, or even parts of the implementation, that can be reused in
the context of Catalyst. <!-- Finally, I propose two distinct yet related
approaches to infer dependent types in presence of higher-order
functions and abstract relations in Catalyst -->.


Popeye vs Catalyst
------------------

Popeye and Catalyst are both verification frameworks, which manifest
as dependent type systems for ML-like languages. While effective
program verification is a shared high-level goal of both the
frameworks, they are nevertheless fundamentally different when it
comes to the problems they propose to solve. 

Popeye takes an ML program annotated with assertions, and aims to
verify that assertions are never violated at run-time. Verification
starts with backward symbolic analysis from the stated assertions and
concludes by by inferring dependent function types that are just
strong enough to prove the validity of stated assertions. For example, 
consider the following program: 

    fun f x = x + 1;
    fun main x = 
      let
        val _ = assert (x>4)
        val y = f x
        val _ = assert (y>5)
      in
        y
      end;

Backward symbolic analysis lets Popeye conjecture that the dependent
type of f is:

    f : x:int -> {v : int | x>4 && v>5}

The type is then verified against the definition of `f`. Note that
this type is sufficient to verify that both the `assert`s in the above
program are never violated at run-time.

The example demonstrates that dependent type of a function in Catalyst
depends not just on the function definition, but also the context in
which it is used. If a function is called in different contexts that
make different assertions, its dependent type is a conjunction of
dependent types inferred from each context. For example, if the
program is extended to use `f` in a context where the input is
guaranteed to be greater than 20 and output is required to be greater
than 21, the type of `f` will be strengthened to the following:

    f : x:int -> {v : int | (x>4 && v>5) || (x>20 && v>21)}

Observe that adding more context strengthens the type by adding more
special cases to the type, but the type itself never generalizes to
something like the following dependent type which captures the
semantics of `f`:  

    f : x:int -> {v : int | v>x}

<!-- Context sensitivity comes at the price of compositionality in Popeye,
for the backward symbolic analysis need to analyze the function
multiple times, once for each calling context. -->

The current version of Catalyst (henceforth called Catalyst V1) takes
an ML program with recursive functions annotated with their relational
dependent types, and simply type checks the program as per standard
dependent typing rules. Catalyst derives its power from the
expressivity of the language of its type refinements, which is capable
of expressing semantics of higher-order functions operating over
recursive data structures. Like Popeye, catalyst can also verify
programs against assertions, but the assertions themselves need to be
dependent type specifications. For example, to assert that the
following program does indeed reverse a list:

    fun rev l = foldl l [] (fn (x,xs') => x::xs')

one simply writes its dependent type specification as:

    rev :: l -> {v | Robs(v) = Robs(l)}

Likewise, to assert that the following program preserves elements in
its input list:

    fun sort l = foldl l [] (fn (x,xs') => insert x xs')

one annotates `sort` with the following dependent type
specification:

    sort :: l -> {v | Rmem(v) = Rmem(l)}

In both the cases, successful typechecking verifies the assertion
encoded in the dependent type of the program. Observe that both
programs make use of the higher-order function `foldl`. For the
verification to work seamlessly, it is imperative that `foldl` has a
sufficiently strong type that lets us derive required invariants in
both the cases. How does one construct such a type for `foldl`?

It is here that Catalyst's approach differs significantly from that of
Popeye. While Popeye's approach would infer types for `foldl`
using backward symbolic analysis from both the contexts, followed by
coalescing the inferred types, Catalyst advocates generalizing the
type such that it captures the semantics of `foldl` as precisely as
possible. Catalyst's type for `foldl`should  _make sense_ regardless
of the context in which it is used. The type inference mechanism for
Catalyst is therefore not _obligated_ to take into account the
assertions made in different calling contexts of `foldl`, although it
may choose to do so for engineering reasons. In theory, the type
inference algorithm can simply analyze the definition of `foldl` to
infer a relational dependent type that models the semantics of
`foldl` as closely as possible. This formulation of type inference
problem in Catalyst decouples it from the program verification
problem, and makes it useful for other purposes, such as computing
abstract representations of functions to be used in searching code
bases.

Aspects of Popeye's Type Inference Relevant to Catalyst
-------------------------------------------------------

The main idea behind Popeye's type inference is to collect good
samples (i.e., test cases that do not trigger assertion violations)
and bad samples (i.e., those that do) of a function's I/O behaviour
and use a machine learning algorithm to infer a classifier that
separates good samples from bad ones. The expectation is that the
classifier thus inferred is the most likely invariant of the function.
While good samples are obtained from the test cases, which are either
manually provided or randomly generated, bad samples are obtained in
two ways: firstly, they are generated by soving the negation of
constraints generated by the WP analysis. Secondly, they are also
obtained from test cases that lead to assertion violations.

Generating Random Lists
------------------------

The current prototype implementation of Catalyst's  ([CEGIS-based type
inference](https://www.cs.purdue.edu/sss/projects/catalyst/2014/11/15/Catalyst-Type-Inference.html))
can benefit from positive samples to reduce the state space of
candidate hypotheses (solutions) by pruning away the hypotheses that
do not explain a positive sample. For example, for the `concat`
function:
    
    fun concat [] ys = ys
      | concat x::xs ys = x::(concat xs ys)

with the following dependent type template:

    concat : xs -> ys -> {v | ??}

The candidate state space for the predicate of form `Robs(v) = ??`
filling the hole is the following:

    Robs2(l) = (Rob3(l2) U (Rob3(l1) U (Robs2(l2) U (Robs2(l1) U 
               ((Rhd3(l2) X Rhd3(l2)) U ((Rhd3(l2) X Rhd3(l1)) U 
               ((Rhd3(l1) X Rhd3(l2)) U ((Rhd3(l1) X Rhd3(l1)) U 
               ((Rhd3(l2) X Rmem2(l2)) U ((Rhd3(l2) X Rmem2(l1)) U 
               ((Rhd3(l1) X Rmem2(l2)) U ((Rhd3(l1) X Rmem2(l1)) U 
               ((Rmem2(l2) X Rhd3(l2)) U ((Rmem2(l2) X Rhd3(l1)) U 
               ((Rmem2(l1) X Rhd3(l2)) U ((Rmem2(l1) X Rhd3(l1)) U 
               ((Rmem2(l2) X Rmem2(l2)) U ((Rmem2(l2) X Rmem2(l1)) U 
               ((Rmem2(l1) X Rmem2(l2)) U (Rmem2(l1) X Rmem2(l1))))))))))))))))))))))

Positive examples involving lists of length 1 and 2 will weed out the
majority of the candidate state space leaving only:

    Robs2(l) = Robs2(l2) U Robs2(l1) U Rmem2(l1) X Rmem2(l2)

Which, fortuitously, happens to be the final solution (this will be
confirmed by the verifier).

How do we obtain positive samples for `concat`? Programmer provided
test cases are indeed helpful, but requiring programmer to write unit
tests for a function as simple as `concat` is not reasonable.
Furthermore, since there are no particular restrictions on the
properties of input lists to `concat`, a random list generator would
serve well as the source of positive samples. How do we construct such
a list generator? 

We turn to Popeye for the answer to this question. Unfortunately,
Popeye does not have a random generator for recursive data types,
which can automatically generate lists and trees of arbitrary sizes.
Consequently, Popeye cannot automatically verify the validity of
assertion in the following user program:

    fun concat [] ys = ys
      | concat x::xs ys = x::(concat xs ys)
    fun main l1 l2 = 
      let
        val l = concat l1 l2
        val _ = assert (length(l) = length(l1) + length(l2))
      in
        l
      end

Alternatively, if we view the above program as a test case for
`concat` that operates on two integer lists of arbitrary lengths,
then the program can be rewritten as following:

    fun concat [] ys = ys
      | concat x::xs ys = x::(concat xs ys)
    fun makeList n = if n<=0 then [] 
      else (randomInt())::(makeList n-1)
    fun main n1 n2 = 
      let
        val l1 = makeList n1
        val l2 = makeList n2
        val l = concat l1 l2
        val _ = assert (length(l) = length(l1) + length(l2))
      in
        l
      end

This program now operates on two integers, which represent the lengths
of two lists, instead of lists themselves. Since random generators for
integers are readily available, test cases can be generated
straightforwardly.  Popeye relies on this intuition to verify some
data structure benchmarks.

The intuition can also be applied in the case of Catalyst to generate
arbitrary lists and trees. To start with, we can expect the programmer
to provide a function for every recursive datatype that maps integers
to objects of that datatype. The function `makeList` above is the
example of such a function for the list domain. For the binary tree
datatype, the function could be the following:

    fun mkTree n = if n<=0 then Empty
      else Node (mkTree n-1, randomInt(), mkTree n-1)

Given the simple structure of these function, we can synthesize the
generator functions, going forward. This solves the problem of
generating positive samples for data structure functions for now.

Tests for Higher-Order Functions
--------------------------------

Popeye does not have a sample generator for higher-order functions. It
requires that programs instantiate higher-order arguments
appropriately in order to generate a type for higher-order function
that is relevant to that program. For example, _in the context of_ the
program shown in Fig. 3 of the PLDI submission, the type inferred by
Popeye for the higher-order function `init` is:

    init : i:int -> n:int -> 
           a : ({a0 : int | a0>=0 && a0<n} 
                -> {ar : int | (a0<i && ar=1) || (a0>=i && ar!=1)}) ->
           f : ({f0 : int | f0>=0 && f0<n} -> {fr: int | fr=1})

If we take a closer look at how Popeye generates the above type, we
observe that the pre-condition of `init`'s higher-order argument (`a`)
is derived from an `assert` inside the function that was actually used
to instantiate `a` in `main`. Likewise, its post-condition is derived
from an assertion in `main`, which is the only calling context of
`init` in the program. In contrast, if `init` was considered in
isolation (i.e., in the absence of any calling context), `init` would
have been assigned a trivial type. To summarize, types for
higher-order arguments of a higher-order function in Popeye are
derived from the calling contexts of the function.

Catalyst also has to infer types for higher-order functions, such as
`map`, `foldl` and `foldr`. However, unlike Popeye, Catalyst does not
have the privelege of operating on a whole-program that provides
contexts for all higher-order functions. Catalyst's types for `map`,
`foldl` and `foldr` have to capture their respective semantics, and
should be general enough to be useful in many different calling
contexts. The generality is achieved via relational parameters and
parametric relations, and inferring such rich types is quite
challenging. For example, consider the dependent type of `map`
function in Catalyst that can be used in multiple different contexts:

    ('R1,'R2) map : xs:'a list 
                -> f:(x:'a -> {y:'a | 'R2(y) = 'R1(x)})
                -> {ys:'a list | Robs[R2](ys) = Robs[R1](xs)}

The dependent type has two relational parameters (`R1` & `R2`), and
makes use of two instances of the parameteric _occurs-before_
relation, which are instantiated with `R1` and `R2` respectively. To
infer the above rich type from the following simple template:

    map : xs:'a list -> f:(x:'a -> {y:'a | ??}) -> {ys:'a list | ??}

involves conceiving the two relational parameters, instantiating
appropriate concrete relations (i.e., `Robs`) and subsequently stating
the invariant in terms of the instantiated relations. Understandably,
this is a tough problem to solve.

Nevertheless, the obligation to infer general (i.e., context
independent) types, like that of `map` function, does not prevent
Catalyst from making use of programmer-provided _sample usecases_ to
_guide_ it towards synthesizing such general types. For example,
following is one sample usecase of the higher-order `map` function
over lists:

    fun main (l:'a pair list) : 'a list = 
      let
        val fst = fn (x,y) => x
      in
        map l fst
      end

following is another usecase:

    fun main (l:'a pair list) : 'a pair list = 
      let
        val inv = fn (x,y) => (y,x)
      in
        map l inv
      end

It is (relatively) easy to infer following (weaker) type for `map`
function with help of the first use-case:

    map : xs: 'a pair list 
          -> f:(x:'a pair -> {y:'a | RId(y) = Rfst(x)})
                -> {ys:'a list | Robs[RId](ys) = Robs[Rfst](xs)}

Likewise, following type can be inferred from the second usecase:

    map : xs: 'a pair list 
          -> f:(x:'a pair -> {y:'a pair | Rsnd(y) = Rfst(x)})
                -> {ys:'a pair list | Robs[Rsnd](ys) = Robs[Rfst](xs)}

Observing that the relations `Rfst` and `Rsnd` are for the `'a pair`
domain, which is not part of `map`'s polymorphic ML type, we
generalize them with help of relational parameters and hypothesize
that the resulant type is indeed the type of `map`. This hypothesis is
verified by the dependent type checker, confirming its validity.

The example demonstrates that user-provided samples of higher-order
arugments are quite helpful in guiding the inference algorithm towards
relationally parametric rich types for higher-order arguments.
However, the higher-order argument samples have to be carefully chose
only from the class of structural transformations in order for the
inference to be effective. Samples that perform domain specific
operations (such as additions, subtractions) that cannot be captured
via structural relations, are ineffective in guiding the inference
process. Nevertheless, I believe that this approach of relying on
user-provided samples is a promising one, atleas in the short term.

