---
layout: post
title:  "Third Homomorphism Theorem and Divide-and-Conquer Parallelism"
--- 

Introduction and Motivation
===========================
A function _h_ over lists is $$\odot$$-homomorphic 
iff, for all lists x and y,

    h (x ++ y) = h x ⊙ h y

where, $$\odot$$ is a (necessarily) associative on the range of h,
because `++` is associative. Examples of list homomorphisms are given
below:

    sum (x ++ y) = sum (x) + sum (y)
    sort (x ++ y) = merge (sort x, sort y)

Homomorphisms are particularly interesting as they are highly amenable
for divide-and-conquer data-parallel execution. Given implementations
of a function over lists in terms of `foldl` and `foldr`, Third
homomorphism theorem effectively says that there exists a homomorphism
that computes the same function. However, the theorem says nothing of
how to construct the homomorphism. The problem of deriving
homomorphisms and, subsequently, efficient parallel implementations from
sequential implementations of a function has been well-studied [3,4,5,6,7].
Such approaches take as input a pair of sequential implementations of
the function, in terms of `foldl` and `foldr`, respectively, and
derive the binary function ($$\odot$$) required to construct the
homomorphism.  The distinguishing feature of each approach is the
methodology employed to derive $$\odot$$ from `foldl` and `foldr` (eg:
generalization, tupling, fusion, weak right inverse calclulation
etc.).

Although such approaches were proven to be effective in deriving
parallel implementations [4], they cannot be used directly in a
general-purpose compiler to transparently derive parallel
implementations from user-provided sequential implementations. This is
because it is unusual for programmers to provide two sequential
implementations, one with `foldl` and another with `foldr`, for the
same problem, unless parallel execution is one of their explicit
goals. Moreover, only the most trivial of catamorphisms (eg: sum, max
etc), are evidently homomorphisms (i.e., their `foldl` and `foldr`
implementations are the same). Most catamorphisms of interest are
functions that are _not quite homomorphisms_, or _almost
homomorphisms_ [7], for which `foldl` and `foldr` implementations
differ significantly. For such catamorphisms, constructing the dual
definition (i.e, `foldl` for `foldr`, and vice-versa) requires
significant extra effort from programmers. For example, consider the
maximum prefix sum (mps) problem, which asks to find the prefix of a
non-empty integer list with maximum sum. Using `foldr`, `mps` can be
calculated as:

    fun mps l = foldr l 0 (fn (x,suffixMps) => max (x, x+suffixMps))
    (*
     * Simple representation:
     * mps (x::xs) = max (x, x+mps(xs))
     *)

To implement it using `foldl` requires an auxiliary definition of
prefix sum:

    fun mps l = 
      let
        val (v,_)  = foldl l (0,0) 
          (fn (x,(prefixMps, prefixSum)) => 
            (max (prefixMps, x+prefixSum), x+prefixSum)) 
      in
        v
      end 
    (*
     * mps (xs ++ [x]) = max (mps(xs), x+sum(xs))
     *)

The example makes it clear that conceiving leftwards (`foldr`) and
rightwards (`foldl`) functions to solve a problem requires significant
effort from programmers. Infact, it might event be easier to directly
write the divide-and-conquer implementation of `mps`:

    mps (x ++ y) = max (mps (x), sum (x) + mps(y))

Which is amenable for parallelization. 

Having made these observations, it is therefore interesting to
consider the following question:

    Given an implementation of a list function in terms of foldl
    (alternatively, foldr), is it possible to derive an equivalent
    foldr (alternatively, foldl) implementation automatically? What
    properties should the function need to satisfy in order for this
    to be possible?

It is perhaps better to first answer decision problem variant of the
above question:

    Given leftwards and rightwards implementations of a list function,
    is it possible to automatically determine whether implementations
    are equivalent?

At this point, it is worth noting that with help of our relational
type system, we can already answer such questions for certain
straightforward functions. For example, we can prove that `foldl`, and
`foldr` implementations of `exists` function are equivalent, in the
sense that one returns true if and only if other returns true.
We can also answer similar question for list `filter` function, 
with help of following arguments:

+ First, recall that relational type of filter is the following:
  
      (R1) filter : l -> (x -> {v | ([v=true] => (R1(x) = {()}))
                                 /\ ([v=false] => (R1(x) = {(x)})) }) 
        -> {v | (Rmem RId)(v) = (Rmem R1)(l) 
             /\ (Robs RId)(v) = (Robs R1)(l)};

+ let l1 and l2 be result lists of applying two implementations of
  `filter` to a list l. Note that, although both implementations
  differ in the way the list is traversed, filtering predicate in both
  cases should be the same in order for the implementations to be
  equivalent. That is, if one implementation filters positive integers
  from the input list of itegers, the other should do the same.
  Consequently, their relational types are same as shown above.
+ From the type of filter, we know that (Rmem RId)(l1) = (Rmem R)(l2) =
  (Rmem R1)(l); so, the set of elements in both lists is the same.
+ Next, we observe that (Robs RId)(l1) = (Robs RId)(l2) = (Robs
  R1)(l); Therefore, the order in which the elements appear in both
  lists is also the same. 
+ We conclude that both lists are extensionally equal. Therefore, both
  implementations of `filter` are equivalent.

Note that left and right folding implementations of `filter` have to
use different folding functions in-order to generate equal lists. This
observation will be used later in this writeup.

In order to extend relational approach to determine equivalences of
non-trivial examples, such as Maximum Prefix Sum, the approach needs
to be extended with ability to reason about arithmetic functions
abstractly. To make sense of this statement, consider the `foldl`, and
`foldr` implementations of `sum`, that compute sum of all elments in
an integer list:

    fun sumL l = foldr l 0 (fn (x,acc) => x+acc)
    fun sumR l = foldl l 0 (fn (x,acc) => x+acc)

In order to prove that both implementations are equivalent, we proceed
in the following way:

+ First we define an abstract relation `Rsum` of sort $$Int
  :\rightarrow \{\{ Int \}\}$$. Note that the co-domain is a set of
  sets of integers.  Intuitively, for an integer x, Rsum(x) is the set
  of all sets of integers, whose sum is x. Consequenly, we have
  following properties, which we add as axioms to the system:

    1. forall x : Int, {(x)} $$\in$$ Rsum(x)
    2. forall x1,x2 : Int, x1 = x2 $$\Rightarrow$$ Rsum(x1) = Rsum(x2)
    3. forall x1,x2 : Int, Rsum(x1) $$\cap$$ Rsum(x2) $$\neq$$ $$\emptyset$$
      $$\Rightarrow$$ x1 = x2

  The above axioms subsume associativity, and commutativity properties
  of addition. Note that we can abstract Int to an uninterpreted sort
  (A). We retained Int for clarity.
+ Next, we assign following type to the primitive addition operation:

      op+ : x:Int -> y:Int -> {v: Int | Rsum(x) U Rsum(y) ∈ Rsum(v)}

+ Recall that we have following type for fold:
    
      (R1,R2) foldl : l -> b -> (y -> acc 
              -> {v| R2(v) = R1(y) U R2(acc)}
              -> {v | R2(v) = Rmem[R1](l) U R2(b)}

    The type can be generalized to following:

       (R1,R2) foldl : l -> b -> (y -> acc 
               -> {v| R2(v) ⊙ R1(y) U R2(acc)}
               -> {v | R2(v) ⊙ Rmem[R1](l) U R2(b)}

    where $$\odot \in \{\subseteq, \supseteq, \in, \ni \}$$. 

+ Now, if we instantiate both R1 and R2 with Rsum, we get the
  following types for sumL and sumR:

        sumL : l -> {v1 : Int | Rsum(v1) = Rmem[Rsum](l) U Rsum(0)}
        sumR : l -> {v2 : Int | Rsum(v2) = Rmem[Rsum](l) U Rsum(0)}

    Therefore, for any l, Rsum(v1) = Rsum(v2). From axiom (3) above,
    it follows that v1 = v2. Hence, for any integer list l, sumL l =
    sumR l; Hence, both implementations are equivalent.

The sum example shows the direction in which we can proceed to scale
to non-trivial examples, such as Maximum Segment Sum. Indeed, more
work needs to be done to integrate complete linear arithmetic.

Context
=========

A point to note, when considering previous works based on third
homomorphism theorem, is that none of them consider the automatic
parallelization problem in the context of the program itself, rather
than a single function. Having the information from context may
sometimes let us reduce the problem to that of deriving a contextually
equivalent implementation of the dual catamorphism. For example,
recall that the `filter` function can be implemented as either using
`foldl` or `foldr`. As noted previously, the folding function in both
cases need to be different in order to generate equal list:

    fun filterL l f = foldr l [] (fn (x,acc) => if f x 
                          then acc else x::acc)
    fun filterR l f = foldl l [] (fn (x,acc) => if f x 
                          then acc else acc ++ [x])

However, if we consider the use of `filter` in the following program,
which defines a function that returns the sum of all +ve integers in a
list:

    fun positiveSum l = foldr (filter l (fn x => x<0)) 0 op+

It can be noted that naively replacing `foldr` with `foldl` (or
vice-versa) in the implementation of `filter` will not make any
difference to the result of `positiveSum`. Therefore, constructing an
equivalent sequential implementation, given one implementation of
`filter` is trivial. 

The example suggests that it is more productive to consider relaxed
versions of the questions that were asked before; Instead of
absolute equivalence, we now consider contextual equivalence:

+ Given an implementation of a list function in terms of foldl
  (alternatively, foldr), is it possible to derive a contextually
  equivalent foldr (alternatively, foldl) implementation
  automatically? What properties should the function need to satisfy
  in order for this to be possible?
+ Given leftwards and rightwards implementations of a list function,
  is it possible to automatically determine whether implementations
  are contextually equivalent?

Related Work and Relevance of the Problem
===========================================

Before we proceed further, an important question that needs to be
answered is whether the questions that were considered above are
relevant in the context of automatic parallelization or not. If we
only consider previous approaches that rely on third homomorphism
theorem for automatic parallelization, the exercise definitely seems
worthy, as I noted in first two paragraphs. To the best of my
knowledge, even the recent among works [3,4] that are based on third
homomorphism theorem require leftwards and rightwards implementations
of a function in order to derive its homomorphism. On the other hand,
there exist alternative approaches [1,2] to automatic parallelization
of recursive functions on lists and trees, which rely on algebraic
properties (of list functions in Bird-Meertens formalism) to formally
derive efficient parallel implementations from sequential
implementations.  Unlike the approaches based on third homomorphism
theorem, they do not require two equivalent sequential
implementations; they directly manipulate recursive definition of a
function, while being able to deal with multiple recursion patterns -
self recursion, mutual-recursion, and accumulation. At this point of
time, the limitations of this second approach are not very clear. I
have also not found a comparision of both approaches in terms of their
applicability. In summary, it is not clear whether solving the problem
of deriving contextually equivalent `foldr` definition from `foldl`
definition so as to apply third homomorphism theorem based approaches,
would be practically relevant to the larger problem of automatically
parallelizing functional programs.

Bibliography
=================

1. Morihata, and Matsuzaki, Automatic Parallelization of Recursive
   Functions Using Quantiﬁer Elimination, FLOPS 2010 
2. Zhenjiang Hu et al., Formal Derivation of Efficient Parallel
   Programs, TOPLAS'97.  
3. Chi, and Mu, Constructing list homomorphisms from proofs, APLAS'11
4. Morita et al., Automatic Inversion Generates Divide-and-Conquer
   Parallel Programs, PLDI'07.
5. Gorlatch, Systematic Extraction and Implementation of
   Divide-and-Conquer Parallelism, 1996.
6. Geser, and Gorlatch, Parallelizing Functional Programs by
   Generalization, JFP'97.
7. Murray Cole, Parallel Programming, List Homomorphisms and the
   Maximum Segment Sum Problem, 1993.
8. J Gibbons, The Third Homomorphism Theorem, JFP'95.


