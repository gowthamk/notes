---
layout: post
title:  "Generalizing Catalyst"
--- 

1. Introduction
-------------

In this note, I describe some ways we can generalize Catalyst to
progress from shape analysis to general relational verification.

1.1 Relations Beyond Relational Abstractions
----------------------------------------

Catalyst's treatment of relations is strongly rooted in the approach
of encoding relations as _abstraction functions_ (like _measures_.
Details in Kuncak et al, Decision Procedures for Abstraction
Functions, POPL'10.). For example, the _occurs-before_
relation is defined as an abstraction function over a list:

    relation Rob(x::xs) = {(x)} X Rmem(xs)

The advantage of defining a _occurs-before_ as an abstraction
functions is that the resultant definition is simple enough to be
elaborated into type refinement of list constructor `Cons`:

    Cons : x -> xs -> {l | Rob(l) = {(x)} X Rmem(xs)}

Once elaborated into a type refinement, the type checking is no
different to any other dependent type system. 

Parametric relations (eg: `Rob[R]`) are somewhat different from simple
relations in that their definitions are not elaborated into type
refinements of constructors. Nevertheless, parametric relations are
also defined inductively over a single datatype, and they too should
be treated as abstraction functions computing relational abstractions
of data structures.

However, not all useful relations abstract a data structure. For
example, consider a parametric relation `Rpw[R]` that relates two
lists (`l1` and `l2`) if and only if elements in `l1` are point-wise
related to elements in `l2` via relation `R`. The relation `Rpw[R]`
needs to be defined inductively over a _pair_ of lists, instead of a
single list.  As such, it is not possible to elaborate the inductive
definition of `Rpw[R]` as a type refinement of list constructor
`Cons`. Moreover, `Rpw[R]` relates two lists, and therefore cannot be
treated as an abstraction of a list. 

The need for relations like `Rpw` often arises in practical
verification. An example (Matrix) is given below this introduction.
To promote Catalyst from shape analysis to more general relational
verification, there is a need to go beyond abstraction functions, and
treat a relation as a more general entity that can possibly relate two
or more data structures.

1.2 Arithmetic Extensions
-------------------------

On the other hand, relational domain itself is not enough for
all verification tasks. While verifying numerical algorithms, such as
K-Means, is an exercise in pure arithmetic, and therefore orthogonal
to relational verification, there exist many cases where we need to
combine arithmetic with relational domain for effective verification.
For example, to specify and verify `SSA-remove-unused` that _counts_
the number of uses, we will have to relate the count (a number) to
existence (a non-empty set) and non-existence (an empty set) of uses
of a variable.  Likewise, to verify array functions, we have to relate
the numerical order of array indices to relative ordering of elements
in the array.  Since unrestricted combination of theories with
quantification is undecidable, allowing a combination of arithmetic
with relations in specifications while retaining decidability of
verification is a challenging exercise. A possible solution is to
allow (in relational specifications) only the restricted subset of
arithmetic that can be abstracted as uninterpreted sorts and relations
at SMT solver level. Alternative approaches that involve separating
theory specific part of VC from pure relational VC may also be
possible. Given the ubiquity of arithmetic, interfacing relational
verification with conventional arithmetic verification should be a
worthwhile exercise.

1.3 Higher-level Abstractions in Specification Language
------------------------------------------------------

Currently, our specification language is nothing more than relational
algebra. In the paper, we have shown that we can encode the constructs
(eg: conditionals) required to write expressive specs only in terms of
relational expressions (For eg, as in the case of `filter` function
specification). However, notwithstanding the expressivity of
relational algebra, writing everything in terms of relational
expressions is unintuitive, and requires significant enterprise on
behalf of spec writer. To control the verbosity of specifications, and
to reduce the effort that goes into crafting a specification, it is
imperative that we extend spec language with higher-level abstractions
that can be compiled down to relational algebra. The `quicksort`
example given below demonstrates this point in greater detail.

 
2. Examples
------------

Here are a couple of examples that corroborate some of the proposals
made in previous section to extend Catalyst.

2.1 Matrix
---------

Consider the following definition fo `matrix` type:

    type 'a matrix = 'a list list

The type defines matrix as a list of rows. For instance, here is a 2 X 3
matrix :

    m23 = 
      [
        [1,2,3],
        [4,5,6]
      ]

Consider a transpose function over matrices:

    transpose: 'a matrix -> 'a matrix

`transpose` takes a M X N matrix and produces a N X M matrix.

Let us define two relations - _row-order_ (denoted `Rro`) and
_column-order_ (denoted `Rco`) over matrix. Two elements `x` and `y`
of matrix `m` are related by `Rro(m)` iff `x` and `y` occur in same row
and `x` occurs before y. Similarly, `x` and `y` are related by `Rco(m)`
iff `x` and `y` occur in same column, and `x` occurs before `y` in
that column.  Using these relations, we can specify `transpose` as:

    transpose: {m1 : 'a matrix} -> {m2 : 'a matrix | Rro(m1) = Rco(m2) 
                                                  /\ Rco(m1) = Rro(m2)};

Stated simply, the spec says that rows in `m1` become columns in `m2`,
and vice-versa.

Now that we have identified `Rro` and `Rco` as useful relational
abstractions of matrix, let us focus on their definitions. Defining
_row-order_ is easy - it is a straightforward combination of
_occurs-before_ relation of all row lists of a matrix. More precisely:

    Rro(m) = Rmem[Robs](m)

For the concrete matrix `m23` shown above, `Rmem(m23)` is the set
`{[1,2,3], [4,5,6]}`, and `Rmem[Robs](m23)` is the set obtained by
mapping each list in `Rmem(m23)` using `Robs`:

    Rmem[Robs](m23) = {(1,2),(1,3),(2,3),(4,5),(4,6),(5,6)}

But, how do we define _column-order_ (`Rco`)? `Robs(m23)` tells us
that row `[1,2,3]` occurs-before the row `[4,5,6]` in the matrix.
`Rco` is simply the point-wise interpretation of this occurs-before
relation. That is, 

    Rco(m23) = {(1,4),(2,5),(3,6)}

Unfortunately, we do not have a way to transform the relation
`{([1,2,3],[4,5,6)}` to the relation `{(1,4),(2,5),(3,6)}`. For a
matrix `m`, there is no way we can express `Rco(m)` as a composition
of parametric or non-parametric structural relations as we cannot
define a point-wise relation between two lists. This is because a
point-wise relation over two lists needs to be defined inductively
over two lists:

    Rpw(x::xs,y::ys) = {(x,y)} U Rpw(xs,ys)

And we simply do not have a way of defining the same in Catalyst.


2.2 QuickSort
-------------

ICFP reviewer 4 suggested quicksort as a benchmark for Catalyst. Here
is the ML type of quicksort function:

    quicksort : 'a list -> ('a -> 'a -> bool) -> 'a list

The higher-order argument is a comparator function that returns true
if and only if its first argument is less than or equal to its second
argument (comparision for `'a` domain).

To write a relational type for `quicksort`, we observe its invariant
in terms of order of elements in its input list and its output list.
Unlike `rev`, where every `x` that occurs before `y` in input list
occurs after `y` in result list, in case of `quicksort`, if `x` occurs
before `y` in input list, then `x` occurs after `y` in result list if
and only if `x` is greater than `y`. Whether `x` is greater than `y`
or not is determined by the comparator function; so, we can imagine
the comparator function as inducing certain order among its arguments.
If we denote that order with a relation `R`, then `R` is an
uninterpreted relation except for the semantics that for all `x` and
`y`, `R(x,y)=true` if and only if the comparator determines `x` to be
less than or equal to `y`. Using `R`, we can write the invariant of
quicksort informally as:

    quicksort : {l : 'a list} -> ({x:'a} -> {y:'a} -> {z:bool | R(x,y) = z})
                  -> {v : 'a list | Rmem(v) = Rmem(l) 
                                 /\ ∀(x,y)∈Robs(l), if R(x,y) = true 
                                                    then (x,y)∈Robs(v)
                                                    else (y,x)∈Robs(v)}

Let us materialize this type in Catalyst. Firstly, `R` is free in
above type; it needs be a relational param to `quicksort`:

    (R) quicksort : {l : 'a list} -> ({x:'a} -> {y:'a} -> {z:bool | R(x,y) = z})
                  -> {v : 'a list | Rmem(v) = Rmem(l) 
                                 /\ ∀(x,y)∈Robs(l), if R(x,y) = true 
                                                    then (x,y)∈Robs(v)
                                                    else (y,x)∈Robs(v)}

Second, all our relations are abstraction functions over a single
value; so `R(x,y) = z` (`z` is true/false) makes no sense in Catalyst.
However, this is not a show stopper as we can equivalently define `R`
as following:

    R(x) = set of all y such that y≥x

Note that this is our (programmer's) interpretation of `R`. Catalyst
does not need to know this definition as it treats `R` uninterpreted.
Using this formulation of `R`, we rewrite the type of `quicksort`:


    (R) quicksort : {l : 'a list} -> ({x:'a} -> {y:'a} 
                  -> {z:bool | z = true <=> y ∈ R(x)})
                  -> {v : 'a list | Rmem(v) = Rmem(l) 
                                 /\ ∀(x,y)∈Robs(l), if y ∈ R(x) 
                                                    then (x,y)∈Robs(v)
                                                    else (y,x)∈Robs(v)}

Next, we need to rewrite the type refinement of result in Catalyst
notation. Unfortunately, we don't have explicit universal
quantification in our spec language. However, observe that the
quantification is only over pairs in `Robs(l)`. In other words, we
want to access all pairs in the set `Robs(l)`. This can be done
through `bind` operator, which is also not part of our spec language,
but we nevertheless use it. We write:

    bind(Robs(l), λ(x,y).e)

Where the transformer expression `e` has to be `(x,y)` or `(y,x)`
depending on whether `y∈R(x)` or not. Since we don't have conditionals
in our spec language, we rely on set-minus to do equality test and
produce empty set when the equality holds, and non-empty set when it
doesn't.  Relying this behaviour, we can write express `e` in above
binds expression as:

    ({x} X e1)  U  (e2 X {x})

Where, `e1` has to be {y} when `y ∈ R(x)`, and ∅ otherwise. Conversely,
`e2` has to be {y} when `y \notin R(x)`, and ∅ otherwise. That is:

    e1 = {y} - ({y} - R(x))
    e2 = {y} - R(x)

Substituting the above definitions of `e1` and `e2` in the definition
of `e`, we have: 

    e = ({x} X ({y} - ({y} - R(x))))  U  (({y} - R(x)) X {x})

Substituting this definition as transformer expression in the bind
expression:

    bind(Robs(l), λ(x,y). ({x} X ({y} - ({y} - R(x))))  
                          U  (({y} - R(x)) X {x}))

Therefore, the type of quicksort is:

    (R) quicksort : {l : 'a list} -> ({x:'a} -> {y:'a} 
                  -> {z:bool | z = true <=> y ∈ R(x)})
                  -> {v : 'a list | Rmem(v) = Rmem(l) 
                         /\ Robs(v) = bind(Robs(l), λ(x,y). 
                                        ({x} X ({y} - ({y} - R(x))))  
                                          U  (({y} - R(x)) X {x}))


So, __we can indeed ascribe a very strong relational type to quicksort__,
given that we promote bind expressions to be used in specification
language. However, observe that while we were able to write the informal
relational type of quicksort fairly quickly, the process of deriving a
well-formed relational type is long and tedious. Ideally, writing spec
for a function has to be much simpler than implementing the function
itself. To this end, our spec language should offer constructs that
let spec writers think at higher level of abstraction:

1. Spec language shouldn't enforce _abstraction function_ view of
   relations, when such a view is not appropriate. In the above
   example, `R` stands for a EUFA relation (such as `≤`); so, Catalyst
   should allow it to be used accordingly. The switch from EUFA view
   to abstraction function view of `R`, and subsequent transformation
   of `z = R(x,y)` to `z=true <=> y ∈ R(x)` need to be done behind the
   screens automatically.
2. We want `bind` in spec language to express bounded quantification.
   So, instead of promoting `bind` to spec language, we should
   directly allow bounded quantification in spec language, and
   automatically compile quantified propositions to `bind` expressions
   in intermediate language.
3. Expressing conditionals in terms of set-minus and cross-products
   requires the spec writer to come up with a clever encoding.  This
   should not be the case. A conditional operator that can be compiled
   down to a relational expression needs to be introduced.


