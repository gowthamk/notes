---
layout: post
title:  "Simpler Semantics for Parametric Relations"
---

## Introduction ##
Our current semantics for parametric relations requires MSFOL extended
with polymorphic sorts and extensional equality axiom over
uninterpreted functions, leading to higher-order uninterpreted
functions. Since such an extension to MSFOL was not previously
attempted, we had to explain its semantics at the intuitive level.
Further, to prove the decidability of type-checking with parametric
relations, we have to prove that type refinements, after being
compiled to extended MSFOL, can be further translated in
semantics-preserving way to decidable fragment of MSFOL. 

In this writeup, I propose simpler and more intuitive semantics for
parametric relations that does not require any such extension. The
intuition is to define parametric relation as a _parametric extension
to its non-parametric counterpart_. For a fully instantiated
parametric relation, the semantics of how it extends its non-parametric
counterpart can be captured in MSFOL itself. Given that semantics of
non-parametric relations is already defined in MSFOL, we do not need
to provide any further explanation. Further, we can re-use the
decidability proof of type checking with non-parametric relations.

This interpretation requires a change in syntax of how parametric
relations are defined, to suit the view that they are an extension of
non-parametric relations. However, there is no change in the syntax of
how they are used; so, all our examples continue to be the same.
Moreover, our text and list-of-pairs example in the introduction are
more oriented towards this interpretation of parametric relations. The
only change required is in formalization section.


## Observation ##
I draw attention to the observation that for every
parametric relation that we defined in our examples, there exists a
non-parametric counterpart that would have served the purpose in
absence of polymorphism or higher-order. For instance, `Rmem R`
is a parametric extension of plain `Rmem`, `Rroot R1 R2` for a
`('a,'b) tree` extends non-parametric `Rroot`, and so on. Explaining
semantics of `Rmem R` as an extension to `Rmem` is easy: `Rmem R`
relates list `l` to `y`, if and only if `Rmem` relates `l` to `x`, and 
`R` relates `x` to `y`. Formally:

    (∀x,y. Rmem(l,x) ∧ R(x,y) ⇒ (Rmem R)(l,y)) ∧ 
    (∀y.∃x. (Rmem R)(l,y) ⇒ Rmem(l,x) ∧ R(x,y)

Similarly, for `Robs R`:

    (∀x1,x2,y1,y2. Robs(l,x1,x2) ∧ R(x1,y1) ∧ R(x2,y2) ⇒ (Robs R)(l,y1,y2)) ∧ 
    (∀y1,y2. ∃x1,x2. (Robs R)(l,y1,y2) ⇒ Robs(l,x1,x2) ∧ R(x1,y1) ∧ R(x2,y2)
    
Observe that above formulas completely capture the semantics of `Rmem R`
and `Robs R`, as we expect when we write their definition in current
syntax. For instance, we have the following defining equations for
`Rmem R` in our current syntax (after expanding the \* notation):

    (Rmem R)(x::xs) = R(x) U (Rmem R)(xs)
    (Rmem R)([]) = {()}

Treating `Rmem R`, as any other structural relation `F`, we have:

    F(x::xs) = R(x) U F(xs)
    F([]) = {()}

Compare it with equations for `Rmem`:

    Rmem (x::xs) = {(x)} U Rmem(xs)
    Rmem ([]) = {()}

By structural induction over the list, and comparing two definitions
we can convince ourselves that semantics of `F` can be captured in
terms of `Rmem` using the quantified formula given above.

We make use of this observation to define new syntax for parametric
relations.

## Syntax ##

Observe that `F` from previous example is defined by _mapping_ (unary)
tuples of `Rmem` using structural relation `R`, followed by folding
with union (recall _mapfold_, but we give it a better name after showing
that this is a well-known operation). Let us assume an operator γ that 
allows lifting non-parametric relations to parametric relations in similar 
way, i.e., by mapping tuples and folding with union. The type of such an 
operator would be:

     γ : ∀t1,t2. {t1} → (t1 :→ {t2}) → {t2}

where `t1,t2` are tuple-type variables, and `{t}` denotes set with tuples 
of type `t`. As a concrete example, let `Rmem : intlist :-> {int}`, and 
`Rrefl : int -> {int*int}`. Then, parametric relation `Rmem Rrefl` of type
`{intlist} :-> {int*int}`:

    (Rmem Rrefl)(l) = γ(Rmem(l),Rrefl)  

Thus, operator γ can be used to lift non-parametric definitions to parametric
definitions. 

To better understand semantics of operator γ, let us write a haskell type
equivalent to above type of γ:

     γ : ∀a,b. M a → (a → M b) → M b

where `M a` is the type of sets with tuple-type `a`. Observe, this is
the type of monadic bind operator, which is not very surprising as set
is a monad, and we express structural relations as sets. Similar to
monadic bind operation, γ _binds_ structural relations to define
parametric structural relations. Therefore, I propose that we consider
γ to be equivalent of bind operator for structural relations and
replace it with usual infix-bind syntax (`>>=`). For instance, to define
parametric `Rmem` relation, we can use the syntax:

    param-relation (Rmem R)(l) = Rmem(l) >>= R

I believe that anyone who understands the semantics of bind operator,
and knows that Rmem(l) is a set, could understand the meaning of above
syntax. A parametric relation defined using above syntax can be
compiled to an MSFOL formula that relates it to its non-parametric
counterpart, and captures its semantics completely.

As an aside, there also exists an equivalent of other essential
monadic operation, namely `return : ∀a. a → M a`, for structural
relations expressed as sets. It is the trivial `RId` relation, with
type `∀a. a → {a}`. 

## Type Checking ##
Type checking will remain same as previous. Only change is in
translation to logic, where, for every fully-instantiated parametric
relation, we add an MSFOL formula that relates it to its non-parametric
version, and subsequently relace terms like `Rmem R` with an
uninterpreted function `F`. I have experimentally verified this
approach with some examples, by manually adding such assertions to Z3
VCs.


