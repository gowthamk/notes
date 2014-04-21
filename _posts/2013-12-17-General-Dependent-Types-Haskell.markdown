---
layout: post
title:  "General Framework for Dependent Types in Haskell"
---

## Introduction ##

This writeup is only meant to put some observations made in previous
writeup in appropriate context, lest they might be lost. It also tries
to reason why it might be worthwhile to explore them further in
future.

## General framework for creating indexed types in Haskell ##

Dependent types for practical programming have been proposed in
various formats by various authors. [Hughes et. al., 1996] proposed
sized types, where data types, such as lists, trees etc., are indexed
by natural numbers that denote their sizes. Cayenne [Augustsson, 1998]
is perhaps the first language that extended a mainstream programming
language (Haskell) with full dependent types, i.e., any language
expression is eligible to be a type. The price that it pays for
providing full dependent types is the decidability of type checking.
Dependent ML (Xi and Pfenning, 1998) extended ML with indexed types,
where type index objects can be drawn from any constraint domain. Type
checking in DML is decidable, modulo decidability of the constraint
domain. Dependent ML is more a language scheme than a language, as it
generates languages with different type systems for different
instantiations of constraint domain. Hybrid types (Flanagan et. al.,
2006) is another full dependent type system with undecidable type
checking, but undecidable type equivalences are cast as run-time
checks, providing _dynamic type checking_. Liquid types [Rondon et.
al., 2008, Kawaguchi et. al., 2009] is a dependent type system for
Ocaml, which relies on predicate abstraction over finite set of
logical predicates, and SMT based decision procedures to infer
dependent types.

Evidently, aforementioned works can be classified as those proposing
full dependent type systems with undecidable type checking, and those
which propose indexed type systems retaining decidability of type
checking. Cayenne and Hybdid types fall into first category, whereas
DML and sized types into second. Liquid types is an outlier, which we
discuss towards the end. In full dependent type systems, there is
no clear distinction between expressions of term and type language.
In Cayenne, term and type language are one and the same. Terms with
appropriate types/kinds are eligible to become types as the following
demonstrates:

    printf :: (fmt :: string) -> PrintType fmt,
    where PrintType :: string -> *

In the above type, PrintType is a function from haskell strings to
haskell types (Int, Bool, Int -> Bool etc). It is written using
haskell expression language by case-matching over strings. Hybdrid
types, however, uses the following syntax for dependent types:

    {v : B | e }

where B is a base type (int, bool etc), and e, the type refinement, is
any boolean expression from the term language. Since term and type
languages mostly overlap in full dependent type systems, there are no
well-defined _entry points_ or _conditions for promotion_ from term
language to type language.

Indexed types, on the other hand, clearly separate term and type
language. DML, for instance, draws its type index objects from a
separate constraint domain which is neither accessible to, nor has
access to term language. Consequently, such indexed types are strictly
less powerful than full (or partial, as we explain later) dependent
types. For example, the following type, which is the first example of
dependent types in [Pierce, Advanced Types and PL, 2005] cannot be
typed in DML:

    tabulate :: Π(n:Nat).a -> Vec a n

The reason is that term level Nat and type-level Nat are kept separate
in DML. Nonetheless, due to the clear stratification of terms, types and
kinds as in mainstream programming languages, and also due to
decidability of type checking, indexed types remain attractive
approach to dependently typed programming. Recent efforts, such as
datatype promotion in Haskell (Weirich et. al., 2012), and kind
equalities in Haskell (Weirich et. al., 2013), have concentrated on
increasing expressivity of indexed types by promoting certain terms to
type level based on a well-defined criteria. Nevertheless, the
extended language still falls short of expressivitiy required to type
flagship examples of dependent types, similar to `tabulate`. 

One interesting thing to notice from term promotion efforts of haskell
is that, GHC does not differentiate between traditional types/kinds
and types/kinds resulting from promotion. Therefore, type checking can
be parametrized over promotion semantics, provided that promotion
semantics also include semantics of equivalences among expressions of
promoted types. Such a parametrized GHC can be instantiated with
different promotion semantics to get different indexed type systems.
The A-DP and R-DP interfaces from previous writeup are examples of
such instantiations. Since these interfaces clearly define promotion
semantics through type projections, they retain clear stratification
of terms, types and kinds, while increasing the expressivity of type
system. Therefore, such parametrized type system can be considered as
generalization of DML, whose type system is parametrized only over
constraint domain. This, I think, could be a significant step forward.

### A Note on Liquid Types ###

Liquid types uses syntax similar to hybdrid types for dependent types.
An observer, who is unfamiliar with internals of liquid types
engine, might not tell the difference between types inferred by the
engine and hybdrid type annotations for many functions. However,
liquid types is not a full dependent type system, as type refinements
cannot be arbitrary term-level boolean expressions. The language of
refinements is defined separately, but syntactic class of variables in
the language coincides with that of term language. This means that 1.
All variables of term language are also variables of type language,
and 2. There are no _phantom_ variables in the type language. In this
sense, liquid types might be considered equivalent to a type index
system, where type language and term language are kept separately, but
term-level variables are automatically promoted to singleton types.
That is, every variabe v::int, now has the type v:: int[v], where type
int is indexed by another type v. Therefore, it is possible to write
types such as

    tabulate : int[n] -> 'a[v] -> 'a[v] list[n]

However, it is possible to write liquid types that do not have
equivalents in indexed types (in their well-known form). For eg:

    max : {x:int} -> {y:int} -> {v:int | v≥x /\ v≥y}

Indexed types extended with constraints over type indexes might be
able to model liquid types. However, we classify liquid types as
_partial_ dependent type system.

