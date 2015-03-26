---
layout: post
title:  "Alternative Approach to Type Inference"
--- 

Possible Approaches for Type Synthesis
-------------------------------------

Consider concat function:

    fun concat l1 l2 = case l1 of
        [] => l2
      | x::xs => 
        let
          val l' = concat xs l2
          val l = x::l'
        in
          l
        end

Let φ be the formula describing the membership relation of `l` (i.e.,
its LHS is `Rmem(l)`). Type inference has to analyze `concat` and
infer the type refinement φ. Assume that we restrict the grammar of
type refinements to the following:

$$
  \begin{array}{lcl}
  R & \in & Structural\; Relations,\; Primitive\; Relations\\
    &     & Relational\; Parameters\\
  v & \in & Variables\; in\; scope\\
  \rho & ::= & \rho[\rho] \;|\; R \\
  Ratom & ::= & \rho(v) \;|\; \rho(v) \times Ratom\\
  Rexpr & ::= & Ratom \;|\; Ratom \cup Rexpr \\
  \varphi & ::= & Ratom = Rexpr \;|\; \phi \wedge \phi\\
  \end{array}
$$

Observe that the grammar of type refinements does not contain base
predicates, but does contains parametric structural relations, which
can be instantiated with other structural relations, relational
parameters, or primitive relations. Previously, our grammar for
primitive relations is quite restricted. We now enrich the grammar of
primitive relation definitions to make up for the loss of base
predicates:

$$
  \begin{array}{lcl}
    PRdef & ::= & \lambda x.\,PRdef \;|\; PRexp \\
    PRexp & ::= & IF\; \pi\; THEN\; PRexp\; ELSE\; PRexp \;|\; Rexp\\
    \pi & ::= & x=x \;|\; \neg \varphi\\
  \end{array}
$$

An important consequence of this restriction is as following. Assume
that under the path condition $$\phi$$, we came to know that
`Rsv[RId](v) = Rsx[RId](x)`, where `v` is the return variable. Because
of the lack of base predicates, the only way we can capture path
condition is via the `IF-THEN-ELSE` inside the primitive relation
syntax. Therefore, there must exist some structural relation `Rsy`,
some variable `y`, and a predicate `pi` such that `Rsy[\k.IF pi THEN
Rsx[RId](x) ELSE {}]` is well-formed, and `ϕ ⊢ Rsy[\k.IF pi THEN
Rsx[RId](x) ELSE {}] <=> Rsx[RId](x)`. In such case, the constraint
that is well-formed under the same environment as φ is as follows: 
`Rsy[\k.IF pi THEN Rsx[R0](x) ELSE {}] ⊆ Rsv[RId](v)`, where `R0` is
an unknown primitive relation (to be inferred).

The intuition behind the above cryptic paragraph is explained below:
Let us say that set `S` captures some relational abstraction of the
result variable. Type inference problem involves defining `S` in terms
of relational abstractions of argument variables (and other variables
in the environment). Let us say that in some branch (under the path
condition ϕ), we came to know that set `S = s`, where `s` is a
relational abstraction (say, `Rsy`) of one of the argument variables
(say, `y`). That is, `s = Rsy[RId](y)`. This observation made along a
specific path generalizes to `s ⊆ S` if the following conditions hold:

1. The path is taken atleast once in every call of the function, and
2. No path removes elements from `S` resulting from a recursive call.

What if the first condition does not hold? Then, the generalization is
conditional to the path being taken: `ϕ => s ⊆ S`. But we don't have
base predicates of form `A => B` in our language. We need to express
`ϕ => s ⊆ S` as `s' ⊆ S`, where `ϕ => s'=s` and `~ϕ => s'={}`. Let `Γ`
and `Γ'` be type environments under which `S` and `ϕ` (its
A-denormalized form) need to be well-formed, respectively (i.e., `Γ ⊢
S` and `Γ'⊢ ϕ`). Then:

1. It must be the case that `Γ ⊆ Γ'`, and 
2. Variables in `Γ'-Γ` (i.e., dom(Γ'-Γ)) must be pattern variables
   that are introduced by unfolding a variable (call it `x`) of
   recursive type in `Γ`.  Therefore, we should be able to capture
   them in some parametric relational abstraction (`Rsx`) of `x`.
   Hence, `Rsx[λ(dom(Γ'-Γ)). IF ϕ THEN s ELSE {}](x)` is the `s'` we
   need.

Now, consider the case when 2nd condition does not hold. Then, the
generalization must be weakened to `s'' ⊆ S`, where `s'' ⊆ s`. But,
how do we define `s''`? Since we haven't analyzed other paths yet, we
don't know the exact nature of `s''`. We therefore define `s''` as
_some_ transformation of `s`. Recalling that `s = Rsy[RId](y)`, we
define `s''` as `s'' = Rsy[R0](y)`, where `R0` is an unknown
primitive relation which will be resolved upon analyzing other
branches in the function.  

Putting the above two cases together, the most general constraint is:
`Rsx[λ(dom(Γ'-Γ)). IF ϕ THEN Rsy[R0](y) ELSE {}](x) ⊆ S`

Analyzing Concat
----------------

Assume that we analyze the `[]` branch first.  We get the constraint
that `Rmem(l1) = {} ⊢ Rmem(l) = Rmem(l2) => φ`, which means that
whatever may be φ, it better be weaker than the proposition `Rmem(l) =
Rmem(l2)` when `Rmem(l1) = {}`. Since the branch condition `Rmem(l1)`
is well-formed under same env as `φ`, we have the constraint:
`Rmem[R0](l2) ⊆ Rmem(l) => φ`. 

Now, lets analyze the `x::xs` branch:

    | x::xs => 
        let
          val l' = concat xs l2
          val l = x::l'
        in
          l
        end

We know that `Rmem(l1) = {x} U Rmem(xs)`, and `Rmem(l) = {x} U
Rmem(l')`. The result list `l` must contain `Rmem[R1](l1)` or
`Rmem[R2](l2)` for some `R1` or  ...

Analyzing Concat - Approach 2
-----------------------------

Let us assume that `l1: 'a list[S1][S2][S3]` and `l2: 'a
list[S4][S5][S6]`, where the tree indexes denote `Rhd`, `Rmem`, and
`Robs` abstractions, respectively. Assume that we are analyzing the
`x::xs` branch. Let`'a[S]` denote the type of a variable whose `RId`
abstraction is `S`. We know that `x:'a[S1]` and `xs:'a
list[S7][S8][S9]`, where the following facts are known:

1. `S2 = S1 ∪ S8`
2. `S3 = (S1 × S8) ∪ S9`

Now, let `l' : 'a list[S10][S11][S12]`, and `l : 'a
list[S1][S14][S15]`. We know the following facts:

3. `S14 = S1 ∪ S11`
4. `S15 = (S1 × S11) ∪ S12`

Now, the aim is to express invariants over `S14` and `S15` in terms of
`S1-6`. Let the invariants be `φ1(S14,S1-6)` and `φ2(S15,S1-6)`,
respectively. Then, following facts are known (IHs):

5. `φ1(S11,S7-9,S4-6)`
6. `φ2(S12,S7-9,S4-6)`

Let us first concentrate on `φ1`. The problem is to infer suitable
formula `φ1(x0,x1,x2,x3,x4,x5,x6)`. Instead of trying to look at this
general problem in isolation, we concentrate on specific instances of
`φ1` that need to be valid. We know that `φ1(S14,S1-6)` needs to hold.
Is there a specific invariant that _could_ hold between `S14` and
`{S1-6}`? Let us take a look at the known fact on `S14`, which is `S14
= S1 ∪ S11`. Unfortunately, `S11 ∉ {S1-6}`. So, we need to eliminate
`S11` from the equation. We take to unification for this purpose. Note
that due to denormalization, we won't have equations of form `S11 =
...` or `S11 ⊆ ...`. We need to make use of equations which contain
`S11` in RHS. With such equations, we make use of a simple unification
strategy: Look for equations with the following structure `X = S1 ∪ Y`.
Then, unification generates following constraints: `Y⊙S11 ⊢ X⊙S14`,
where `⊙ ∈ {⊆,⊇,=}`. In the current case, we generate the constraint:
`S8⊙S11 ⊢ S2⊙S14`. The constraint means that in order to derive an
invariant on `S2` and `S14`, we need to prove the same invariant on
`S8` and `S11`. The context does not contain a known invariant on `S8`
and `S11`, but there is a possibility that `φ1(S11,S7-9,S4-6)` can
give us the required invariant. For it to happen,
`φ1(x0,x1,x2,x3,x4,x5,x6) => x2⊙x0` needs to hold for any `⊙ ∈
{⊆,⊇,=}`. Assuming this holds, we get `S8⊙S11` in our context. But if
that holds, known fact 5 means that `S2⊙S14` should also hold. This
holds trivially from the constraint `S8⊙S11 ⊢ S2⊙S14`. Hence, we have
`φ1(x0,x1,x2,x3,x4,x5,x6) => x2⊙x0`. 

We now validate this invariant in the `[]` branch. We have following
known facts:

7. `S1 = {}`
8. `S2 = {}`
9. `S3 = {}`
10. `S14 = S5`
11. `S15 = S6`

Does `S2⊙S14` hold for `⊙ ∈ {⊆,⊇,=}`? It holds only for `⊙ = ⊆`.
Hence, we have the constraint that `φ1(x0,x1,x2,x3,x4,x5,x6) =>
x2⊆x0`, and the invariant that `S2⊆S14`. Furthermore, the invariant
`S14⊙S5` holds, where `⊙ ∈ {⊆,⊇,=}`, giving us the constraint
`φ1(x0,x1,x2,x3,x4,x5,x6) => x0⊙x5`. Since, this constraint is not
validated in `x::xs` branch, we validate it now. Under the `x::xs`
branch, we note that only `S5⊆S14` holds, leaving the constraint
`φ1(x0,x1,x2,x3,x4,x5,x6) => x5⊆x0`. Hence, the final two constraints
are:

12. `φ1(x0,x1,x2,x3,x4,x5,x6) => x2⊆x0`
13. `φ1(x0,x1,x2,x3,x4,x5,x6) => x5⊆x0`

The strongest solution to φ1 (strongest because φ1 is a
post-condition) is `x0 = x2 ∪ x5`. 

Now, lets concentrate on `φ2`.  As a result of above analysis, we have
the following two additional facts in our context:

14. `S11 = S8 ∪ S5`
15. `S14 = S2 ∪ S5`

From facts 4 and 14, we have:

16. `S15 = (S1 × S8) ∪ (S1 × S5) ∪ S12`

As a known fact, we are are aware that `φ2(S15,S1-6)` has to hold. As
with `φ1` case, lets look for a specific invariant that _could_ hold
between `S15` and `{S1-6}`. Fact 16 is interesting in this regard.
Firstly, it lets us derive the following:

17. `S1 × S5 ⊆ S15`

The fact can be captured by the constraint:

18. `φ2(x0,x1,x2,x3,x4,x5,x6) => x1 × x5 ⊆ x0`

Since `φ2(S12,S7-9,S4-6)` has to hold, this means that following
should hold as well:

19. `S7 × S5 ⊆ S12`

Proposition 19 is not invalid. So, we can assume it to be valid. Fact
18 holds in the `[]` branch as well. The `[]` branch gives us another
constraint:

20. `φ2(x0,x1,x2,x3,x4,x5,x6) => x6 ⊆ x0`

Which is also valid in the `x::xs` branch. Finally, we can try to
eliminate `S8` and `S12` in 16 (as they do not belong to `{S1-6}`) to
derive more constraints. Unifying facts 16 and 2, we have: 

21. `S9⊆S12 ⊢ S3 ∪ (S1 × S5) ⊆ S15`.

We don't have a known invariant to prove `S9⊆S12`, but we can generate
such invariant if:

22. `φ2(x0,x1,x2,x3,x4,x5,x6) => x3⊆x0`. 

If we assume this, then we will have:

23. `S9⊆S12` 

in our context, but we now have the obligation to prove `S3⊆S15`. This
can be proved trivially from 17 & 18.

Hence, the final set of constraints are:

18. `φ2(x0,x1,x2,x3,x4,x5,x6) => x1 × x5 ⊆ x0`
20. `φ2(x0,x1,x2,x3,x4,x5,x6) => x6 ⊆ x0`
22. `φ2(x0,x1,x2,x3,x4,x5,x6) => x3⊆x0`. 

Unfortunately, the conjecture `φ2(x0,x1,x2,x3,x4,x5,x6) <=> x0 = x3 ∪
x6 ∪ (x1 × x5)` is invalid. Therefore, we will have to settle for the
following weaker version:

`φ2(x0,x1,x2,x3,x4,x5,x6) <=> x3 ∪ x6 ∪ (x1 × x5) ⊆ x0`


Learning
--------

The essential idea tried in the approach above is to imitate ML type
inference to infer Catalyst types. ML assigns symbols to unknown
types, and _unifies_ them to infer actual types. We wanted to see how
similar approach fares with Catalyst types. However, there is a
fundamental difference between the type inference problems in ML and
Catalyst. While in former, one only has to infer types, in the later
one has to infer the relationship between types. For example, when the
concat function is given the following template type:

    concat : 'a list -> 'b list -> 'c list

where `'a`, `'b`, and `'c` are unknowns, ML infers that `'b = 'a` and
`'c = 'a` to derive the following type for `concat`:

    concat : 'a list -> 'a list -> 'a list

Now lets consider the type of lists indexed by their membership sets
(a list GADT indexed by a a set). The type of concat with set-indexed
list type is:

    concat : 'a list[s1] -> 'a list[s2] -> 'a list[s1∪s2]

Observe that the set index of the result list is `s1∪s2`, which is a
type that has been constructed out of indexes of both the input lists.
But, this isn't new to ML. For example, consider the following
function:

    zip : 'a list -> 'b list -> 'a*'b list
    fun zip ([],[]) = []
      | zip (x::xs,y::ys) = (x,y)::(zip xs ys)

The type `'a*'b` has been constructed out of so-called indexes of both
the input lists. How did ML manage to do that? It used local
information to make a global decision. Let the type of result list of
concat be `'c list`. In the result expression, `(x,y)::(zip xs ys)`,
ML knows the type of `(x,y)` as `'a*'b`. The type of `cons` mandates
the type of the expression `zip xs ys` to `'a*'b list` producing the
constraint `'c = 'a*'b`. Finally, the result type of `cons` informs ML
that the result expression is of type `'a*'b list`, generating the
constraint `'c = 'a*'b`. The two constraints are simple equations,
which are equivalent. They can be solved to derive `'c = a'*'b`. 

Now, let us consider simple length-indexed list type with an append
function in Haskell:

    module LengthIndexedList where

      data Zero
      data Succ a

      type family Plus (a :: *) (b :: *) :: *
      type instance Plus Zero b = b
      type instance Plus (Succ a) b = Succ (Plus a b)

      data Vec :: * -> * -> * where
        VNil :: Vec a Zero
        VCons :: a -> Vec a n -> Vec a (Succ n)

      append v1 v2 = case v1 of
        VNil -> v2
        (VCons x xs) -> VCons x (append xs v2)

We would like GHC to infer the following type for append:

    append :: Vec a n1 -> Vec a n2 -> Vec a (Plus n1 n2)

GHC starts with the type `'a -> 'b -> 'c`. The first equation for
`append` generates following constraints: 

1.`'a ~ Vec a Zero`
2. `'c ~ 'b`.

The second equation generates following constraints:

3. `'a ~ Vec a (Succ n)`
4. `x :: a`
5. `xs :: Vec a n`
6. `'c ~ Vec a n1`
7. `'c ~ Vec a (Succ n1)`

Type inference fails because GHC cannot reconcile constraints (1,3),
and (6,7). For the similar example (involving empty/non-empty tagged
lists), we get the following error in OCaml:

   Error: This pattern matches values of type ('a, nonempty) vec
          but a pattern was expected which matches values of type
          ('a, empty) vec

The above constraints are generated assuming the absence of
polymorphic recursion. Let us assume that we have polymorphic
recursion. Also, let us say that by some shape analysis, we have
figured out that inputs and output of append are of type `Vec`. So, we
start with the following type for append:

    append : ∀(a1,a2,a3,n1,n2,n3). Vec a1 n1 -> Vec a2 n2 -> Vec a3 n3

Inside the `VNil` branch, we have following constraints:

1. Local constraint: `n1 ~ Zero`
2. `a3 ~ a2`
3. `n3 ~ n2`

Inside the `VCons` branch, we have following constraints:

4. Local constraint: `n1 ~ Succ n`
5. `x :: a1`
6. `xs :: Vec a1 n`

Assuming that we instantiate the bound type variables in append's type
with `b1,b2,b3,m1,m2,m3` respectively:

7. `b1 ~ a1`
8. `m1 ~ n`
9. `b2 ~ a2`
10. `m2 ~ n2`
11. `b3 ~ a1`
12. `n3 ~ Succ m3`

GHC's constraint solver cannot solve the above equations to derive a
solution. However, if we annotate the type of append using the
type-level function `Plus`, then we get few helpful equations:

13. `n3 = Plus n1 n2`
14. `m3 = Plus m1 m2`
15. `Plus Zero b = b`
16. `Plus (Succ a) b = Succ (Plus a b)`

Which would be enough to satisfy all constraints. 

The append example involves a type-level function `Plus`. Consider the
following zip example that involves nothing other than GADTs:

     zip :: Vec a n -> Vec b n -> Vec (a,b) n
     zip v1 v2 = case (v1,v2) of
       (VNil,VNil) -> VNil
       (VCons x xs, VCons y ys) -> VCons (x,y) (zip xs ys) 

GHC cannot infer a type for zip.

As the `append` example makes it clear, ML's type inference approach
of collecting constraints and solving them globally by unification is
not going to work for GADTs for the following reasons:

1. With GADTs, there are _local constraints_ like the constraint `n1 ~
   Zero` in the `VNil` branch. Local constraints collected from
   different branches may be incompatible, hence cannot be unified.
   This also means that types escaping from a branch may become
   _ambiguous_. For example, In the `VNil` branch of zip function, the
   return type can be `Vec a Zero` or `Vec a n1` or `Vec a n2`.
   Although they are equivalent in this branch, they are not
   equivalent outside this branch. So, it is not clear what the return
   type needs to be. Assuming that `n3` needs to be defined in terms
   of `n1` and `n2` (i.e., `n3 = f(n1,n2)`), it is not clear what `f`
   is. In this branch, it seems that `f(n1,n2) = Zero`, but this
   solution may be too restrictive to be applicable in other branches.
   Alternatively, solutions `f(n1,n2) = n1` and `f(n1,n2) = n2` may
   not hold in the other branch (where `n1≠Zero` and `n2≠Zero`) if the
   branch returns a vector of size `Zero`.
2. In presence of type-level functions like `Plus`, generalizing the
   relationship between type indices of arguments and results (the
   `f`) is even more difficult as the constraints of `append` example
   make it clear. If we look at first 12 constraints, which are
   generated in the absence of any type annotations on append, they
   offer no clue as to what the structure of `f` is. We have no way of
   knowing that some `Plus` function, defined elsewhere, is going to
   be useful in defining `f`.

**To conclude, in order for ML-ish approach to be successful in
inferring Catalyst types, the GADT type inference problem has to be
solved first**.

With GADTs, "the loss of principal types is both well-known and unavoidable"
([OutsideIn(x)](http://research.microsoft.com/en-us/um/people/simonpj/papers/gadt/implication_constraints.pdf)).

Here is a thought: If I tell you that there is a principal type for a
function, can you find it?

"Type inference for GADTs is notoriously
hard". ".. it is usually enough to only annotate functions". ([OCamlDocs](http://caml.inria.fr/pub/docs/manual-ocaml-400/manual021.html#toc85)) 
