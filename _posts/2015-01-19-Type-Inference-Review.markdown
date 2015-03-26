---
layout: post
title:  "Catalyst Type Inference Review"
---

In this post, I first review the current approach to infer dependent
types in Catalyst, discuss what is currently possible with this
approach along with its limitations. I then sketch some of alternative
approaches to type inference that I am currently considering. 

Current approach: CEGIS aided by concrete executions
----------------------------------------------------

The current approach to infer types in Catalyst can be summarized as
CEGIS aided by concrete executions of the program. The current
approach can infer dependent types for functions, whose invariants can
be expressed in the following simple grammar (lets call it _Grammar
V1_):

$$
\begin{array}{lcl}
R & \in & Structural\; Relations\\
v & \in & Variables\; in\; scope\\
Ratom & ::= & R(v) \;|\; R(v) \times Ratom\\
Rexpr & ::= & Ratom \;|\; Ratom \cup Rexpr \\
\phi & ::= & Rapp = Rexpr \;|\; \phi \wedge \phi\\
\end{array}
$$

Examples of such functions include `concat`, `rev`, `inOrder`,
`preOrder`, and `postOrder`. We have previously tried [naive
enumeration + cegis approach][naive-cegis], which generates all
possible candidate refinements from the above grammar, and relies on
counterexample-based refinement (CEGIS) to arrive at the final
invariant. If the invariant of the function cannot be expressed in the
aforementioned grammar, then the approach simply returns the trivial
true invariant. 

Naive enumeration strategy is sketched in the following figure:

![NaiveEnumeration]({{ site.baseurl }}/assets/naive-enumeration.jpg)

CEGIS is described in the following figure:

![CEGIS]({{ site.baseurl }}/assets/naive-cegis.jpg)

In practice, even for the simple grammar, _naive enumeration + CEGIS_
was found to be ineffective; except for the simplest of invariants
containing no more than 5 atomic candidates, the SMT solver acting as
the oracle fails to generate a model (hence, a hypothesis to verify).
As a result, naive CEGIS cannot infer the _occurs-before_ invariant of
the `concat` function as its candidate space contains 20 atomic
disjuncts.

However, the actual _occurs-before_ invariant of concat contains only
3 disjuncts:

    concat : l1 -> l2 -> {l | Robs(l) = Robs(l1) U Robs(l2) U Rmem(l1)XRmem(l2)}

This means that if we can drastically reduce the candidate space of
solutions for _occurs-before_ invariant, CEGIS could be successful in
inferring the valid invariant. Here is where we introduced the runner
component. The idea is to observe the behaviour of `concat` over
finite number of random inputs, and weed out the candidate atoms that
are not part of the invariant for concrete runs (hence will not be
part of the final invariant). The following figure describes CEGIS
extended with the runner component:

![CEGIS+Runner]({{ site.baseurl }}/assets/cegis+runner.jpg)

Following is the schematic of the current approach (_Naive enumeration
+ CEGIS + Runner_):

![CurrentApproach]({{ site.baseurl }}/assets/current-approach.jpg)

The runner has been proved to be quite useful in practice. The simple
examples, such as `concat` and `inOrder`, exhibit consistent behaviour
over every list and tree regardless of their sizes or properties of
their constituent elements. For these examples, it has been observed
that the invariant that holds over small number (~5) of concrete runs
is also the final invariant, which is usually small in size (~4
atoms).  Consequently, CEGIS runs without any problem confirming the
validity of the invariant.

Limitations of the current approach
-----------------------------------

The current approach infers type refinements drawn from a very
restricted grammar. As such, invariants for many interesting functions
cannot be expressed in the grammar. For example, consider the
following `zip` function:

    zip : 'a list -> 'b list -> ('a*'b) list
    fun zip [] [] = []
      | zip x::xs y::ys = (x,y)::(zip xs ys)

<!-- 
    exists_eq : int list -> int -> bool
    fun exists_eq l id = case l of
        [] => false
      | x::xs => (x=id) orelse (exists_eq xs id)
-->
The catalyst type for the `zip` function requires multiple instances
of parametric _occurs-before_ relation, instantiated with structural
relations `Rfst` and `Rsnd`, and primitive relation `RId`. The type is
shown below: 

    zip : l1 -> l2 -> {l | Robs[Rfst](l) = Robs[RId](l1) /\
                           Robs[Rsnd](l) = Robs[RId](l2)}

Clearly, the type refinement cannot be expressed in the simple grammar
that we presented previously due to the lack of parametric relations.
Therefore, let us extend the grammar of type refinements to include
parametric relations. However, to keep things simple, let us keep the
grammar of types intact (i.e., do not add relational parameters).
Consequently, parametric relations in type refinements are always
instantiated with concrete relations. The grammar is given below (lets
call it _Grammar V2_):

$$
  \begin{array}{lcl}
  R & \in & Structural\; Relations,\; Primitive\; Relations\\
  v & \in & Variables\; in\; scope\\
  \rho & ::= & \rho[\rho] \;|\; R \\
  Ratom & ::= & \rho(v) \;|\; \rho(v) \times Ratom\\
  Rexpr & ::= & Ratom \;|\; Ratom \cup Rexpr \\
  \varphi & ::= & Ratom = Rexpr \;|\; \phi \wedge \phi\\
  \end{array}
$$

The candidate state space of refinements expressible in this grammar
is still finite, although it can get quite large as we add more
relations to the syntactic class $$R$$. In the case of `zip`, assuming
that we have following 3 structural relations defined on the `'a*'b`
type:

    Rfst (x,y) = {x};
    Rsnd (x,y) = {y};
    Rpair (x,y) = {x} X {y};

and that there are 4 parametric relations (`Rhd[R]`, `Rmem[R]`,
`Robs[R]`, and `Roas[R]`) defined on the list type, there are
$$4\times3=12$$ different relational abstractions of the result list
for which inference tries to infer invariants. For each invariant, the
candidate space can contain up to 20 distinct atomic disjuncts, which
is also the case with `concat`. Further, like `concat`, concrete runs
of `zip` are expected to reduce the space to 3-4 atomic disjuncts,
which is small enough for CEGIS to work without the solver timing out.
This suggests that the current approach of CEGIS+Runner is indeed
capable of inferring all invariants for `zip` despite the presence of
parametric relations.

Another interesting example which can be typed in Grammar V2 is
`filter_neq` function, which filters elements not equal to some `id`
in its input list. The function is shown below:

    filter_neq : int list -> int -> int list
    fun filter_neq l id = case l of
        [] => []
      | x::xs => 
        let
          val xs' = filter_neq xs id
          val l' = if x=id then xs' else x::xs'
        in
          l'
        end

Its relational type makes use of the primitive relation `RNeq` defined
as `RNeq = \y.\x.{x} - {y}`. Observe that `RNeq y x = {x}` if `x≠y`,
and `RNeq y x = {}` otherwise. The type is shown below:

    filter_neq : l1 -> id -> { l | Rmem[RId](l) = Rmem[RNeq id](l1)}

With the introduction of `RNeq` relation, there are now 2 primitive
relations on `'a` type: `RId` and `RNeq`. Given that there are 4
structural relations defined on `'a list`, type inference tries to
infer invariants for $$4\times2=8$$ relational abstractions of the
result list. Further, candidate space for each invariant now includes
relational abstractions of `l1` with respect to _both_ primitive
relations. Since `filter_neq` has only one list argument, the
candidate space still has around 20 atomic disjuncts. However, due to
the introduction of new primitive relation, the candidate space
doubles (~40 atomic disjuncts) in case of `zip` and `concat`.

In general, if the type structure of an ML type $$T$$ has depth $$d$$,
and each ML type has $$k$$ parametric structural relations defined,
then there exist $$O(k^d)$$ relational abstractions for $$T$$. This
suggests that the number of distinct relational abstractions for which
the inference tries to infer invariants increases exponentially as we
define more structural and primitive relations. Furthermore, the
candidate space for each invariant also increases exponentially as we
add more relational operators (e.g: union and minus) to our grammar.
For example, consider the `intersection` function:

    intersection : int list -> int list -> int list
    fun intersection [] l2 = l2
      | intersection x::xs l2 = 
        let
          val l' = intersection xs l2
          val l = if exists_eq l2 x then x::l' else l'
        in
          l
        end

A straightforward relational type for `intersection` is the
following:

    intersection : l1 -> l2 -> {l | Rmem[RId](l) = Rmem[RId](l1) ∩ Rmem[RId](l2) }

However, addition of the intersection operator to the grammar leads to
doubling of candidate state space for every invariant. Consequently,
instead of dealing with a candidate space of 40 atoms, we now have to
deal with 80 atoms in case of `concat` and `zip`. Moreover, due to the
obvious subset relationships that exist between various atoms (eg:
`Rhd(l1) ⊆ Rmem(l1)` and `Robs(l1) ∩ Robs(l2) ⊆ Robs(l1)`), the size
of the state space left after pruning by the runner also doubles. This
invariant could be too large for CEGIS to work (recall that CEGIS
times out on candidate spaces containing more than 5 atoms).

We get similar results with the introduction of the set difference
(minus) operator, which is required to state the invariant of
the `subst` function in the alpha conversion example:

    datatype exp =    Var of string
                    | App of exp*exp
                    | Abs of string*exp

    fun alphaConvert (e:exp) : exp = case e of                                      
        Abs (id,e') => 
        let 
          val fv_e' = freeVars e'                                       
          val id' = createNewName fv_e' id
        in
          Abs(id',subst (Var id') id e')
        end
      | _ => raise Fail "No alpha-conversion for Unbound terms"
    and subst (e1:exp) (id:string) (e2:exp) :exp = case e2 of
        Var id' => if idEq (id,id')
          then e1 else (Var id')
      | App(e21,e22) => App(subst e1 id e21, subst e1 id e22)
      | Abs(id',e2') => if idEq (id',id) then e2 else
        let
          val fv_e1 = freeVars e1 
        in
          if exists_eq fv_e1 id'
          then subst e1 id (alphaConvert e2)
          else Abs(id',subst e1 id e2')
        end

Following is the relational type of `subst`:

    subst : e1 -> id -> e2 -> {ex | IF ({id} ⊆ Rfv(e2)) 
                THEN Rfv(ex) = Rfv(e2) - {id} U Rfv(e1) 
                ELSE Rfv(ex) = Rfv(e2) };

In the above type,`Rfv` denotes the set of free variables in an
expression. Apart from the minus operator, the type refinement also
makes use of `IF-THEN-ELSE` operator, which is effectively a syntactic
sugar for a disjunctive proposition involving implications. Given that
`IF-THEN-ELSE` is a rich operator that operates on a boolean
expression and two relational expressions, introducing it (along with
the minus operator) into the grammar of type refinements leads to a
significant blow up in the candidate space of solutions to unknown
invariants. The increase in state space makes it practically
infeasible to enumerate and test all possible solutions in case of
non-trivial functions, such as the `subst` function. 

Towards a better strategy
-------------------------------

In lieu of above observations, there is a need to go beyond the
current strategy of enumerate-prune-verify implemented by CEGIS+Runner
in order to scale the inference to non-trivial benchmarks like
`subst`. Although I currently do not have concrete proposals in this
direction, there are some observations which I think are key to a
better type inference:

1.Guess and Check
-----------------

The current approach uses runner to prune the candidate state space
generated initially by the naive enumeration strategy. Pruning is done
based on the observed behaviour of the program on random test cases,
which is effective only to some extent. The candidate set might still
contain large number of invalid hypotheses, which nonetheless
explain the observed behaviour. The current approach relies on CEGIS's
counterexample-guided refinement to further prune the search space and
eventually zero in on the final invaraint. CEGIS relies on an SMT
oracle to pick an appropriate hypothesis that explains the
counterexamples seen so far. Solver has to peform expensive reasoning
with the abstract representation (the VC) of the program in order to
generate the hypothesis. Given that the candidate state space can
still be large, oracle may timeout before generating any hypothesis.
In fact, this is what happens in practice when candidate state space
contains more than 5 atoms.

An alternative approach is to do away with the SMT oracle, and solely
rely on the runner to generate a hypothesis. Since the runner can pick
the hypothesis that explains the given counterexample simply by
running the program on inputs corresponding to the counterexample, why
rely on expensive reasoning? The schematic of this approach (which I
call _Guess-And-Check_) is shown below:

![GuessAndCheck]({{ site.baseurl }}/assets/guess-and-check.jpg)

One challenge with this approach is the implementation of model
parser. Recall that SMT solver works with the abstract relational
representation of the program, which means that the counterexamples
generated by the verifier are also relational. For example, if the
counterexample is a list (`l`) containing the constant `id` (lets say
that the list is `[id',id]`, where `id'` is some other symbol),
verifier describes the list in terms of its relational abstractions
as:

    Rmem(l) = {id,id'}
    Robs(l) = {(id',id)}

It is now incumbent on the model parser to parse the above model and
generate the concrete list. How can the model parser go about solving
this problem? Indeed, by generating constraints and relying on the
solver again. Let us say that the model parser knows that `l` is
non-empty (again, by relying on the solver), and let `x0` denote the
first element of `l`. From the definition of `Rmem` and `Robs`, model
parser knows the following that for some sets `S1` and `S2`, following
is true:

    Rmem(l) = {x0} U S1
    Robs(l) = {x0} X S1 U S2

From the above two sets of equations, we have the following
constraints:

    {x0} U S1 = {id,id'}
    {x0} X S1 U S2 = {(id',id)}

Relying on solver to solve the above constraints, we get that
`x0=id'`, `S1={id}`, and `S2={}`. We now know that the first element
of the counterexample list is `id'`. Repeating the process, we will
also know that the second element is `id`, and the list ends there.
Hence, model parser can generate the apprropriate list representation
of the relational counterexample.

<div id="smart-enumeration" />

2.Rich primitive relations can replace {∩,-, IF-THEN-ELSE} in type refinements
----------------------------------------------------------

Let us recall the `REq` primitive relation:

    REq x y  = \x.\y. {x} - ({x} - {y})

In other words, `REq` is a primitive relation such that `REq x y =
{x}` if `x=y`, and `REq x y ={}` otherwise. 

With help of `REq` relation, we can define the intersection of
`Rmem[RId](l1)` and `Rmem[RId](l2)` as:

    Rmem[RId](l1) ∩ Rmem[RId](l2) = Rmem[\x.Rmem[\y.REq x y](l2)](l1)

This demonstrates that intersection can be expressed using only
primitive relations. Now, let us extend the syntax of primitive
relation definitions with IF-THEN-ELSE operator. With help of this
operator, intersection can be defined even more directly:

    
    Rmem[RId](l1) ∩ Rmem[RId](l2) = 
        Rmem[\x. IF x∈Rmem(l2) THEN {x} ELSE {}](l1)

We refer to the above as primitive relational definition of
intersection. The advantage with primitive relational definition of
intersection is that it is more _operational_ (i.e., closer to the
actual implementation of intersection) than the conventional
definition, while still being in the realm of decidable logic.

Now, reconsider the `intersection` function:

    fun intersection [] l2 = l2
      | intersection x::xs l2 = 
        let
          val l' = intersection xs l2
          val l = if exists_eq l2 x then x::l' else l'
        in
          l
        end

Assume that the type of `exists_eq` is as following:

    exists_eq : l -> id -> {v | v=true <=> id∈Rmem(l)}

In the `l1=x::xs` branch, we have the invariant that `Rmem(l1) = {x} ∪
Rmem(xs)`. If we interpret `val l = ...` relationally, without the
reference to the return list from recursive call (i.e., `l'`), we have
the following:

    if x∈Rmem(l2) then x∈Rmem(l) else x∉Rmem(l)

Let us say that the above is true for every `x` in a set S. That is:

    ∀x∈S. if x∈Rmem(l2) then x∈Rmem(l) else x∉Rmem(l)

Then, from the definition of bind, following is true:

    bind(S,\x.if x∈Rmem(l2) then {x} else {}) ⊆ Rmem(l)

In the `intersection` example, it is indeed the case that the
expression `if exists_eq l2 x then x::l' else l'` executes for every
`x` in the list `l1`. Therefore, we have `S=Rmem(l1)` in the above
proposition making the following true:

    Rmem[\x.IF x∈Rmem(l2) THEN {x} ELSE {}](l1) ⊆ Rmem(l)

Observe that LHS is the primitive relational definition of `Rmem(l1) ∩
Rmem(l2)`. Although the final invariant is stronger than the above
proposition (LHS = RHS instead of LHS ⊆ RHS), the proposition gives us
the clue to the structure of the invariant, without actually having
to enumerate all the candidate solutions. 

This example demonstrates that it could indeed be possible to _mine_
from the text of the program or its relational interpretation (i.e.,
VC), primitive relations that are necessary to construct its
relational type. Once we have all primitive relations required to
construct the type, the existing enumeration approach can be used to
infer the actual invariant. Note that with appropriate primitive
relations we don't have to add the intersection operator to our
grammar. Consequently, candidate state space remains manageable.

Similar to intersection, we can give primitive relational definition
to minus operator:

    S1 - S2 = S1[\x. IF x∈S2 THEN {} ELSE {x}]

Inspired by the above definition of minus, we can rewrite the
invariant of `subst` function as following:

    subst : e1 -> id -> e2 -> {ex | Rfv(ex) = Rfv[\id'.IF id'=id THEN Rfv(e1) ELSE {id'}](e2)};

Take a look at the primitive relation used in the type refinement of
`subst`:

    \id'.IF id'=id THEN Rfv(e1) ELSE {id'}

Now, consider the `Var` branch of subst function:

    Var id' => if idEq (id,id') then e1 else (Var id')

The above `if-then-else` expression can be rewritten as following: 

    let val ex = if idEq (id,id') then e1 else (Var id') in ex end
    
Here is its relational interpretation:

    Rfv(ex) = IF id'=id THEN Rfv(e1) ELSE {id'}

Note the similarity between the structure of primitive relation used
in the type refinement of `subst` and the RHS of the above equation.
As the case with `intersection` example, the similarity suggests that
it might indeed be possible to construct the primitive relation as a
candidate relation of interest while analyzing `subst`.

The above examples of `intersection` and `subst` demonstrate a
hypotheses enumeration strategy that is supported by a semantic
analysis of the program. This schematic of this enumeration strategy,
called the _smart enumeration strategy_, is shown below:

![SmartEnumeration]({{ site.baseurl }}/assets/smart-enumeration.jpg)

The semantic analysis, which is the integral part of the smart
enumeration strategy, is expected to synthesize all the primitive
relations that are most likely to be useful in describing the
invariant of the program. As evident in the above examples, the
ability to synthesize a (reasonably small) set of primitive relations
needed to express the invariant obviates the need to extend the
grammar with multiple relational operators, thereby drastically
reducing the candidate state space.

The smart enumeration strategy can be used in conjunction with any of
the counter-example guided refinement methods discussed previously to
build an effective inference procedure. The schematic is shown below:

![PromisingApproach]({{ site.baseurl }}/assets/promising-approach.jpg)

3.Counter Example Guided Hindley-Milner (CEGHiM)
------------------------------------------------

Given the complexity of relational types (vis-a-vis ML types), it is
unlikely that we will ever have a sound algorithm that simply analyzes
the program in the Hindley-Milner style and infers the correct type
(see Note1 at the end of this document).  On the other hand,
approaches that blindly enumerate all hypotheses without concerning
themselves with program semantics are very ineffecient and do not
scale for real-world programs. In this context, we can envision an
approach that strikes balance between these two extremities. Instead
of trying to infer a sound type in one go or trying to enumerate all
possible types in advance, the approach can start by inferring a
single type that is most likely (but not guaranteed) to be valid. In
the event of the type being judged invalid by the verifier, the
approach can use the counterexample to refine its initial hypothesis
and generate a better hypothesis for the subsequent iteration. In
other words, the approach tries to construct a sound type inference
algorithm by supplementing an unsound semantic analysis with an
intelligent counter-example guided refinement strategy. We call this
approach as _Counter Example Guided Hindley-Milner (CEGHiM)_.


4.A Data-driven approach to generate candidate hypothesis.
---------------------------------------------------------

Another way to avoid enumerating candidate state space is to rely on
concrete data.  R.Sharma et al's [ESOP13 paper][esop13]
([summary][esop13-summary]) presents a data-driven approach to infer
algebraic loop invariants for real-number programs. The novelty of
their method is in using linear algebra to generate a candidate
hypothesis that explains observed behaviour of the program on sample
inputs. Is it possible to devise a similar method to generate
candidate hypotheses in relational domain?  In other words, does there
exist an algorithm that takes a set of sets (`S`) and a set (`s`), and
returns a strongest proposition in some grammar `G` that relates sets
in `S` and the set `s`?

The schematic of the data-driven approach is shown below. What we
currently don't know is how to implement the synthesizer.

![DataDriven]({{ site.baseurl }}/assets/data-driven-approach.jpg)

5.Intelligent counterexample-guided refinement
----------------------------------------------

Initial hypothesis generated by the unsound semantic analysis in
CEGHiM, or by the data-driven apporach is not necessarily the final
invariant. In such case, we should be able to refine the hypothesis
with help of the counterexample. Note that the current approach does
indeed have counterexample-guided refinement inherent in the CEGIS
loop. However, the refinement strategy is naive in the sense that it
simply removes the failed hypothesis from the set enumerating all
hypothesis, and selects a new hypothesis that satisfies the
counterexample. As such, this naive refinement strategy only works if
the set of all candidate hypothesis is available beforehand. Since it
does not understand the semantic significance of the counterexample,
it cannot _refine_ the existing hypothesis to generate a new
hypothesis.

Let us conjecture how an intelligent counterexample-guided refinement
might work in tandem with data-driven approach. Lets assume that
data-driven approach has observed concrete executions of `subst`
function on random inputs and generated a candidate hypothesis. Since
randomly generated expression `e2` is unlikely to contain the randomly
generated `id` as a freevar, `subst` behaves as the identity function
in the observed runs leading the observer to conclude that `Rfv(ex) =
Rfv(e2)` (`ex` is the result expression). However, verification fails
on the candidate `Rfv(ex)=Rfv(e2)` generating a counterexample that
includes constant `id` in `Rfv(e2)`. 

How can the data-driven approach use the counterexample? It can adopt
the following strategy:

1. First, it can negate the condition denoted by the counterexample
   and re-verify if its initial hypothesis. In this case, the
   condition that characterizes the counterexample is `id∈Rfv(e2)`.
   The refined hypothesis the preempts this condition is `id∉Rfv(e2)
   => Rfv(ex)=Rfv(e2)`. This hypothesis is indeed valid. However, it
   only captures the behaviour of `subst` when the condition
   `id∈Rfv(e2)` is invalid (first half). The inference process has to
   still infer the invariant when the condition is satisfied (second
   half).
2. To infer the second half of the invarint, the data-driven approach
   _enforces_ the condition denoted by the counterexample by
   generating a sample input that satisfies the condition. In this
   case, a sample input that satisfies `id∈Rfv(e2)` is a lambda
   expression that contains `id` as a freevar. The data-driven
   approach will now observe the runs of `subst` on this input and
   generate a different candidate hypothesis. For example, it may now
   infer that the equation `Rfv(ex) = Rfv(e2) - {id} U Rfv(e1)`
   explains the observed IO behaviour of `subst` when input (`e2`)
   satisfies the condition `id∈Rfv(e2)`. Consequently, it generates a
   `id∈Rfv(e2) => Rfv(ex) = Rfv(e2) - {id} U Rfv(e1)` as the new
   hypothesis. The hypothesis is indeed valid, completing the
   invariant.
3. The final invariant is the conjunction of both the halves:
   `(id∉Rfv(e2) => Rfv(ex)=Rfv(e2)) ∧ (id∈Rfv(e2) => Rfv(ex) = Rfv(e2) - {id} U Rfv(e1))`.

First two steps of the above process repeat themselves until the
verification succeeds, or the approach fails to generate any new
hypotheses. Although the approach looks reasonable on the `subst`
example, its convergence properties are not clear.

Conclusion
----------

Catalyst currently employs enumerate-test-verify strategy for type
inference via CEGIS augmented with a Runner component. Although the
strategy is succesful in inferring types for simple functions, it is
likely to be ineffective or very ineffecient for non-trivial
functions. Alternative approaches to type inference have been
sketched.

Notes
-----

1. If a sound HM-style type inference algorithm exists for Catalyst,
   it should necessarily be able to solve GADT type inference problem.
   Given that the problem is ["notoriously hard"][ocamldocs], and even
   the [state-of-the-art][OutsideIn] solution [cannot infer][stackoverflow] 
   a type for a function as simple as `append`, there is little hope
   that Hindley-Milner approach succeeds in inferring Catalyst types.
   See my [previous wiki][wiki20150110] for a more comprehensive analysis.

[naive-cegis]: https://www.cs.purdue.edu/sss/projects/catalyst/2014/11/15/Catalyst-Type-Inference.html
[esop13]:http://web.stanford.edu/~sharmar/pubs/esop13.pdf
[esop13-summary]: https://www.cs.purdue.edu/sss/projects/catalyst/2015/01/15/Paper-Review-Sharma-Aiken-Esop13.html
[OutsideIn]: http://research.microsoft.com/en-us/um/people/simonpj/papers/gadt/implication_constraints.pdf
[ocamldocs]: http://caml.inria.fr/pub/docs/manual-ocaml-400/manual021.html#toc85
[stackoverflow]: http://stackoverflow.com/questions/27934337/ghc-could-not-infer-types-in-presence-of-gadts-and-type-families
[wiki20150110]: https://www.cs.purdue.edu/sss/projects/catalyst/2015/01/10/Alternative-Approach.html
