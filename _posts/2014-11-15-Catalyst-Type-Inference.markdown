---
layout: post
title:  "Catalyst Type Inference"
--- 

Introduction
=============

Catalyst admits rich relational type refinements, and inferring
dependent types with such refinements is a non-trivial problem. In
this note, I describe how the problem of inferring (non-parametric)
relational refinements can be framed as a program synthesis problem,
so that established techniques in program synthesis, such as the
Counter-Example Guided Inductive Synthesis (CEGIS), can be used to
infer Catalyst type refinements. One such CEGIS-based type inference
approach has been implemented in Catalyst with mixed results. While
our experiments demonstrated the applicability of synthesis techniques
in inferring relational refinements with simple structure, scaling the
approach to richer refinements has been identified as a problem. This
note suggests possible ways to remedy this problem.

Program Synthesis Problem
=========================

The problem of [syntax-guided
synthesis](http://www.cis.upenn.edu/~audupa/pubs/SyGuS13.pdf) is
concerned with synthesizing a function $$f$$, given its correctness
specification $$\varphi$$ that uses symbols from a background theory
$$T$$. The syntactic space of possible implementations of $$f$$ is
described as a set $$L$$ of expression built from the theory $$T$$, and
this set is specified using a grammar. The syntax-guided synthesis
problem then is to find an implementation expression $$e \in L$$ such
that the formula $$[e/f] \varphi$$ is valid in the theory $$T$$. The
problem is succinctly represented as the following:

$$ (f = ??, \varphi, L, T)$$


Quite often in practice, a partial implementation of function $$f$$
with _holes_ is given, and the synthesis problem reduces to
synthesizing suitable expressions to fill the holes in the partial
implementation. This simpler formulation of synthesis problem is
represented as:

$$ (f = E[??], \varphi, L, T)$$

Where $$E[??]$$ denotes a context (also an expression in L) with a
hole.  For example, consider the following racket code taken from the
[Rosette][onward] paper:

{% highlight racket %}
    #lang s-exp rosette
    (define-symbolic a boolean?)
    (define-symbolic b boolean?)
    (define-symbolic c boolean?)
    (define-symbolic d boolean?)

    (define (RBC-parity a b c d) 
      (xor (<=> a b) (<=> c d)))

    (define (AIG-parity a b c d) 
     (&&
      ;; The following sub-expression denotes a hole, which needs 
      ;; to be filled with an expression (e) constructed from 
      ;; the following recursive grammar:
      ;;   e ::= var | (&& e e) | (! e)
      ;;   var ::= a | b | c | d 
      ;; The depth of the expression is bound at 3.
      (circuit-hole [! &&] a b c d #:depth 3)
      (! (&& (&& (! (&& a b)) (! (&& (! a) (! b))))
             (&& (! (&& (! c) (! d))) (! (&& c d)))))))

    (define model (synthesize
                   #:forall (list a b c d)
                   #:guarantee (assert (eq? (AIG-parity a b c d)
                                            (RBC-parity a b c d)))))


    (display "\n Here is the completed AIG-parity function: \n")
    (generate-forms model)

{% endhighlight %}

As the code comment indicates, there is a hole in the `AIG-parity`
function (The function $$f$$ for which the synthesis problem needs to
be solved). The problem is to fill the hole with a suitable expression
from the stated grammar (the $$L$$ in this case) such that
`AIG-parity` is equivalent to `RBC-parity` for all inputs `a, b, c, d`
Formally, the problem is to fill the hole in the following
specification formula ($$\varphi$$) such that it is valid:

$$\forall(a,b,c,d). (AIG-parity \;a\; b\; c\; d) = 
                    (RBC-parity \;a\; b\; c\; d)$$
                    
The theory $$T$$ in this case is the theory of quantifier-free
boolean formulas.

Dependent Type Inference as Refinement Synthesis
================================================

We consider a version of dependent type inference problem, where the
structure of the dependent type is given, but all refinements are
omitted in favor of holes. For example, here are the input dependent
types of `concat` and `inOrder`

    concat : l1 -> l2 -> {l | ??}
    inOrder : t -> {l | ??}

The problem is to synthesize suitable refinements (denoted $$\phi$$)
to fill the holes, such that the dependent type typechecks against the
implementation of the function.

At the superficial level, the refinement synthesis problem is semantic
inverse of the program synthesis problem; while the later deals with
synthesizing an implementation that satisfies the specification,
refinement synthesis is concerned with synthesizing a specification
given an implementation of the function. Nevertheless, refinement
synthesis can be formally stated as the program synthesis problem
(i.e, as $$(\phi=??,\varphi,L,T)$$), where $$\phi=??$$ denotes the type
refinement to be inferred, $$\varphi$$ denotes the verification
condition (VC) in which $$\phi$$ occurs free, and $$L$$ denotes the
recursive grammar of type refinements ($$\phi$$) shown below:

$$
\begin{array}{lcl}
R & \in & Structural\; Relations\\
v & \in & Variables\; in\; scope\\
Rapp & ::= & R(v)\\
Rexpr & ::= & Rapp \;|\; Rexpr \cup Rexpr \;|\; Rexpr \times Rexpr\\
\phi & ::= & Rapp = Rexpr \;|\; \phi \wedge \phi\\
\end{array}
$$

$$T$$ is the refinement synthesis problem denotes theory of Sets,
Relations and Uninterpreted sorts (denoted $$EPR$$).

For example, consider the concat function:

    fun concat l1 l2 = case l1 of
      [] => l2
    | x::xs => x::(concat xs l2)

Denoting the unknown type refinement of concat as $$\phi$$, the type
inference problem of the concat function is the program synthesis
problem $$(\phi=??,\varphi,L',EPR)$$, where $$L'$$ is the above
grammar with $$R$$ fixed to range over the set $$\{Rhd, Rmem, Robs,
Roas\}$$, and $$v$$ fixed to range over the set $$\{l1,l2,l\}$$.
$$\varphi$$ is the verification condition (VC) that captures the
semantics of `concat` in relational domain. The VC generated by
Catalyst for concat can be seen
[here][github] (Observe that it contains
holes).

CEGIS
=====

Inductive synthesis technique deals with the problem of finding a
program matching a set of input-output examples. Counter-Example
Guided Inductive Synthesis (CEGIS) is the most popular approach to the
inductive synthesis today. The standard high-level formulation of
CEGIS uses two components:

1. An oracle that generates a positive example capturing the I/O
   behaviour of the function f, along with a hypothesis about its
   implementation that explains the positive example.
2. A verifier that either proves the hypothesis generated by the
   oracle, or refutes it by providing a counter-example.

The counter-example generated by the verifier is communicated back to
the oracle so that it can refine its hypothesis in the subsequent
iterations.

In practice, both the oracle and the verifier are implemented using an
SMT solver. To make the solver act as an oracle, it is provided with
the entire candidate space of solutions to the synthesis problem,
along with the specification that the solution has to satisfy, and the
solver is asked if there exists a candidate solution that satisfies
the specification for at least _one_ example input-output assignment.
If there exists such a solution, it is called the hypothesis. In the
subsequent verification phase, this hypothesis is verified by asking
the solver if the candidate solution satisfies the specification for
_all_ possible input-output assignments. If the verification succeeds,
the hypothesis is the solution to the synthesis problem. If the
verification fails, we move on to the next iteration of CEGIS, where
we now ask the oracle to generate a hypothesis that also explains the
counter-examples seen so far. This process is repeated until we find a
valid hypothesis (i.e., the solution to the synthesis problem), or
there are no candidate solutions that can explain the I/O behaviour
seen so far.

To solve the refinement synthesis problem, I implemented CEGIS in
Catalyst. The candidate space of solutions is the set of all
well-formed type refinements generated by the grammar shown
previously. Candidate space is usually quite large even with very few
variables and relations. For example, consider the concat function
with the following dependent type template:

    concat : l1 -> l2 -> {l | ??}

Even when we fix the unknown type refinement ($$\phi$$) to be of the
form `Rmem(l) = ??`, there are many possible (well-typed) solutions to
the hole on the right hand side:

+ `Rhd(l1)`
+ `Rhd(l2)`
+ `Rhd(l1) U Rhd(l2)`
+ `Rmem(l1)`
+ `Rmem(l1) U Rhd(l1)`
+ `Rmem(l1) U Rhd(l2)`
+ and so on ...

This is not even considering the duplicate solutions such as `Rmem(l1)
U Rmem(l2)` and `Rmem(l2) U Rmem(l1)`. Clearly, enumerating all of
possible solutions, and then pruning away duplicate ones such as above
is a very tedious exercise. Fortunately, this can be avoided by
reformulating relational expressions in left-associative form, and
then using a "disjunctive normal form with if-then-else atoms" to
represent the candidate space of all solutions in the solver. The
left-associative formulation of the type refinement grammar is shown
below:

$$
\begin{array}{lcl}
R & \in & Structural\; Relations\\
v & \in & Variables\; in\; scope\\
Ratom & ::= & R(v) \;|\; R(v) \times Ratom\\
Rexpr & ::= & Ratom \;|\; Ratom \cup Rexpr \\
\phi & ::= & Rapp = Rexpr \;|\; \phi \wedge \phi\\
\end{array}
$$

By construction, the expressions in the grammar are in
disjunctive/union normal form (i.e., every expression is a union of
$$Ratom$$s). In this grammar, following is the longest (syntactically
irreducible) candidate solution to the hole in `Rmem(l) = ??`:

    Rhd(l1) U Rhd(l2) U Rmem(l1) U Rmem(l2)

Moreover, observe that any candidate solution to the hole can be
obtained by _erasing_ one ore more of the atoms in the above longest
solution. We capture this intuition by defining an operator `SEL`:

    SEL(a,S) = if a=true then S else {}

When `a` is a boolean variable, `SEL(a,Rhd(l1))` is `Rhd(l1)` if `a =
true`. Otherwise, `SEL(a,Rhd(l1))` is a null-set. Using the operator
`SEL`, we capture the entire space of candidate solutions to the hole
as:

    SEL(a1,Rhd(l1)) U SEL(a2,Rhd(l2)) U SEL(a3,Rmem(l1)) U SEL(a4,Rmem(l2))

Where `a1`, `a2`, `a3`, `a4` are distinct boolean variables called
selectors. We substitute the above expression for $$\phi$$ in the
verification condition ($$\varphi$$) of concat to arrive at the input
to the CEGIS loop. Lets denote the resultant VC as $$\varphi0$$. In
the first iteration, we ask the oracle if $$\varphi0$$ is
satisfiable. The oracle returns SAT with an assignment to literals
`a1`, `a2`, `a3`, and `a4`. An example assignment is `true`, `false`,
`false`, and `false`, respectively, denoting the solution:`Rmem(l) =
Rhd(l1)` for the input case (the positive example) of `l1 = [x]` and
`l2=[]`.  However, verifier refutes this hypothesis providing the
counter-example `l1=[x], l2=[y]`. To reflect this refutation, the
counter-example, and the previously generated positive example, the VC
for next iteration (call it $$\varphi1$$) is extended with following
conjuncts:

+ `not (a1=true /\ a2=false /\ a3=false /\ a4=false)`
+ `SEL(a1,{x}) U SEL(a2,{}) U SEL(a3,{x}) U SEL(a4,{}) = {x}`
+ `SEL(a1,{x}) U SEL(a2,{y}) U SEL(a3,{x}) U SEL(a4,{y}) = {x,y}`

The first conjunct asserts the negation of the failed hypothesis to
prevent it from ever being generated again, the second and third
conjuncts guide the oracle towards generating a better hypothesis.

This process is repeated until the verifier approves the hypothesis
generated by the oracle. An example of such hypothesis is the
assignment [`a1=false`, `a2=false`, `a3=true`, `a4=true`] capturing
the solution `Rmem(l) = Rmem(l1) U Rmem(l2)`. In fact, this is the
solution generated by Catalyst. However, when `a3` and `a4` are
true, any assignment to `a1` and `a2` yields a valid solution. This is
because for any list `l`, `Rhd(l)`$$\subseteq$$`Rmem(l)`. Therefore,
it is just a coincidence that Catalyst generated the solution of
smallest length. Nevertheless, it is possible to guarantee the
generation of type refinements of minimum length by encoding the
problem as a MaxSAT problem. We do not consider this currently. 

Scalability
===========

In the previous section, we restricted the shape of the unknown type
refinement of `concat` to `Rmem(l) = ??`. Now, let us generalize it
to `Rmem(l) = ??  /\ Robs(l) = ??`. Although this only adds one more
element to the syntactic class of $$R$$, the fact that `Robs` is a
binary relation (hence admits cross products) leads to significant
blowup in the candidate state space. The longest (syntactically
irreducible) candidate solution to `Robs` is shown below:

      Robs(l) = (Robs(l2) U (Robs(l1) U 
               ((Rhd(l2) X Rhd(l2)) U ((Rhd(l2) X Rhd(l1)) U 
               ((Rhd(l1) X Rhd(l2)) U ((Rhd(l1) X Rhd(l1)) U 
               ((Rhd(l2) X Rmem(l2)) U ((Rhd(l2) X Rmem(l1)) U 
               ((Rhd(l1) X Rmem(l2)) U ((Rhd(l1) X Rmem(l1)) U 
               ((Rmem(l2) X Rhd(l2)) U ((Rmem(l2) X Rhd(l1)) U 
               ((Rmem(l1) X Rhd(l2)) U ((Rmem(l1) X Rhd(l1)) U 
               ((Rmem(l2) X Rmem(l2)) U ((Rmem(l2) X Rmem(l1)) U 
               ((Rmem(l1) X Rmem(l2)) U (Rmem(l1) X Rmem(l1)))))))))))))))))))

The RHS of the above equation is in disjunctive normal form with 18
atoms, which means there are 2^18 possible solutions to the hole.
If we include the hole with `Rmem` conjunct, the number increases to
2^22. Due to the enormity of (rich) state space, Z3 was not able
decide validity of hypotheses in this case. This tells us that the
naive approach of offloading all reasoning to Z3 does not scale beyond
trivial type refinements. Type inference needs to be smart and pose
right kind of questions to the solver. In the following sections, I
propose some ways this can be done.

One hole at a time
===================

With every addition of a hole, there is an exponential increase in the
candidate state space. For example, while the type refinement template
`Robs(l) = ??`, which has only one hole, has 2^18 candidate
solutions, the template `Rmem(l) = ?? /\ Robs(l) = ??`, which has two
holes, has 2^22 solutions. This blowup can be avoided by solving
one hole at a time, instead of trying to solve both at the same time.
Order of solving the holes is also important. For example, there exists
no solution to the hole `Robs(l) = ??` unless the hole `Rmem(l) = ??`
is solved as `Rmem(l) = Rmem(l1) U Rmem(l2)`. This is because the VC
includes inductive hypothesis that is obtained from the return type of
recursive call to `concat`. Unless this hypothesis contains membership
invariant, the order invariant cannot be proved. 

Fortunately, the appropriate order in which holes can be solved can be
found out easily from the syntactic structure of the definition of
relations. For example, given that the definition of occurs-before
refers to the membership relation (`Rob(x::xs) = {x} X Rmem(xs)`), but
the converse is not true, it is apparent that hole for `Robs` might
need the invariant in terms of `Rmem`. Hence the hole for `Rmem` needs
to be solved before the hole for `Robs`. 

[sketch]: http://people.csail.mit.edu/asolar/papers/asplos06-final.pdf
[onward]: http://homes.cs.washington.edu/~emina/pubs/rosette.onward13.pdf
[github]: https://github.com/tycon/catalyst/blob/cegis/catalyst/test/rev.vcs#L198

