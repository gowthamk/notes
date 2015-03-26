---
layout: post
title:  "Combining Unification with SMT"
---

Unification based type inference ([wiki][algo1]) has been successful
in inferring types for simple first-order functions. We have also
presented some [ideas][algo2] how this approach can be extended to
parametric relations and higher-order functions. However, our approach
has many weak links:

1. Unification is a syntactic process, hence weak. It could fail in
   cases where semantic equivalence does not manifest as syntactic
   equality in equational constraints. It is therefore better to
   employ a solver wherever possible during unification.
2. Our inference algorithm is built to infer the invariant **one
   disjunct at a time**. This approach fails when we cannot justify
   the presence of a disjunct in the invariant, except in conjunction
   with one or more other disjuncts. One instance when this occurs is
   the `alternate` function defined later in this wiki. Since this
   scenario is fairly common, the algorithm needs to be generalized to
   infer a clique of disjuncts, which are either all present or all
   absent.
3. The _one disjunct at a time_ approach becomes even more restrictive
   while inferring disjuncts for alphas. If the algorithm adopts an
   approach similar to non-alpha disjuncts while inferring
   α-disjuncts, it should to the following:

   + Step 1: Since there are no ill-formed disjuncts to start with,
     algorithm has to make a guess and select an input relational
     abstraction (RAbs) of appropriate sort as a hypothesis (hyp).
     There is no obligation (ob) generated.
   + Step 2: The algorithm applies hyp in α, to generate a new
     disjunct δ. This disjunct can either be well-formed or
     ill-formed.
   + Step 3: If the disjunct is well-formed, then we are done.
     Otherwise, the algorithm treats δ as any other ill-formed
     disjunct, and tries to eliminate it via unification.

   Most often, in reality, unification yeilds the same hypothesis
   (hyp) that, in first place, produced the ill-formed disjunct δ.
   Why? Most functions have trivial recursive structure. If `l1 =
   x::xs` in the current branch, then applying `Rmem(l1)` as hyp in
   α most often generates `Rmem(xs)`, which can only be unified with
   `Rmem(l1)` again. Applying `Rmem(l1)` in α, again produces
   the ill-formed `Rmem(xs)`, hence it is useless. Therefore,
   unification should be considered a failure if it cannot produce a
   hypothesis other than hyp. Even when unification produces a
   different hypothesis than hyp (call it hyp'), it would most
   probably be invalid. For example, if `l1=x::xs` and `l2=y::ys` in
   the current branch, the applying `Rmem(l1)` as hyp in α might, in
   some cases, generate `Rmem(ys)`. Trying to eliminate this
   ill-formed disjunct, the algorithm generates (`Rmem(l2)`,`{y}`) as
   (hyp',ob'). Applying `Rmem(l2)` in α, might either `Rmem(xs)`, or
   `Rmem(ys)`, or `Rmem(l1)`, or `Rmem(l2)`. Except in the last case,
   the obligation cannot be discharged. In last case, ob' is satisfied
   because `Rmem(l2)` is equivalent to `{y} U Rmem(l2)`. However, the
   last case occurs when recursive call is made with `ys` and `l2` as
   arguments, which is very unusual because it ignores `l1` entirely. 

   The above paragraph makes it clear that there is very little reward
   for considering ill-formed disjuncts in Step 3 of the algorithm.
   Therfore, our actual [algorithm][algo1] considers only well-formed
   disjuncts in Step 3. 
   
   In reality, our strategy to eliminate alpha performs badly on
   most tail-recursive functions. An example is the tail-recursive
   definition of `rev` shown later in this wiki. Modifying algorithm
   to consider ill-formed disjuncts in Step 3 makes no difference, as
   the fundamental problem is our _one hypothesis at a time_ approach:
   "A hypothesis better justify itself. No new hypotheses are
   generated to justify the current hypothesis".

In this wiki, we modify and extend our algorithm to address each of
the aforementioned shortcomings. All the fixes end up involving SMT
solver into the workflow, hence the title of this wiki.

## From Syntactic Equality to Semantic Equivalence

Consider the following contrived function named `foo` that takes two
lists and replicates the first element of the first list as many times
as the length of the second list.

    fun foo l1 [] = []
      | foo (l1 as x::xs) (y::ys) = 
          let
            val l = foo l1 ys
            val v = x::l
          in
            v
          end

Here are the simplified equational constraints obtained from the VC of
the `l1 as x::xs` branch:

      Rmem(l1) = {(x)} U Rmem(xs)
      Rhd(l1) = {(x)}
      Rmem(v) = {(x)} U [ys/l2]α
    -------------------------------
      Rmem(v) = α

Unification algorithm first tries to eliminate all ill-formed
disjuncts from opEqRHS. In this example, opEqRHS is `{(x)} U
[ys/l2]α`, and the only ill-formed disjunct is `{(x)}`. The algorithm
can unify this `{(x)}` with `{(x)}` in the RHS of the first input
equation, generating `(Rmem(l1),Rmem(xs))` as
hypothesis(hyp)-obligation(ob) pair. Lets denote the opEqRHS sans the
ill-formed disjunct as opEqRHS'. The hypothesis should now be applied
to α in opEqRHS', and the resultant opEqRHS'' has to _satisfy_ (see
footnote #1) the obligation, for the hypothesis to be judged valid.
Applying hypothesis `Rmem(l1)` in α results in `Rmem(l1)` again, as
`[ys/l2]Rmem(l1)` = `Rmem(l1)`. Unfortunately, unification fails as
the obligation `Rmem(xs)` cannot be unified with `Rmem(l1)`. This
results in the hypothesis `Rmem(l1)` getting invalidated despite it
being a perfectly sensible hypothesis under the given constraints.

The `foo` example demonstrates the inadequacy of syntactic unification
as the mechanism to judge the validity of a hypothesis. Fortunately,
the strategy adopted by our inference algorithm to make informed
guesses about likely hypotheses is not tied to unification; it merely
needs a decision procedure to decide equality and subset inclusion
predicates on relational expressions. We have used unification for
this purpose, since it was sufficient for examples with trivial
recursion pattern, such as `concat`. Clearly, unification is too weak
for functions with non-trivial recursion pattern, such as `foo`. We
therefore switch to SMT solver as the decision procedure. At the
high-level, we modify our algorithm to be parametric over any decision
procedure (D):

1. Firstly, instead of syntactically unifying the ill-formed disjunct
   (δ) with a disjunct in the RHS of an input relational abstraction
   (RAbs), we ask D if `δ ⊆ RAbs`. For the `foo` example, this
   translates to the following query to the solver:

          Rmem(l1) = {(x)} U Rmem(xs)
          Rhd(l1) = {(x)}
          {(x)} ⊆ Rmem(v)
        -------------------------------
          {(x)} ⊆ Rmem(l1)? 
  
   Notice that we have weakened the antecedent to remove the alpha.
   Specifically, we have replaced `Rmem(v) = {(x)} U [ys/l2]α` with
   `{(x)} ⊆ Rmem(v)`. 
   If the query is answered positively by D, then RAbs becomes a
   hypothesis.  
2. What do we mean when we say that RAbs is a hypothesis? It means
   that we hypothesize RAbs to be a disjunct in α. To verify that this
   is indeed the case, we need to ask D if `RAbs ⊆ α`. For the `foo`
   example, this means asking if `Rmem(l1) ⊆ α`. Clearly, it is
   impossible to frame this query without knowing α, which we are yet
   to infer! 
   The way forward is to frame a stronger query, whose validity implies
   the validity of the original query, and hence the hypothesis (see
   footnote #2). The structure of this stronger query will be apparent
   if we look at the original equational constraint system of `foo`:

        Rmem(l1) = {(x)} U Rmem(xs)
        Rhd(l1) = {(x)}
        Rmem(v) = {(x)} U [ys/l2]α
      -------------------------------
        Rmem(v) = α

   From the last equation in the antecedent, and the equation in the
   consequent, we know that `α = {(x)} U [ys/l2]α`. Since we
   conjecture `Rmem(l1)` to be a disjunct in α, we have that `α =
   Rmem(l1) U s`, for _some_ unknown relational expression `s`.
   Rewriting the RHS of former equation using the later equation (we
   call this rewriting as _applying_ the hypothesis in α), we have: `α
   = {(x)} U Rmem(l1) U [ys/l2]s`. Now, the query `Rmem(l1) ⊆ α` is
   equivalent to the query `Rmem(l1) ⊆ {(x)} U Rmem(l1) U [ys/l2]s`,
   which is also impossible to frame as we don't know the relational
   expression `s`. Here is where we rely on our _one disjunct at a
   time_ principle that translates into the restriction that a
   _hypothesis has to justify itself_. We came up with the hypothesis
   of `Rmem(l1)` to eliminate the ill-formed disjunct `{(x)}` from
   opEqRHS. Applying the hypothesis in α resulted in an extra term
   (`Rmem(l1)`) in opEqRHS. The simplest way to justify the validity
   of our hypothesis, without generating any further proof
   obligations, is if the hypothesis (`Rmem(l1)`) accounts for both,
   the ill-formed disjunct (`{(x)}`) and the newly introduced term
   (`Rmem(l1)`). We therfore check if `Rmem(l1) = {(x)} U Rmem(l1)`
   (Not in a straightforward way; see footnote#3), which is indeed
   valid, thus justifying the hypothesis. This method of judging the
   validity of `Rmem(l1) ⊆ {(x)} U Rmem(l1) U [ys/l2]s` by checking
   the validity of stronger assertion (`Rmem(l1) = {(x)} U Rmem(l1)`)
   is sound and simple, but very conservative, as the following
   section demonstrates.
   
   <!-- Since we don't know the relational expression `s`, we
   abstract the term `[ys/l2]s` as set `s'`, and make the stronger
   query `Rmem(l1) ⊆ {(x)} U Rmem(l1) U s'` to D. The query passes
   verification, validating our original hypothesis.

   Why is the query we made to D (`Rmem(l1) ⊆ {(x)} U Rmem(l1) U s'`)
   stronger than the original query `Rmem(l1) ⊆ α`? The query we made
   to D is considered valid if it is valid for _any_ choice of set
   `s'` (see footnote#3). In contrast, the original query requires
   that _exists a_ relational expression `s` such that `s' =
   [ys/l2]s`, and the query is valid for this `s'` (see footnote#4).
   -->

The approach described above is more general than the
unification-based approach, as it relies on semantic equivalence
(decided via a solver) rather than syntactic equality. However, there
is still a significant level of syntactic flavour to the approach:

1. We assume that all relational expressions (hence opEqRHS) are in
   disjunctive normal form (DNF), which is a syntactic restriction.
   Our algorithm eliminates one ill-formed disjunct of the opEqRHS,
   while inferring one well-formed disjunct of the invariant in a
   single iteration.  Nevertheless, the DNF assumption is not
   restrictive if we stick to unions and cross products, as any
   relational expression constructed using only unions and cross
   products can be converted into DNF. 
2. Type inference uses opEq as a starting point, and reduces the task
   of inferring invariant to the task of eliminating ill-formed
   disjuncts from opEqRHS. This has some unpleasant consequences:
   1. Inference can only infer invariants having same or weaker
      top-level predicate as opEq. This means that if opEq is not
      actually an equality at the top-level, but a sub-set inclusion
      predicate, then inference will never infer an invariant that is
      an equality at the top-level.
   2. Ill-formed disjunct elimination is a syntactic manifestation of
      what we really want to achieve, namely _ill-formedness_
      elimination from opEqRHS. Both are equivalent if and only if the
      the invariants satisfy the grammar, and constraints satisfy the
      assumptions described in [this wiki][assumps]. Further, opEqRHS
      has to be consider only after constraint simplification has been
      carried out until the fixpoint is reached. If any of these
      conditions are not met, then ill-formed disjunct elimination
      becomes a conservative alternative to ill-formedness
      elimination.

To generalize the type inference algorithm and make it less fragile,
there is a need to eliminate assumptions about syntax of invariants,
constraints and functions. For instance, a less fragile version of
inference algorithm should be able to perform _ill-formedness_
elimination from opEqRHS without having to make assumptions about
syntax of constraints. We now present one such algorithm, called
`semantic_solve_1`, which starts with a well-formed underapproximation
of relational expression in opEqRHS, and gradually strengthens the
approximation until an equivalent well-formed expression is
discovered. The prefix `semantic_` in the name of the algorithm
denotes that algorithm tries to infer a well-formed expression that
is semantically equivalent to the ill-formed expression, regardless of
the syntax of the later. The suffix `_1` alludes to the conservative
_one disjunct at a time_ (or, _a hypothesis has to justify itself_)
strategy employed by the algorithm. A discussion on why this strategy
is conservative is presented in next section. The algorithm is shown
below:

    proc semantic_solve_1 (hypAcc, cs, opEqRHS as r U p*α, dom)
      if (cs ⊢ hypAcc = r) then
        return hypAcc;
      else if (isEmpty dom) then
              raise CantSolve
           else
              let hyps = {d ∈ dom | cs ⊢ ((r - hypAcc) ∩ d) ≠ {} Λ
                                    isComplete (cs,r,p) hyp Λ
                                    isStrong (cs,p) hyp}
              let hyp = oneOf hyps
              let dom' = dom - {hyp}
              let opEqRHS' = r U p(hyp) U p*α
              return semantic_solve_1 (hypAcc U hyp, cs, opEqRHS', dom');
           endif
      endif
    endproc

    proc isComplete (cs,r,p,hyp)
      return (cs ⊢ hyp ⊆ r U p(hyp));
    endproc

    proc isStrong (cs,p) hyp
      return (cs ⊢ p(hyp) ⊆ hyp);
    endproc

The procedure `semantic_solve_1` accepts:

+ A set of constraints `cs` (not necessarily equations),
+ RHS of the output equation, which is expected to be in the form `r U
  p*α`, where `r` denotes an ill-formed concrete relational
  expression, `p` denotes substitution function for pending
  substitutions, and `α` is simply a place holder for the unknown
  invariant (we are in the process of discovering α),
+ A set of valid relational abstractions of inputs (`dom`), and
+ `hypAcc`, the current well-formed underapproximation. The procedure
  is intented to be invoked with `hypAcc := {}`, since an empty set is
  the smallest well-formed underapproximation of any relational
  expression (hence, also `r`). 

The procedure returns when `hypAcc = r`, that is when the well-formed
underapproximation (`hypAcc`) becomes equivalent to ill-formed `r`.
Each iteration of the algorithm aims to reduce the gap between the
well-formed `hypAcc` and the ill-formed `r`. It does so by finding a
_strong_ and _complete_ `hyp ∈ dom` such that `cs ⊢ ((r - hypAcc) ∩
hyp) ≠ {}`, and making it the new hypothesis disjunct. This entails:

+ Adding `hyp` as a disjunct to adding to the `hypAcc` for the next
  iteration, and  
+ Adding `p(hyp)` as a disjunct to `r`, the ill-formed expression. 

First step is self-explanatory, as `hypAcc` is keeps track of
hypothesis disjuncts so far. But, why second step? As described
previously, α is the place-holder for the uknown relational expression
which we are in the process of inferring. When we hypothesize that a
certain `hyp` is a disjunct in the unknown expression, we effectively
conjecture that `α = hyp U α'`, which means `p*α = p(hyp) U p*α'`,
where `p(hyp)` applies pending substitutions in `hyp`. The resultant
concrete disjunct (`p(hyp)`) could be ill-formed, which is why we add
it to `r`. 

A hypothesis is said to be _complete_ if it is an underapproximation
of the ill-formed `r`. The reason why we call such a hypothesis
_complete_ (instead of, say, _legal_) will become apparent going
forward. A hypothesis is said to be _strong_ if also accounts for the
new (possibly ill-formed) disjunct (`p(hyp)`) added to `r` for next
iteration. 

We have previously mentioned that the gap between `hypAcc` and `r`
reduces in each iteration of the algorithm. We now prove this
progress (or liveness) condition. Let `hypAcc'` and `r'` be `hypAcc`
and `r` for next iteration (tail-recursive call) of the algorithm.
Then,

      r' - hypAcc'
    = (r U p(hyp)) - (hypAcc U hyp)
    = (r - (hypAcc U hyp)) U (p(hyp) - (hypAcc U hyp))
    = (r - (hypAcc U hyp)) U {}    /* Since hyp is strong */
    = (r - hypAcc) ∩ (r - hyp)     /* Simple rewriting */
    ⊆ (r - hypAcc)                 /* Since hyp is complete (i.e, underapproximation of r) */

We refer to the progress property of `semantic_solve_1` as _strong
progress_, which is the result of restricting ourselves to strong
hypothesis. 

The safety condition (or, the invariant) of the algorithm is that
`hypAcc` is an underapproximation of r.  We prove it by induction on
number of iterations of the algorithm. Intially, `hypAcc` is
empty-set, which is always a valid underapproximation. Lets assume
that after `i` iterations, `hypAcc` is still an underapproximation.
This means:

    hypAcc ⊆ r

In the `i+1`th iteration, `hypAcc' = hypAcc U hyp` and `r' = r U
p(hyp)`. Since `hypAcc ⊆ r`, we have that `hypAcc ⊆ r U p(hyp)`. It
remains to prove that `hyp ⊆ r U p(hyp)`, which follows directly from
the completeness property of `hyp`.

Limitations
-----------

Although the algorithm described by `semantic_solve_1` is simpler,
more general, and less fragile than the unification-based type
inference algorithm, it is still severely limited by its _one disjunct
at a time_ approach (manifest as _completeness_ condition), and
insistence on strong progress. The next section elaborates these
limitations through examples.

## From a single disjunct to a clique of disjuncts

Consider the following function named `alternate`:

     fun alternate l1 [] = l1
        | alternate [] l2 = l2
        | alternate (l1 as x::xs) l2 = 
            let
              val v = x::(alternate l2 xs)
            in
              v
            end

The function intersperses elements of `l1` and `l2` in the output
list. Hence, its relational dependent type should be inferred as the
following:

    alternate : l1 -> l2 -> {v | Rmem(v) = Rmem(l1) U Rmem(l2)}

The equational constraints resulting from the VC on `l1 = x::xs`
branch are shown below:

        Rmem(l1) = {(x)} U Rmem(xs)
        Rhd(l1) = {(x)}
        Rmem(v) = {(x)} U [l2/l1][xs/l2]α
      -----------------------------------
        Rmem(v) = α

The inference algorithm first tries to eliminate all ill-formed
disjuncts from opEqRHS. In this example, opEqRHS is `{(x)} U
[l2/l1][xs/l2]α`, and the only ill-formed disjunct is `{(x)}`. The
algorithm can unify this `{(x)}` with `{(x)}` in the RHS of the first
input equation, generating `Rmem(l1)` as the hypothesis. _Applying_
the hypothesis `Rmem(l1)` in α results in the new term `Rmem(l2)`. As
per our conservative (_a hypothesis has to justify itself_) approach,
the hypothesis `Rmem(l1)` is valid iff `Rmem(l1) = {(x)} U Rmem(l2)`.
Clearly, the later is invalid, thus invalidating the hypothesis that
`Rmem(l1)` is a disjunct in α (i.e., the invariant). In reality,
however, `Rmem(l1)` is indeed a disjunct in the invariant (see the
type of `alternate` above), demonstrating the limits of our
conservative approach.

The example demonstrates the need to generalize the inference
algorithm from _a hypothesis has to justify itself_ approach to a _a
clique of n hypotheses has to justify itself_ approach. Let us fix
`n=2` for the current example (we denote this as `n=2` approach). This
means that even if a hypothesis (hyp) could not justify itself, we do
not discard it. Instead, we look for a new hypothesis (hyp') such that
`hyp U hyp'` is _most likely_ to justify itself. How do we decide on
such a hyp'? by addressing the reason why hyp couldn't justify itself
in the first place . Let `hyp ⊆ re U psubsts*α` be the hypothesis
validation query, which we discharge in a conservative 2-step process
(see footnote #3). If the validation failed, then it could be due to
the failure of step 1 or step 2 or both:

1. In step 1 of two-step verification, if the check `hyp ⊆ re` fails,
   then new hypothesis (`hyp'`) better address the deficiency of 
   `hyp - re`. That is, `hyp'` should be selected such that `hyp U
   hyp' ⊆ re U psubsts(hyp')`. Since there are disjuncts that belong
   to `hyp`, but not to `re`, it must be the case that `hyp - re ⊆
   psubsts(hyp')`.  This suggests the property that `hyp'` should
   satisfy for it to be a valid joint hypothesis with `hyp`.
2. In step 2, if `psubsts(hyp) ⊆ hyp` fails, then the new hypothesis
   `hyp'` better be such that `psubsts(hyp) - hyp ⊆ hyp'`. 


Now, let us look at how `n=2` strategy works on the `alternate`
example. Let us start from where the weaker `n=1` strategy left. The
`n=1` strategy prematurely invaldiated the `Rmem(l1)` hypothesis
because `Rmem(l1) = {(x)} U Rmem(l2)` check failed. In contrast, `n=2`
strategy tries to find a new hypothesis which can validate the choice
of our earlier hypothesis. The new hypothesis should satisfy the
following necessary conditions:

1. hyp' should not be same as hyp.
2. `Rmem(l1) - ({(x)} U Rmem(l2)) ⊆ [l2/l1][xs/l2]hyp'`, and
3. `[l2/l1][xs/l2](Rmem(l1)) - Rmem(l1) ⊆  hyp'`, which simplifies to
   `Rmem(l2) - Rmem(l1) ⊆ hyp'`

The only hypothesis that satisfies above conditions is `Rmem(l2)`,
which we select as new hypothesis. The resultant clique of two
hypothesis is now validated using the check `Rmem(l1) U Rmem(l2) =
{(x)} U Rmem(l2) U Rmem(xs)`, which turns out to be valid.

How do we generalize this approach to any `n`? The algorithm is shown
below:

    proc solve (hypAcc, cs, opEqRHS as r U p*α, dom)
      if (cs ⊢ hypAcc = r) then 
        return hypAcc;
      else if (isEmpty dom) then raise CantSolve
           else
              let hyps = List.filter (dom, 
                  fn d => cs ⊢ ((r - hypAcc) ∩ d) ≠ {})
              let hyp = oneOf hyps
              let dom' = List.keepAll (dom, fn d => d ≠ hyp)
              let opEqRHS' = r U p(hyp) U p*α
              if isComplete (cs,r,p,hyp) then
                return solve (hypAcc U hyp, cs, opEqRHS', dom')
              else
                return completeHypAndSolve (hyp, hypAcc, cs, 
                                opEqRHS, dom')
              endif
           endif
      endif
    endproc

    proc completeHypAndSolve (hyp, hypAcc, cs, opEqRHS as r U p*α, dom)
      if (isEmpty dom) then
        raise CantSolve
      else
        let hyps' = List.filter (dom,
            fn d => cs ⊢ (hyp - (r U p(hyp)) ∩ d) ≠ {})
        let hyp' = oneOf hyps'
        let newHyp = hyp U hyp'
        let newDom = List.keepAll (dom, fn d => d ≠ hyp')
        if isComplete (cs,r,p,newHyp) then
          return solve (hypAcc U newHyp, cs, opEqRHS, newDom)
        else
          return completeHypAndSolve (newHyp, hypAcc, cs, 
                                  opEqRHS, newDom)
        endif
      endif
    endproc

    proc isComplete (cs,r,p,hyp)
      return (cs ⊢ hyp ⊆ r U p(hyp))
    endproc


Footnotes
---------

1. We say a relational expression `re` in disjunctive normal form
   (DNF) satisfies an obligation, which is also a DNF relational
   expression `re'`, if every disjunct in `re'` is also present in
   `re`.
2. In contrast, its invalidity does not mean that original query is
   invalid. In posteriority, we show how the counter-example from the
   failed query can be used to refine the hypothesis.
3. In reality, after applying the hypothesis (hyp), to check the
   validity of `hyp ⊆ re U α`, we don't simply check if `hyp = re`.
   This is because `re` may contain ill-formed disjuncts that we
   didn't account for when we generated hyp. Instead, we do a two step
   verification: In step 1, we check if `hyp ⊆ re`. If this check
   passes, we do step 2, where we collect all disjuncts (`δi`)
   different from `psubsts(hyp)` such that `δi ⊆ hyp`, and check if `hyp = ⋃(δi) psubsts()`. If both
   steps pass, we conclude that
   hyp is a valid hypothesis that could justify itself. We eliminate
   all `δi`s from `re` (call the resultant `re'`), and proceed to
   solve `re' U α`.

<!-- 3. Specifically, we ask the solver to find a model, where `¬(Rmem(l1)
   ⊆ {(x)} U Rmem(l1) U s')` is satisfiable. Unsat result from the
   solver implies that for all `s'`, it is the case that `Rmem(l1) ⊆
   {(x)} U Rmem(l1) U s'`. -->
4. If the query `Rmem(l1) ⊆ {(x)} U Rmem(l1) U s'` is SAT, and we get
   a model for `s'`, how can we use it?
4. The progress metric in hypotheses.


[assumps]: https://www.cs.purdue.edu/sss/projects/catalyst/2015/02/02/Inferring-Disjuncts-Intuition.html
[algo1]: https://www.cs.purdue.edu/sss/projects/catalyst/2015/02/02/Inferring-Disjuncts-Intuition.html
[algo2]: https://www.cs.purdue.edu/sss/projects/catalyst/2015/03/10/Extending-Unification.html
