---
layout: post
title:  "Extending Unification-based Inference to RelParams and ParamRels"
--- 

Unification-based inference has been proven to be quite effective in
inferring non-parametric relational refinements for first-order
examples. In this wiki, I describe how unification-based inference can
be extended to 

1. Parametric Relations, which could introduce relational parameters
   over types. and 
2. Higher-order functions, which necessarily rely on relational
   parameters.



## Parametric Relations

The grammar of type refinements with parametric relations is given
below:

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

Note that, although the grammar admits parametric relations, it does
not capture their full generality:

1. Relations cannot have multiple relational parameters. Only one is
   allowed. This restriction leads to no loss of generality in
   practice, as we never found the need to define relations with more
   than one parameters in Catalyst. 
2. Primitive relations can only be defined on one variable. This
   allows relations like `RId` and `RNull`, but disallows useful
   relations like `REq` and `RNeq`.
3. Syntactic class of $$Rexpr$$ admits neither set difference nor
   `IF-THEN-ELSE`. This, like the previous restriction, prevents us
   from defining useful primitive relations like `REq` and `RNeq`.
   Further, lack of `IF-THEN-ELSE` in both $$Rexpr$$ and $$\varphi$$,
   the syntactic class of type refinements, means that the type of
   `subst` function on lambda calculus terms cannot be expressed in
   this grammar.
4. There are no base predicates. Consequently, we cannot record the
   boolean predicate for `if-then-else` expressions while generating
   VCs. In short, VC generation is not path sensitive w.r.t
   `if-then-else` branching.

Apart from the above simplifying assumptions about the grammar of type
refinements, we also retain the assumptions we made
[previously][algo1] about the structure of functions we analyze. The
assumptions are reproduced below:

1. Functions are first-order.
2. There are no pre-conditions. That is, function inputs have trivial
   type refinements.
3. We assume that the return value of a function/constructor
   application is never pattern-matched.
4. Any variable (including function arguments) is bound only once.
   Further, we assume that there are no duplicate pattern matches; for
   e.g., a list `l` is never destructed twice along the same path. 

We make the above simplifying assumptions to focus on the core problem
of inference without having to deal with too many details. We shall
try to relax these restrictions going forward.

We now demonstrate that, under the aforementioned simplifying
assumptions, inference algorithm for parameteric case is a
straightforward extension of unification-based inference algorithm for
non-parametric case.

The zip example
---------------

We will use the following `zip` function as our running example:

    fun zip [] [] = []
      | zip (x::xs) (y::ys) = 
          let
            val xys = zip xs ys
            val xy = (x,y)
            val v = xy::xys
          in
            v
          end 

Let us assume that we have the parametric versions of the `Rmem` and
`Rhd` relations defined over lists:

    Rhd[R](x::xs) = R(x);
    Rmem[R] = (Rhd[R])*;

Further, assume that following parametric relations are defined over
the pair type (we consider SML's `(x,y)` representation as syntactic
sugar for `Pair (x,y)`. Therefore, relations on pairs are also
structural relations; not primitive relations):

    Rfst[R](x,y) = R(x);
    Rsnd[R](x,y) = R(y);

Let us consider the following type template of `zip` for the inference
problem:

    zip : l1 -> l2 -> {v | ??}

Succesfull inference should result in, for example, the following
dependent type:

    ('R) zip : l1 -> l2 -> {v | Rmem[Rfst['R]](v) = Rmem['R](l1) /\
                                Rmem[Rsnd['R]](v) = Rmem['R](l2)}

The inference process starts by refining the single hole in the type
template of `zip` with multiple holes, one for each relational
abstraction of the return type, namely `'a list`. For the sake of this
discussion, we ignore the `Rhd` abstraction and present only the
`Rmem` holes (we denote such holes as α1, α2, ..):

    zip : l1 -> l2 -> {v | Rmem[Rfst['Ra]](v) = α1 /\ 
                           Rmem[Rsnd['Rb]](v) = α2}

Relations `'Ra` and `'Rb` in the above type denote unknown relational
abstractions over the types `'a` and `'b`, respectively. If `'Ra` and
`'Rb` remain free in the final type of `zip`, they will be
generalized. 

The type inference problem now reduces to finding suitable relational
expressions to substitute for α1 and α2. Note that alphas needs to be
well-formed under env containing ML type bindings of `l1`, `l2` and
`v`:

$$
    l1:{\sf 'a\, list};\,l2:{\sf 'b\, list};\,v:{\sf 'a*'b\, list}
    \;{\vdash}_{wf}\; \alpha_1,\,\alpha_2
$$

The VC from the `x::xs y::ys` branch of `zip` is shown below
(simplfied for clarity):

        Rmem['R1](l1) = 'R1(x) U Rmem['R1](xs)
        Rhd['R2](l1) = 'R2(x)
        Rmem['R3](l2) = 'R3(y) U Rmem['R3](ys)
        Rhd['R4](l2) = 'R4(y)
        Rfst['R5](xy) = 'R5(x)
        Rsnd['R6](xy) = 'R6(y)
        Rmem[Rfst['Ra]](xys) = [xs/l1][ys/l2]α1
        Rmem[Rsnd['Rb]](xys) = [xs/l1][ys/l2]α2
        Rmem[Rfst['Ra]](v) = Rfst['Ra](xy) U Rmem[Rfst['Ra]](xys)
        Rmem[Rsnd['Rb]](v) = Rfst['Rb](xy) U Rmem[Rfst['Rb]](xys)
     =>
        Rmem[Rfst['Ra]](v) = α1
        Rmem[Rsnd['Rb]](v) = α2

Like the VCs from the non-parametric case (algorithm for
non-parametric case is described in [this][algo1] wiki), the above VC
can be represented as the following constraint system with α1 and α2
as unknowns:

    Equational Constraints
    -------------------------

        Rmem['R1](l1) = 'R1(x) U Rmem['R1](xs)
        Rhd['R2](l1) = 'R2(x)
        Rmem['R3](l2) = 'R3(y) U Rmem['R3](ys)
        Rhd['R4](l2) = 'R4(y)
        Rfst['R5](xy) = 'R5(x)
        Rsnd['R6](xy) = 'R6(y)
        Rmem[Rfst['Ra]](v) = Rfst['Ra](xy) U [xs/l1][ys/l2]α1
        Rmem[Rsnd['Rb]](v) = Rfst['Rb](xy) U [xs/l1][ys/l2]α2

    Well-Formedness Constraints
    -----------------------------
        l1:'a list; l2:'b list ⊢ α1
        l1:'a list; l2:'b list ⊢ α2
    
As with the non-parametric case, we solve constraints for one unknown
at a time. Let us first consider equations for α1, categorized as
_input equations_, _intermediary equations_, and _output equations_
(this terminology is retained from the [previous wiki][algo1]).

    Equational Constraints
    -------------------------
      Input Equations:
        Rmem['R1](l1) = 'R1(x) U Rmem['R1](xs)
        Rhd['R2](l1) = 'R2(x)
        Rmem['R3](l2) = 'R3(y) U Rmem['R3](ys)
        Rhd['R4](l2) = 'R4(y)
      Intermediary Equations:
        Rfst['R5](xy) = 'R5(x)
        Rsnd['R6](xy) = 'R6(y)
      Output Equation:
        Rmem[Rfst['Ra]](v) = Rfst['Ra](xy) U [xs/l1][ys/l2]α1

    Well-Formedness Constraints
    -----------------------------
        l1:'a list; l2:'b list ⊢ α1

Proceeding similar to the non-parametric case, first step is
constraint simplification, which eliminates intermediary equations.
Each intermediary equation of form `ρ(x) = e` becomes a substitution
`[e/ρ(x)]`, which then needs to be applied to input, output, and rest of
the intermediary equations. However, applying a substitution is not
straightforward, as `ρ(x)` and `e` can contain free relational
variables which need to be instantiated. For example, the intermediary
equation `Rfst['R5](xy) = 'R5(x)` leads to the substitution
`['R5(x)/Rfst['R5](xy)]`, which has `'R5` as a free relational
variable. When applying this substitution to the term `Rfst['Ra](xy)`,
`'R5` gets instantiated with `'Ra` to yeild `'Ra(x)` as the result of
the substitution. Unification also proceeds similarly: two relational
expressions can be unified iff there exists a substitution for their
free relational variables such that resultant expressions are
equivalent.

After constraint simplification, we will have the following constraint
system:

    Equational Constraints
    -------------------------
      Input Equations:
        Rmem['R1](l1) = 'R1(x) U Rmem['R1](xs)
        Rhd['R2](l1) = 'R2(x)
        Rmem['R3](l2) = 'R3(y) U Rmem['R3](ys)
        Rhd['R4](l2) = 'R4(y)
      Output Equation:
        Rmem[Rfst['Ra]](v) = 'Ra(x) U [xs/l1][ys/l2]α1

    Well-Formedness Constraints
    -----------------------------
        l1:'a list; l2:'b list; ⊢ α1

We call the RHS of output equation as opEqRHS. An ill-formed disjunct
in opEqRHS is a disjunct that violates the well-formedness constraint
stated above. Observe that if opEqRHS contains only well-formed
disjuncts, and does not contain the unknown α1, then the output
equation _is_ the invariant we wished to infer. Therefore, the aim of
constraint solving is to eliminate all ill-formed disjuncts and the
unknown α1 from the output equation, in favour of well-formed ones.

Second step in constraint solving is the unification of ill-formed
disjuncts in opEqRHS with RHS of input equations. The only
(ill-formed) disjunct in opEqRHS is `'Ra(x)`, which unifies with
disjuncts `'R1(x)` and `'R2(x)` (both relation variables need to be
instantiated with `'Ra`) in the RHS of first and second input
equations, respectively.  The corresponding hypotheses are
`Rmem['Ra](l1)` and `Rhd['Ra](l1)`, and obligations are
`Rmem['Ra](xs)` and `{()}`, respectively. Since a hypothesis is also
valid for the recursive call, it needs to be instantiated as a
disjunct in the invariant of the recursive call as well (recall that
recursive call invariant is captured by `[xs/l1][ys/l2]α1`).
Instantiating hypotheses in recursive call invariant leads to
following output equations:

1. `Rmem[Rfst['Ra]](v) = 'Ra(x) U Rmem['Ra](xs) U [xs/l1][ys/l2]α1`,
   when the hypothesis is `Rmem['Ra](l1)`, and
2. `Rmem[Rfst['Ra]](v) = 'Ra(x) U Rhd['Ra](xs) U [xs/l1][ys/l2]α1`,
   when the hypothesis is `Rhd['Ra](l1)`

The obligation for the second hypothesis is the trivial empty-set,
which can be readily satisfied. However, the newly generated disjunct
after instanting hypothesis in α1 (i.e, `Rhd['Ra](xs)`) cannot be
unified with any disjuncts of input equations. Hence, second
hypothesis is considered to be invalid, and discarded.

The obligation for the first hypothesis (`Rmem['Ra](xs)`) is same as
the new disjunct generated after instanting hypothesis in α1. Hence,
the obligation is discharged. The resultant output equations is:

      Rmem[Rfst['Ra]](v) = Rmem['Ra](l1) U [xs/l1][ys/l2]α1
    
Observe that opEqRHS contains no further ill-formed disjuncts. Hence
`Rmem['Ra](l1)` is a valid hypothesis.

We now proceed with the last step of constraint solving, which is the
elimination of `[xs/l1][ys/l2]α1` from opEqRHS. Well-formedness
constraint dictates that α1 can only refer to `l1` and `l2`, which
means that its disjuncts can only be relational abstractions of either
`l1` or `l2`.  However, any such disjunct invariably becomes an
ill-formed disjunct in opEqRHS after applying pending substitutions
`[xs/l1][ys/l2]`. Hence, the only candidate for α1 is the trivial
empty-set. 

The result of constraint solving is the following _likely invariant_
for `zip`:

      Rmem[Rfst['Ra]](v) = Rmem['Ra](l1)

The adjective _likely_ is dropped when this invariant is also
confirmed by the base case (`l1=[] l2=[]`) branch of `zip`. Constraint
solving for the other unknown (α2), and also for the VC generated on
the base case branch is very similar to the process described above.
At the end of constraint solving on all branches, we infer both the
invaraints of `zip`, resulting in the following type:

    ('Ra,'Rb) zip : l1 -> l2 -> {v | Rmem[Rfst['Ra]](v) = Rmem['Ra](l1) /\
                                     Rmem[Rsnd['Rb]](v) = Rmem['Rb](l2)}


Conclusion
-----------

The `zip` example demonstrates that the unification-based inference
algorithm that we built for non-parametric case, extends
straightforwardly for the parametric case in the absence of (a).
higher-order functions, and (b). base predicates resulting from
`if-then-else` expressions.


## Higher-Order Functions

In this section, I describe how parametric type inference can be
extended to higher-order functions.

The map Example
---------------

Consider the map function:

    fun map [] f = []
      | map (x::xs) f = 
          let
            val x' = f x
            val xs' = map xs f
            val v = x'::xs'
          in
            v
          end

Let us consider the following type template of `map` for the inference
problem:

    map : l -> (f: z -> {z' | ??}) -> {v | ??}

Succesfull inference should result in the following dependent type:

    ('R1,'R2) map : l -> (f: z -> {z' | 'R2(z') = 'R1(z)}) 
                            -> {v | Rmem['R2](v) = Rmem['R1](l)}

The inference process starts by refining the single hole in the type
template of map with multiple holes, one for each relational
abstraction of the return type. For the return type of map (namely,
`'a list`), we consider `Rmem` relational abstraction. We ignore `Rhd`
since it is not particularly interesting. The return type of the
higher-order argument (`f`) to map is a type variable (`'b`), for
which no pre-defined abstractions exist. Therefore, we introduce a new
relation variable (call it `'Rb1`) to represent the unknown relational
abstraction of interest for `'b` type. The type template of map after
refining holes is shown below: 

     map : l -> (f: z -> {z' | 'Rb1(z') = β}) 
                            -> {v | Rmem['Rb2](v) = α}

Relations `'Rb1` and `'Rb2` in the above type denote unknown (possibly
distinct) relational abstractions over the type `'b`.  If `'Rb1` and
`'Rb2` remain free in the final type of map, they will be generalized. 

The type inference problem now reduces to finding suitable relational
expressions to substitute for α and β. Note that alpha needs to be
well-formed under env containing ML type binding of `l`:

$$
    l:{\sf 'a\, list} \;{\vdash}_{wf}\; \alpha
$$
    
Likewise, beta needs to be well-formed under bindings for `l` and `z`:

$$
    l:{\sf 'a\, list};\, z:{\sf 'a} \;{\vdash}_{wf}\; \beta
$$

The VC on `x::xs` branch is shown below (simplified for clarity):

        Rmem['R1](l) = 'R1(x) U Rmem['R1](xs)
        Rhd['R2](l) = 'R2(x)
        'Rb1(x') = [x/z][x'/z']β
        Rmem['R1](xs') = [xs/l]α
        Rmem['Rb2](v) = 'Rb2(x') U Rmem['Rb2](xs')
     =>
        Rmem['Rb2](v) = α  

Like the VCs from the non-parametric case (algorithm for
non-parametric case is described in [this][algo1] wiki), the above VC
can be represented as the following constraint system with α and β
as unknowns:

    Equational Constraints
    -------------------------

        Rmem['R1](l) = 'R1(x) U Rmem['R1](xs)
        Rhd['R2](l) = 'R2(x)
        'Rb1(x') = [x/z][x'/z']β
        Rmem['Rb2](v) = 'Rb2(x') U [xs/l]α

    Well-Formedness Constraints
    -----------------------------
        l:'a list ⊢ α
        l:'a list; z:'a ⊢ β

Unlike the non-parametric and parametric examples seen so far, unkowns
α and β do not stand for two orthogonal relational expressions in the
return type of map. Therefore, they cannot be solved separately. For a
given solution of α, the solution for β should be a relational
expression that is just strong enough to ensure α. This tells us that
the solutions to the constraint system described above are pairs of
`(α,β)`.

Let us categorize equations as _input_, _intermediary_ and _output_
equations, respectively:
 
    Equational Constraints
    -------------------------

      Input Equations:
        Rmem['R1](l) = 'R1(x) U Rmem['R1](xs)
        Rhd['R2](l) = 'R2(x)
      Intermediary Equations:
        'Rb1(x') = [x/z][x'/z']β
      Output Equations:
        Rmem['Rb2](v) = 'Rb2(x') U [xs/l]α

    Well-Formedness Constraints
    -----------------------------
        l:'a list ⊢ α
        l:'a list; z:'a ⊢ β

First step of constraint solving is constraint simplification. We have
one intermediary equation, which we would like to eliminate. We
therefore carry out the substitution of `[[x/z][x'/z']β / 'Rb1(x')]`
in both input and output equations. Observe that substitution has
`'Rb1` as free variable. As described previously, this free relational
variable has to be instantiated before substitution is carried out.
This instantiation happens once in output equation, where `'Rb1` is
instantiated with `'Rb2`. Note that `'Rb1` cannot be instantiated with
`'R1` or `'R2` for substitution in input equations because of the sort
mismatch.

The resultant equations after constraint simplification are shown:

    Equational Constraints
    -------------------------

      Input Equations:
        Rmem['R1](l) = 'R1(x) U Rmem['R1](xs)
        Rhd['R2](l) = 'R2(x)
      Output Equations:
        Rmem['Rb2](v) = [x/z][x'/z']β U [xs/l]α

    Well-Formedness Constraints
    -----------------------------
        l:'a list ⊢ α
        l:'a list; z:'a ⊢ β

As usual, we name the RHS of output equation, i.e., `[x/z][x'/z']β U
[xs/l]α` as opEqRHS. Second step of constraint solving is the
unification of ill-formed disjuncts in opEqRHS with disjucts in RHS of
input equations (or their cross products). Unfortunately, we now don't
have any concrete disjuncts in opEqRHS to unify. We only have a beta
and an alpha. How do we proceed?

We can conceive a way forward if we recollect that β just needs to be
strong enough to let us describe output relational abstractions in
terms of inputs. We therefore instantiate β with approriate disjuncts
such that (a). they satisfy the well-formedness constraint on β, and
(b). the resultant disjuncts in opEqRHS, after applying pending
substitutions on β, are unifiable with disjuncts in input equations.
To find an appropriate disjunct to instantiate β, we take an input
disjunct, apply inverse of β's pending substitutions on the disjunct,
and check if the resulant disjunct (δ) satisfies well-formedness
constraint on β. If it does, then we replace `pending-substitutions *
β` with `δ U pending-substitutions*β`. We now have a concrete
constraint (δ) to make progress.

For example, in case of above constraint system, we can find an
appropriate disjunct (δ) for β by applying inverse of pending subts,
which is `[z/x][z'/x']` on a disjunct of the inputs, and then testing
if its free vars are in `{z,l}`. One such disjunct is `'R1(x)`, which
gives `'R1(z)` as δ. The resultant opEqRHS is `'R1(x) U [x/z][x'/z']β
U [xs/l]α`. Now, unification proceeds as usual:

+ `'R1(x)` is unified with `'R1(x)` in the RHS of first input
  equation. `Rmem['R1](l)` and `Rmem['R1](xs)` are generated as
  hypothesis and obligation, respectively.
+ The hypothesis is _applied_ to alpha (since it is also valid for the
  recursive call), to get `Rmem['R1](xs)` as the new disjunct. The
  resultant opEqRHS is `'R1(x) U [x/z][x'/z']β U Rmem['R1](xs) U
  [xs/l]α`. 
+ The obligation can be now be unified with newly generated disjunct.
  This means that unification with first input equation has succeeded,
  and we can now replace `'R1(x) U Rmem['R1]` in opEqRHS with
  `Rmem['R1](l)`, which is the LHS of first input equation.

In the last step above, what if the obligation cannot be satisfied by
the newly generated disjunct? In such case, the only option available
is to check if we can strengthen β (thereby making more assumptions
about the higher-order argument) to satisfy the obligation. Here, this
amounts to checking if `[z/x][z'/z']Rmem['R1](xs)]` is well-formed
under `l:'a list; z:'a` constraints of β. In this case, it does not.
Hence, the hypothesis would've been invalidated due to unsatisfied
obligations.

We repeat this process of hypothesizing about β, once for every input
equation of appropriate sort. Each successful unification with an
input equation adds one _independently nullable_ disjunct to β. An
_independently nullable_ disjunct can be instantiatied to an empty set
without constraining the instantiations of other disjuncts. Hence,
addition of an independently nullable disjunct does not amount to
strengethening β, or making more assumptions about the higher-order
argument. In contrast, the disjunct added to β to fulfill unification
obligation is not independently nullable; it is only _jointly
nullable_ with a previously added disjunct in β. Addition of jointly
nullable disjuncts amounts to strengthening β, which is equivalent to
making more assumptions about the higher-order argument. The aim of
constraint solving is to **maximize the number of independently
nullable disjuncts, and minimize the number of jointly nullable
disjuncts** in β. For the current example, there are no independently
nullable disjuncts other than `'R1(z)`. Hence we conclude that
`'R1(z)` is the solution for β. 

Once we have added all possible independently nullable disjuncts to
β, we replace the β term with an empty-set in opEqRHS, and proceed to
eliminate α. Elimination of alpha is same as how it was done
previously. In the current example, the possible disjunct that can
eliminate α happens to be the trivial empty-set. Consequently, we
derive `Rmem['Rb2](v) = Rmem['R1](l)` as a likely invariant of map.
The VC from `l = []` branch also confirms this invariant, making it
the final invariant of map. Recollecting that `'Rb1` has been
unified with `'Rb2` during constraint simplification, the resultant
type of map without holes is:

     ('R1,'Rb2) map : l -> (f: z -> {z' | 'Rb2(z') = 'R1(z)}) 
                            -> {v | Rmem['Rb2](v) = Rmem['R1](l)}

foldr example
-------------

Oftentimes, alphas and betas in equations can be entangled in the sense
that one could appear in other's pending substitutions. This is a
fairly common scenario, and happens when the higher-order argument is
applied to the result of the recursive call, or vice-versa. The
function `foldl` is one such example. The definition is shown below:

    fun foldr [] b f = b
      | foldr (x::xs) b f = 
          let
            val acc = foldr xs b f 
            val v = f x acc
          in
            v
          end

We will now demonstrate that the approach that was successful in
inferring the type of map, also works for `foldr`.

Let us consider the following type template of `foldr` for the
inference problem:

    foldr : l -> b -> (f: v0 -> v1 -> {v2 | ??}) -> {v3 | ??}

Succesfull inference should result in a dependent type that is atleast
as strong as the following type:

    ('R1,'R2) foldr : l -> b -> (f: v0 -> v1 -> {v2 | 'R2(v2) = 'R1(v0) U 'R2(v1)}) 
                             -> {v3 | 'R2(v3) = Rmem['R1](l) U 'R2(b)}

After refining holes, we get:

     foldr : l -> b -> (f: v0 -> v1 -> {v2 | 'Rb1(v2) = β}) 
                             -> {v3 | 'Rb2(v3) = α}

The type inference problem now reduces to finding suitable relational
expressions to substitute for α and β. Note that alpha needs to be
well-formed under env containing ML type bindings of `l` and `b`:

$$
    l:{\sf 'a\, list};\,b:{\sf 'b} \;{\vdash}_{wf}\; \alpha
$$
    
Likewise, beta needs to be well-formed under bindings for `l`, `b`,
`v0` and `v1`:

$$
    l:{\sf 'a\, list};\, b:{\sf 'b};\, v0:{\sf 'a};\, v1:{\sf 'b} 
      \;{\vdash}_{wf}\; \beta
$$

The VC on `x::xs` branch is shown below (simplified for clarity):

        Rmem['R1](l) = 'R1(x) U Rmem['R1](xs)
        Rhd['R2](l) = 'R2(x)
        'Rb2(acc) = [xs/l]α
        'Rb1(v) = [x/v0][acc/v1]β
     =>
        'Rb2(v) = α  

Like the VCs from the non-parametric case (algorithm for
non-parametric case is described in [this][algo1] wiki), the above VC
can be represented as the following constraint system with α and β
as unknowns:


[algo1]: https://www.cs.purdue.edu/sss/projects/catalyst/2015/02/02/Inferring-Disjuncts-Intuition.html
