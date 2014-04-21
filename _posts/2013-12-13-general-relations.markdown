---
layout: post
title:  "General Relations"
date:   2013-12-10 10:23:41
--- 
Generalizing Structural Relations
---------------------------------
So far, we have been using structural relations to map data structures
, such as lists, trees, abstract syntax etc., to relational domain.
Our structural relations are first-order, since they are only indexed
by terms of recursive datatypes. In this document, we are going to
describe generalized structural relations, which extend structural
relations by 1. Allowing them be parametrized over other relations
(parametric relations, but not higher-order relations. We do not let
relations to return relations), 2. Defining relations by
pattern-matching over terms of non-algebraic datatypes (viz., pairs,
records, or even variables), and 3. Adding intersection and difference
operations over relational expressions (This is not very significant
addition).  We argue that we achieve this generality without losing
decidability of type checking by sketching an encoding of language of
verification conditions in the language of decidable logic.The primary
motivation of this exercise is to make the structural relations
framework general enough to accommodate most of EUFA relations, and
powerful enough to assign very general types (not principal types,
unfortunately) to most higher-order functions. The eventual goal is to
meet the MLton SSA pass benchmark.  

In this document, we only present examples of utility of such
generalized relations. Last example in this series is a relatively
advanced exercise in verification of alpha-renaming operation over
untyped lambda calculus terms. This example can serve as an
intermediary benchmark before we are ready for MLton SSA.  

## 1. Examples ##

### 1.1 zip ###

Consider the zip function over lists, with following type:

    zip : 'a list -> 'b list -> ('a*'b) list

How do we assert that elements of resultant list are pairs of elements
from both argument lists? In the current implementation of catalyst,
we cannot make such an assertion. Recall that we have considered such
examples while trying to type MLton remove-unused pass, and conceived
a "map-fold" based solution, which was somewhat unweildy. This problem
can be overcome, by generalizing the Rmem relation, which is currently
defined as:

    relation Rhd (x::xs) = {(x)};
    relation Rmem = Rhd*;

By parametrizing it over ('a * 'b) relation Rx:

    relation Rhd Rx (x::xs) = Rx(x);
    relation Rmem Rx = (Rhd Rx)*;

The semantics of parametrized relation Rhd is apparent in its
following elaboration: 

    ΛT. λRx : {'a * T} relation.  (Rhd Rx) (x::xs) = Rx (x)

Futher elaboration:

    forall (T : type), (Rx : {'a * T} relation), let R denote the
    relation (Rhd Rx). Then,
    forall x : 'a, xs: 'a list, y : T, 
    R(x::xs, y) <=> Rx (x,y)

With help of parametrized relations Rhd and Rmem, and few auxiliary
relations defined below:

    relation RId (x) = {(x)}
    relation Rfst R (x,y) = R(x)
    relation Rsnd R (x,y) = R(y)

zip can be assigned following type:

    zip : l1 -> l2 -> {l | (Rmem (Rfst RId))(l) = (Rmem RId)(l1) /\ 
                       (Rmem (Rsnd RId))(l) = (Rmem RId)(l2)}

### 1.2 map and fold ###

Similar to Rhd and Rmem, parametrized occurs-before relation can be
defined as :

    relation Rob Rx (x::xs) = Rx(x) X (Rmem Rx)(xs);
    relation Robs Rx = (Rob Rx)*;

With help of parametrized relations, higher-order map function can be
assigned following expressive type:

    Abstract ('Ra,'Rb) in
    map : l -> (f : x -> {y | 'Rb(y) = 'Ra(x)}) -> 
            {l' | (Robs 'Rb)(l') = (Robs 'Ra)(l)}

Observe that we have instantiated parametrized abstract relations with
abstract relations 'Ra and 'Rb in the above type. Similarly, the type
of fold function (from APLAS draft and HOPA talk) can be extended with
parametric relations as following:

    Abstract ('R1, 'R2, 'r) in
    fold : l -> b -> {f : x -> acc-> {z | 'R1(z) = 'r(x) U 'R1(acc) /\ 
                                          'R2(z) = ('r(x) X 'R1(acc)) U 'R2(acc)}} 
           -> {z | 'R1(z) = (Rmem 'r)(l) U 'R1(b) /\
                   'R2(z) = (Rob 'r)* (l1) U 'R2(b) U ('R1(z) X 'R1(b)}

Observe that above type of fold is parametrized over three abstract
relations against previous two. The third parameter ('r) is a result
of parametrizing list relations themselves. Nevertheless, intuition
behind the type remains the same as previous.

### 1.3 First-order List.exists ###

Consider the first order List.exists function for string lists with
following type:

    List.exists : {l : string list} -> {k : string} -> {z : bool}

The function returns true if and only if string k is present in the
list l. The following type captures this invariant:

    List.exists : {l : string list} -> {k : string} -> 
                    {z : bool | z=true <=> {k} ⊆ Rmem(l)}

However, special provision has to be made for boolean datatype to
accommodate such types.  To see why, observe that the post-condition
(z=true <=> {k} ⊆ Rmem(l)) is a meta-theoretic assertion for both
theories of propositional logic with equality, and structural
relations (theory of equality and sub-set inclusion predicates over
relational expressions). This special provision is odd considering the
fact that true and false are nullary value constructors similar to
Nil, and we never encountered such case with list functions.

The problem lies in inability to construct any useful structural
relation for boolean datatype (or any type with only nullary
constructors) as pattern matching on constructors does not introduce
any variables in to scope. With parametric relations, this is no
longer the case. Consider the following relation on bools:

    relation Rbool R (true) = R | (false) = {()};

Rbool relation is parametrized over relation R. (Note that R is
necessarily a ground relational term (i.e., a relational expression
similar to {(x)}) owing to the restriction that parametric relations
are not higher-order relations). Due to the above definition, we
generate following types for true and false:

    true : {v : bool | ΛT. λR : {T} relation. (Rbool R)(v) = R}
    false : {v : bool | ΛT. λR : {T} relation. (Rbool R)(v) = {()}}

With help of Rbool and few auxiliary relations defined below,
List.exists can be assigned a precise type:

    relation Rk r (x) = r - (r - {x});

    listexists : l -> k -> {z : bool | Rbool {(k)} (z) = Rmem (Rk {(k)}) (l)}

To understand the post condition, first observe that LHS of assertion
is singleton {(k)} when z is true, and empty set {()} when z is false.
Let R denote the relation Rk, where its parameter r is instantiated
with ground term {(k)}. (i.e., R = Rk {(k)}). Observe that:

    R(x) = {(k)}, whenver x=k, and
         = {()}, otherwise.

Recall that for any relation R, 

    Rmem R (x::xs) = R(x) U (Rmem R)(xs)

Consequently, RHS of assertion, which is equivalent to ((Rmem R) (l)),
evaluates to {(k)}, if there exists an element in list which is equal
to k. Otherwise, it evaluates to empty set {()}. Putting everything
together, the post-condition expresses the fact that z is true if and
only if k exists in the list.

Now, let us consider an example where this type proves to be very
useful. Function addk adds k to list l if and only if it is not
already present in the list:


{% highlight ocaml %}
fun addk l k = 
  let
    val v = List.exists l k 
  in
    case v of 
      true => l
    | false => k::l
  end
{% endhighlight %}

We would like to assert that k is always present in the result list
(Note that (Rmem RId) has same behaviour as unparametrized Rmem):

    addk : l -> k -> {l' | {(k)} ⊆ (Rmem RId)(l')}

Informally, here is how the type is checked. Recall the types of true
and false constructors:

    true : {v : bool | ΛT. λR : {T} relation. (Rbool R)(v) = R}
    false : {v : bool | ΛT. λR : {T} relation. (Rbool R)(v) = {()}}

After instantiating T with string and R with {(k)}, we have

    true : {v : bool | (Rbool {(k)})(v) = {(k)} }
    false : {v : bool | (Rbool {(k)})(v) = {()} }

In the true branch, we therefore have 

    (Rbool {(k)})(v) = {(k)}  --- 1

From the return type of List.exists, we also have that

    Rbool {(k)} (z) = Rmem (Rk {(k)}) (l) --- 2

From 1 and 2,

    {(k)} = Rmem (Rk {(k)}) (l)

This means that there exists atleast one x:'a such that
Rmem (l,x) and x=k. This is precisely what post-condition asserts.

For false branch, type-checking is trivial as k is explicitly cons'ed
to l to create l'. Therefore l' trivially contains k.

### 1.4 Higher-order List.exists ###

We now demonstrate type of List.exists can be generalized to
higher-order case. Higher-order List.exists (henceforth referred to as
just List.exists) has the following ML type:

    List.exists : 'a list -> ('a -> bool) -> bool

Retaining the definition of Rbool from first-order case, we ascribe
following relational type to List.exists:

    Abstract ('R2,'r) in
    List.exists : l -> (f : {x:'a} -> {v : bool | (Rbool 'r)(v) = 'R2(x)} )
        -> {z : bool | (Rbool 'r)(z) = (Rmem 'R2)(l)}

Note that, when typing List.exists under the context Γ, 'R2 and 'r
must be well-formed relations under Γ extended with type of l. That
is,

    Γ, l ↦ 'a list ⊢ r : {T₁} relation
    Γ, l ↦ 'a list ⊢ 'R2 : {'a*T₁} relation

Instantiating 'a with string, 'r with {(k)} (assume k is in scope at
call-site of List.exists.), and 'R2 with (Rk {(k)}) will give us the
first-order case (from section 1.3). That is, it gives us List.exists,
which takes a function f that returns true if and only if its argument
(x : string) is equal to k. List.exists will then return true if and
only if there exists atleast one x:string in l : string list, such
that x = k. 

However, List.exists is more general. Consider a relations Rk2 and R'
defined below:

    relation Rk2 r (x) = (r - {x});
    relation R' = Rk2 {(k)}; (* Assume k:string is in scope here. This
                          relation is only to make presentation easy. *)
    relation Rmemk = (Rmem R');

Observe that 

    R' (x) = {()}, whenever x = k, and
           = {(k)}, otherwise.

That is, R' is semantic inverse of relation R defined in section 1.3.
Therefore, a function notk from string to bool that returns true iff and
only if its argument is NOT equal to k can be assigned following type:

    notk : {x: string} -> {v : bool | (Rbool {(k)}) (v) = R'(x)}

Now, instantiating 'a with string, 'r with {(k)}, and 'R2 with R', we
get a List.exists that accepts notk as argument and returns z:bool,
where z is true if and only if there exists x:string in l such that 
x ≠ k. 

Based on these observations, we argue that type of higher-order
List.exists is general enough for most practical uses.

### 1.5 Capture-avoiding substitution & Alpha-renaming ###

We now switch gears and demonstrate how to utilize relational types to
assert safety properties of alpha-renaming operation over expressions
of untyped lambda calculus. Although we may not be able to assert full
functional correctness, we can describe and verify such properties
that help preclude commonly occuring erratic behaviours. This
benchmark is particularly significant in the context of alpha-renaming
being notoriously error-prone. For the sake of this example, we use
untyped LC implementation from
https://github.com/gowthamk/Lambda/blob/master/gadts/untyped.sml.

Alpha renaming is a transformation of lambda term (e), where the bound
variable (v), and all its bound occurrances are consistently renamed.
Alpha renaming relies on capture-avoiding substitution operation,
which is also used to perform beta reduction. Enough care has to be
taken to avoid following subtle errors while implementing alpha
renaming and substitution:

1. Occurances of bound variable with same name, but introduced by a
different binder should not be renamed. For eg:

    λx.(x y λx.x) ≢ λz.(z y λx.z)

2. Conversely, renaming should not let bound occurance to be captured 
by different binder. For eg:

    λz.(z y λx.(z x)) ≢ λx.(x y λx.(x x))

3. Renaming should not capture free variables. For eg:

    λx.(x y λz.z) ≢ λy.(y y λz.z)

It should be observed that all erratic behaviours described above can
be precluded if alpha renaming preserves set (bag, to be precise) of
free variables at every lambda sub-expression occuring within the
given lambda expression. However, we will only attempt to verify that
alpha-renaming preserves set of free variables in the given lambda
expression, which is a weaker property than that is required for full
functional correctness. Nevertheless, considering that alpha renaming
is usually implemented recursively, and erratic implementations rename
either all occurances of a variable under a given scope, or none of
them, we argue that this is sufficient to capture aforementioned bugs.
We demonstrate this observation with help of examples at the end of
this section.

To verify implementation of alpha-renaming and subst, we first define
free-variable relation over untyped LC AST.

    relation Rfv (Var x) = {(x)} | (App (e1,e2)) = Rfv(e1) U Rfv(e2)
              | (Abs (id,e)) = Rfv(e) - {(id)}

Next, we assert that function freeVars has following type:

    freeVars : {e : exp} -> {l : id list | Rmem(l) = Rfv(e)};

Typechecking freeVars requires the type of higher-order List.filter to
be general enough. This is not a problem as List.filter can be
typed in similar way as higher-order List.exists from previous
sections.

Next, we ascribe following types to alphaConvert and subst functions:

    alphaConvert : {e : exp} -> {e' : exp | Rfv(e') = Rfv(e) }
    subst : {e1 : exp} -> {id : id} -> {e2 : exp}
        -> {e2' : exp | ({(id)} ∩ Rfv(e2) = {()} /\ Rfv(e2') = Rfv(e2)) 
                 \/ (({(id)} ⊆ Rfv(e2)) /\ 
                    (Rfv(e2') = (Rfv(e2) - {(id)}) U Rfv(e1))) }

The type of subst captures the fact that free-variables of substituted
expression e2' are same as that of initial expression e2, if variable
id does not occur free in e2. Otherwise, free-vars of e2' contain all
free-vars of e1 and all free-vars of e2, except the variable being
substituted (id).

To typecheck alphaConvert, we rely on the types of freeVars and
createNewName functions. We ascribe following type to createNewName:

    createNewName : {fvs : id list} -> {hint : string} -> 
                    {id : id | Rmem(fvs) ∩ {(id)} = {()}}

CreateNewName uses higher-order List.exists function to check if a
generated name is already present in list of free variables. The type
that we ascribed to List.exists proves to be useful here. From the
case-match statement and definition of Rfv relation, we derive this
equality:

    Rfv(e) = Rfv(e') - {(id)}

Next, we instantiate the type of createNewName to derive this
proposition (we skipped the intermediate list representation of
freevars here):

    id' : id, Rfv(e') ∩ {(id')} = {()}

We then instantiate the type of subst given above with (e1 = Var id'),
(id = id), and (e2 = e') to derive following proposition:

    ({(id)} ∩ Rfv(e') = {()} /\ Rfv(e2) = Rfv(e')) 
                 \/ 
    (({(id)} ⊆ Rfv(e')) /\ (Rfv(e2) = (Rfv(e') - {(id)}) U {(id')})

Now, we have sufficiently strong context to discharge the
post-condition of alphaConvert.

Similar to alphaConvert, the proof that subst function type checks
uses the type of higher-order List.exists. Due to nested branching,
the proof exercise is little involved, so we refrain from describing
entire proof here. Nevertheless, we demonstrate that subst fails to
type check if either 1. substitution is not capture-avoiding, or 2.
bound occurances are substituted.

For case 1, consider the erratic implemention:

{% highlight ocaml %}
fun subst (e1,id,e2) = case e2 of 
    ...
  | Abs(id',e2') => if id' = id then e2 else 
      Abs(id', subst (e1,id,e2'))
{% endhighlight %}

Type checking fails for the above implementation as following equation
about free-vars is invalid:

    ((Rfv(e2') - {(id)}) U Rfv(e1)) - {(id')}  = 
    (((Rfv(e2') - {(id')}) - {(id)}) U Rfv(e1)

The root cause is that

    Rfv(e1) - {(id')} ≠ Rfv(e1)

because free-vars of e1 may contain id', which is bound at current
lambda.

For case 2, consider the following implementation that implements
capture-avoiding substitution, but fails to ensure that bound
variables are not substituted:

{% highlight ocaml %}
fun subst (e1,id,e2) = case e2 of
    ...
  | Abs(id',e2') => 
      if List.exists (fn fv => fv = id') (freeVars e1)
        then subst(e1,id,alphaConvert e2)
        else Abs(id',subst(e1,id,e2'))
{% endhighlight %}

This implementation fails to typecheck as we cannot lift the
proposition that id occurs free in e2' to inference that either id
occurs free in e2 or id does not occur free in e2, as we do not know
if id = id' or id ≠ id' (where id' is variable bound at the current
lambda expression).

From these observations, we conclude that by appropriately annotating
alphaConvert and subst it is possible to ensure capture-avoiding and
scope-respecting properties of substitution and alpha-renaming
operations over untyped LC.

-- Update -- : Alpha renaming was verified by Catalyst. Here is the
code:

{% highlight ocaml %}
    exception Catalyst;

    datatype exp =    Var of string
                    | App of exp*exp
                    | Abs of string*exp

    fun idEq (x,y) = (x=y)

    fun listHas l n = case l of
        [] => false
      | x::xs => (idEq(x,n)) orelse (listHas xs n)

    fun freeVars e = case e of
          Var id => [id]
        | App (e1,e2) => List.concat [freeVars e1,freeVars e2]
        | Abs (id,e') => List.filter (fn fv => not (fv = id))
            (freeVars e')

    fun createNewName fvs base =
      let
        val name = base ^ "'"
      in
        if List.exists (fn fv => fv = name) fvs
        then createNewName fvs name
        else name
      end

    fun alphaConvert e = case e of
        Abs (id,e') =>
        let
          val fv_e' = freeVars e'
          val id' = createNewName fv_e' id
        in
          Abs(id',subst (Var id') id e')
        end
      | _ => raise Fail "No alpha-conversion for Unbound terms"

      (* Capture-avoiding substitution *)
    and subst (e1:exp) (id:string) (e2:exp) :exp = case e2 of
        Var id' => if idEq (id,id')
          then e1 else e2
      | App(e21,e22) => App(subst e1 id e21, subst e1 id e22)
      | Abs(id',e2') => if idEq (id',id) then e2 else
        let
          val fv_e1 = freeVars e1
        in
          if listHas fv_e1 id'
          then subst e1 id (alphaConvert e2)
          else Abs(id',subst e1 id e2')
        end (*Abs(id',subst e1 id e2')*)
{% endhighlight %}

## 2. Encoding ##

Encoding verification conditions with parametric relations in
decidable logic is primarily based on treating paramteric relations as
macros. That is, we create a ground relation for every instantiation
of parametric relation and abstractly interpret every evaluation step
in terms of each of these relations. While this methodology ensures
decidability, it leads to exponential blow-up in the size of
Z3 verification conditions. However, considering the stellar
performance of Z3 on verification conditions that Catalyst generated
so far, we can probably afford the size explosion.

Precise details on type checking and encoding with parametric
relations are yet to be worked out. I will send one more write-up with
such details once they are clear enough.
