---
layout: post
title:  "Primitive Relation Synthesis"
---

The [previous wiki][tireview] demonstrates the observation that the
syntactic structure of various primitive relations required to
construct the relational type of a function often matches with the
syntactic structure of some expression within the function definition.
In this wiki, we work with this observation and try to develop a
methodical way to extract, from the definition of a function,
primitive relations relevant to build its type.

Concat Example
--------------

Lets take a look at the concat function.

    fun concat l1 l2 = case l1 of
        [] => l2
      | x::xs => 
        let
          val l' = concat xs l2
          val l = x::l'
        in
          l
        end

Consider the `x::xs` branch. Let us say `R0?` and `R1?` be structural
relations defined over the list type, such that the following
equations hold:

    R0?(x::xs) = {x}
    R0? _ = {}
    R1? = R0?*

Notice that `R1?` has been conveniently defined such that any total
function defined structurally recursively over the list _will_ access 
every element in `R1?` in its `x::xs` branch.

Expl. 1
--------

Let `I` be the relational interpretation synthesizer. Then, in the
`x::xs` branch of `concat`:

    I("x::xs => e",[]) = R1?[\x.I("e",[xs])](l1)

Let us denote the instantiated relation `R1?[\x.I(e,[xs])]` as `R1?c`.
In the `let` expression: `R1?[RId](l) = R1?[\x.RId(x) U
R1?[RId](l')](l1)`.  However, `l'` is unknown. Plus we have the
obligation that `R1?c(xs)⊆R1?[RId](l')`. Therefore, we have:
`R1?[\x.RId(x)](l1) ⊆ R1?[RId](l)`.

Expl. 2
-------

The aim is to infer an invariant of form: `R2?['Rb?](l) = R1?['Ra](l1)
U re'`, where `l1 ∉ freevars(re')`. From the analysis in previous
subsection, we know that `R2?['Rb?](l) = R1?[\x.'Rb?(x) U
R2?['Rb?](l')](l1)`. However, since we know that `R2?['Rb?](l') =
R1?['Ra?](xs) U re'`, we have:
    
    R2?['Rb?](l) = R1?[\x.'Rb?(x) U R1?['Ra?](xs)](l1) U  re'.

The above can be unified with:

    R2?['Rb?](l) = R1?[\x.'Ra?(x) U R1?['Ra?](xs)](l1) U  re'.

Inferring `'Rb? = 'Ra?`, and the following inv:

    R2?['Ra?](l) = R1?[Ra?](l1) U re'

or, inferring `'Ra? = 'Rb?`, and the following inv:

    R2?['Rb?](l) = R1?[Rb?](l1) U re'

Concat CoreML Example
---------------------

Here is the actual an-core-ml of `concat`:

    val rec concat = (fn x_0 => (fn x_1 =>
      let val anc_27 = x_0
          val anc_28 = x_1
      in
         case (anc_27, anc_28) of
           (l1, l2) =>
           case l1 of
             [] => l2
           | ::(x, xs) =>
             let val anc_29 = :: 
                 val anc_30 = x
                 val anc_31 = concat
                 val anc_32 = (anc_31 xs)
                 val anc_33 = (anc_32 l2)
             in
                (anc_29 (anc_30, anc_33))
             end
      end))

Zip Example
------------

Here is the zip function:

    fun zip [] [] = []
      | zip x::xs y::ys = 
        let 
          val v = (x,y) 
          val l' = zip xs ys
        in
          v::l'
        end

Consider the `x::xs y::ys` branch. Similar to concat, we are
interested in `'R1?` relational abstraction of `l1` and `l2`.  The aim
is to infer an invariants of form `R2?['Rc?](l) = R1?['Ra?](l1) U re'`,
and `R2?['Rd?](l) = R1?['Rb?](l2) U re''`. 

`R1?[\x.let Rfst(v) = {x} in 'Rb?(v) U R2?['Rb?](l')](l1) U re' = R2?['Rb](l)


Filter Example
--------------

Here is the filter_neq function:

    fun filter_neq l id = case l of
        [] => []
      | x::xs => 
        let
          val xs' = filter_neq xs id
          val l' = if x=id then xs' else x::xs'
        in
          l'
        end

`R1?[]`

[tireview]: https://www.cs.purdue.edu/sss/projects/catalyst/2015/01/19/Type-Inference-Review.html
