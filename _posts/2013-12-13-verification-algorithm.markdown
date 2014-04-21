---
layout: post
title:  "Verification with General Relations"
date:   2013-12-13 11:23:41
--- 
In the last writeup, we introduced parametric relations which
generalize structural relations. This write-up captures my thought
process as I worked towards a multi-step verification algorithm that
discharges assertions in presence of parametric relations.  The
informal description of the final algorithm is given at the end of
this document.

Walk-Through
------------

First try:
Represent parametric relation as 2nd order proposition.  Keep
generating context in the usual way.  Once context is generated,
expand all (n&gt;1) order propositions by instantiating the parameter
with all suitable relations in scope. This process may have to be
repeated multiple times till all relations are flattened. We then
represent the flattened relation as yet another uninterpreted
function. That is, (Rmem RId) becomes a new relation RmemRId.
Context is ordered, so scope of relations is restricted. 
Remember that scope of abstract relations is the named binder for
which the type is specified.

{% highlight ocaml %}
    map f l = case l of
    (* (Rmem R)(x::xs) = R(x) U (Rmem R)(xs) *)
      [] => []
    | x::xs =>  (*  ΛT. λR : {'a * T} relation.  
        (Rmem R) (l) = R(x) U (Rmem R)(xs) *)
      let
        val v1 = (f x) (* 'Rb(v1) = 'Ra(x) *)
        val v2 = (map f xs) (* (Rmem 'Rb)(v2) = (Rmem 'Ra)(xs) *)
        val v3 = v1 :: v2 (*  ΛT. λR : {'b * T} relation.  
        (Rmem R) (v3) = R(v1) U (Rmem R)(v2) *)
      in
        v3 (* (Rmem 'Rb)(v3) = (Rmem 'Ra)(l)) ?? *)
      end

{% endhighlight %}

Let us add order asserton to map (i.e., _occurs-before_ assertion)

{% highlight ocaml %}
    fun map f l = case l of
    (* (Rmem R)(x::xs) = R(x) U (Rmem R)(xs) *)
    (* (Robs R)(x::xs) = R(x) X (Rmem R)(xs) U (Robs R)(xs) *)
      [] => []
    | x::xs =>  (*  ΛT. λR : {'a * T} relation.  
        (Rmem R) (l) = R(x) U (Rmem R)(xs) *)
                (*  ΛT. λR : {'a * T} relation.  
        (Robs R) (l) = (R(x) X (Rmem R)(xs)) U (Robs R)(xs) *)
      let
        val v1 = (f x) (* 'Rb(v1) = 'Ra(x) *)
        val v2 = (map f xs) (* (Rmem 'Rb)(v2) = (Rmem 'Ra)(xs) *)
                            (* (Robs 'Rb)(v2) = (Robs 'Ra)(xs) *)
        val v3 = v1 :: v2 (*  ΛT. λR : {'b * T} relation.  
        (Rmem R) (v3) = R(v1) U (Rmem R)(v2) *)
                          (*  ΛT. λR : {'b * T} relation.  
        (Robs R) (v3) = (R(v1) X Rmem(v2)) U (Robs R)(v2) *)
      in
        v3 (* (Rmem 'Rb)(v3) = (Rmem 'Ra)(l) ?? *)
           (* (Robs 'Rb)(v3) = (Robs 'Ra)(l) ?? *)
      end
{% endhighlight %}


Order assertion on map: Approach v1 continues to work.  One
interesting qn is that when parametrized (Robs R) is instantiated with
'Ra, it implicitly refers to (Rmem 'Ra). How do we know that (Rmem
'Ra) is a valid relation?  Robs is defined in terms of Rmem. So
parametrized Rmem is definitely defined. Since 'Ra is in scope,
instanted Rmem, i.e., (Rmem 'Ra) is also defined. 

{% highlight ocaml %}
    fun foldl f b l =  case l of
      [] => b
    | x::xs => (*  ΛT. λR : {'a * T} relation.  
        (Rmem R) (l) = R(x) U (Rmem R)(xs) *)
      let
        val v1 = f x b (*  'R1(v1) = 'r(x) U 'R1(b) *)
        val v2 = foldl f v1 xs (* 'R1(v2) = (Rmem 'r)(xs) U 'R1(v1) *)
      in
        v2 (* 'R1(v2) = (Rmem 'r)(l) U 'R1(b) ?? *)
      end

{% endhighlight %}

Approach v1 continues to work so far. Now consider this small, yet
interesting example:

{% highlight ocaml %}
    fun eq x1 x2 =
     let
       val y1 = x1 (* y1 = x1 *)
       val y2 = x2 (* y2 = x2 *)
       val v = (y1=y2)
         (* Rbool (RId(y1)) (v) = {(y1)} - ({(y1)} - {(y2)}) /\
            Rbool (RId(y2)) (v) = {(y2)} - ({(y2)} - {(y1)})*)
     in
       v (* Rbool ({(x1)}) (v) = {(x1)} - ({(x1)} - {(x2)}) /\
            Rbool ({(x2)}) (v) = {(x2)} - ({(x2)} - {(x1)}) ?? *)
     end
{% endhighlight %}

Clearly, the usual approach of representing flattened relation as a
unique uninterpreted relation does not work. Why? Z3 cannot infer that
that flattened relations Rboolx1 and Rbooly1 are the same when x1=y1. 
Here, should we explicitly add assertion for extensional equality? 
[Stack overflow qn link](stackoverflow.com/questions/20499217/encoding-parametric-functions-in-z3).

We need extensional equality. Fortunately, Z3 theory of arrays is same
as that of uninterpreted functions with extensional equality.
Therefore, we proceed with VC elaboration as follows:

    After first elaboration:
    y1=x1; y2=x2; 
    ry1 = RId(y1); ry2 = RId(y2);
    Rbool ry1 (v) = {(y1)} - ({(y1)} - {(y2)}) /\
    Rbool ry2 (v) = {(y2)} - ({(y2)} - {(y1)})
    rx1 = {(x1)}; rx2 = {(x2)};
    ----------------------------------------
    Rbool rx1 (v) = {(x1)} - ({(x1)} - {(x2)}) /\
    Rbool rx2 (v) = {(x2)} - ({(x2)} - {(x1)})
    
    After second elaboration:
    y1=x1; y2=x2; 
    ry1 = {(y1)}; ry2 = {(y2)};
    Rbool ry1 (v) = {(y1)} - ({(y1)} - {(y2)}) /\
    Rbool ry2 (v) = {(y2)} - ({(y2)} - {(y1)})
    rx1 = {(x1)}; rx2 = {(x2)};
    ----------------------------------------
    Rbool rx1 (v) = {(x1)} - ({(x1)} - {(x2)}) /\
    Rbool rx2 (v) = {(x2)} - ({(x2)} - {(x1)})
    
    After third elaboration:
    y1=x1; y2=x2; 
    ry1 = {(y1)}; ry2 = {(y2)};
    ary1 = array-from-fn ry1; 
    ary2 = array-from-fn ry2; 
    Rbool ary1 (v) = {(y1)} - ({(y1)} - {(y2)}) /\
    Rbool ary2 (v) = {(y2)} - ({(y2)} - {(y1)})
    rx1 = {(x1)}; rx2 = {(x2)};
    arx1 = array-from-fn rx1; 
    arx2 = array-from-fn rx2; 
    ----------------------------------------
    Rbool arx1 (v) = {(x1)} - ({(x1)} - {(x2)}) /\
    Rbool arx2 (v) = {(x2)} - ({(x2)} - {(x1)})
  

The above VC can be encoded in Z3 and discharged.

Now, first order List.exists example:

{% highlight ocaml %}
    fun List.exists11 l k = case l of
     (* relation Rk r (x) = r - (r - {(x)}) *)
     (* relation Rbool R (true) = R | (false) = {()} *)
     (*  = : x1 -> x2 -> {v: bool | 
            Rbool (RId(x1)) (v) = {(x1)} - ({(x1)} - {(x2)}) /\
            Rbool (RId(x2)) (v) = {(x2)} - ({(x2)} - {(x1)})}*)
     (* orelse : b1 -> b2 -> {b : bool | 
            Rbool r b = (Rbool r b1) U (Rbool r b2)} *)
      [] => false
    | x::xs => (*  ΛT. λR : {'a * T} relation.  
        (Rmem R) (l) = R(x) U (Rmem R)(xs) *)
      let
        val v1 = x=k (* Rbool {(x)} (v1) = {(x)} - ({(x)} - {(k)}) *)
          (* Rbool {(k)} (v1) = {(k)} - ({(k)} - {(x)}) *)
        val v2 = List.exists11 xs k 
          (* Rbool {(k)} (v2) = Rmem (Rk {(k)})(xs) *)
        val v3 = v2 orelse v1
          (* ΛT. λr : {T} relation. 
              (Rbool r)(v3) = (Rbool r)(v2) U (Rbool r)(v1)*)
      in
        v3 (* Rbool {(k)} (v3) = (Rmem (Rk {(k)}))(l) *)
           (* The judgement that has to be made is to instantiate
              R in parametrized Rmem R with (Rk {(k)}) *)
      end
{% endhighlight %}
The elaboration process is described below:

    Initial VC:
    ΛT. λR : {'a * T} relation.  
       (Rmem R) (l) = R(x) U (Rmem R)(xs) 
    Rbool RId(x) (v1) = {(x)} - ({(x)} - {(k)}) /\
    Rbool RId(k) (v1) = {(k)} - ({(k)} - {(x)})
    Rbool RId(k) (v2) = Rmem (Rk RId(k))(xs)
    ΛT. λr : {T} relation.  
       (Rbool r)(v3) = (Rbool r)(v2) U (Rbool r)(v1)
    -------------------------------------------
    Rbool {(k)} (v3) = (Rmem (Rk {(k)}))(l) ??
    
    After first elaboration:
    ΛT. λR : {'a * T} relation.  
       (Rmem R) (l) = R(x) U (Rmem R)(xs) 
    r1 = RId(x); r2 = RId(k)
    Rbool r1 (v1) = {(x)} - ({(x)} - {(k)}) /\
    Rbool r2 (v1) = {(k)} - ({(k)} - {(x)})
    Rbool r2 (v2) = Rmem (Rk r2)(xs)
    ΛT. λr : {T} relation.  
       (Rbool r)(v3) = (Rbool r)(v2) U (Rbool r)(v1)
    -------------------------------------------
    Rbool r2 (v3) = (Rmem (Rk r2}))(l) ??
    
    After second elaboration:
    ΛT. λR : {'a * T} relation.  
       (Rmem R) (l) = R(x) U (Rmem R)(xs) 
    r1 = RId(x); r2 = RId(k);
    r3(x) = (Rk r2)(x)
    Rbool r1 (v1) = {(x)} - ({(x)} - {(k)}) /\
    Rbool r2 (v1) = {(k)} - ({(k)} - {(x)})
    Rbool r2 (v2) = Rmem r3 (xs)
    ΛT. λr : {T} relation.  
       (Rbool r)(v3) = (Rbool r)(v2) U (Rbool r)(v1)
    -------------------------------------------
    Rbool r2 (v3) = (Rmem r3))(l) ??
    
    After third elaboration:
    ΛT. λR : {'a * T} relation.  
       (Rmem R) (l) = R(x) U (Rmem R)(xs) 
    r1 = {(x)}; r2 = {(k)};
    r3 (x) = r2 - (r2 - {(x)});
    Rbool r1 (v1) = {(x)} - ({(x)} - {(k)}) /\
    Rbool r2 (v1) = {(k)} - ({(k)} - {(x)})
    Rbool r2 (v2) = Rmem r3 (xs)
    ΛT. λr : {T} relation.  
       (Rbool r)(v3) = (Rbool r)(v2) U (Rbool r)(v1)
    -------------------------------------------
    Rbool r2 (v3) = (Rmem r3))(l) ??
    
    We now have to instantiate relational assertion schemes *)
    After fourth elaboration:
    (Rmem r3) (l) = r3(x) U (Rmem R)(xs) 
    r1 = {(x)}; r2 = {(k)};
    r3 (x) = r2 - (r2 - {(x)});
    Rbool r1 (v1) = {(x)} - ({(x)} - {(k)}) /\
    Rbool r2 (v1) = {(k)} - ({(k)} - {(x)})
    Rbool r2 (v2) = Rmem r3 (xs)
    (Rbool r1)(v3) = (Rbool r1)(v2) U (Rbool r1)(v1)
    (Rbool r2)(v3) = (Rbool r2)(v2) U (Rbool r2)(v1)
    -------------------------------------------
    Rbool r2 (v3) = (Rmem r3))(l) ??
    
    Finally, we encode relational parameters as arrays *)
    After fourth elaboration:
    r1 = {(x)}; r2 = {(k)};
    ar1 = array-from-fn r1; ar2 = array-from-fn r2;
    r3 (x) = r2 - (r2 - {(x)});
    ar3 = array-from-fn r3;
    (Rmem ar3) (l) = ar3[x] U (Rmem R)(xs) 
    Rbool ar1 (v1) = {(x)} - ({(x)} - {(k)}) /\
    Rbool ar2 (v1) = {(k)} - ({(k)} - {(x)})
    Rbool ar2 (v2) = Rmem ar3 (xs)
    (Rbool ar1)(v3) = (Rbool ar1)(v2) U (Rbool ar1)(v1)
    (Rbool ar2)(v3) = (Rbool ar2)(v2) U (Rbool ar2)(v1)
    -----------------------------------------------
    Rbool ar2 (v3) = (Rmem ar3))(l) ??
    
The VC in final step can now be discharged!

The Elaboration process for List.exists12, which returns true iff k is
not in the list, is same as List.exists11. The only change is in the
definition of Rk.

Now, let us consider higher-order List.exists.
{% highlight ocaml %}
    (* Higher-Order List.exists *)
    (* Abstract 'R2 *)
    (* Abstract 'r *)
    (*
     * List.exists21 : l -> (f : {x:'a} -> {v : bool | 
     *  (Rbool 'r)(v) = 'R2(x)} )
     *  -> {z : bool | (Rbool 'r)(z) = (Rmem 'R2)(l)}
     *)
    fun List.exists21 l f = case l of
        [] => false
      | x::xs =>(*  ΛT. λR : {'a * T} relation.  
        (Rmem R) (l) = R(x) U (Rmem R)(xs) *)
        let
          val v1 = List.exists21 xs f
            (* (Rbool 'r)(v1) = (Rmem 'R2)(xs) *)
          val v2 = f(x)
            (* (Rbool 'r)(v2) = 'R2(x) *)
          val v3 = v1 orelse v2
            (* ΛT. λr : {T} relation. 
              (Rbool r)(v3) = (Rbool r)(v2) U (Rbool r)(v1)*)
        in
          v3 (* (Rbool 'r)(v3) = (Rmem 'R2)(l) *)
        end
{% endhighlight %}
The VC elaboration process is described below:

    
    No A-Normalization style elaboration required. We start with
    instantiating relational assertion schemes.
    First elaboration:
    (Rmem 'R2) (l) = 'R2(x) U (Rmem 'R2)(xs)
    (Rbool 'r)(v1) = (Rmem 'R2)(xs)
    (Rbool 'r)(v2) = 'R2(x)
    (Rbool 'r)(v3) = (Rbool 'r)(v2) U (Rbool 'r)(v1)
    ---------------------------------------------
    (Rbool 'r)(v3) = (Rmem 'R2)(l) ??
    
    
    Second elaboration (Array'ize higher-order arguments):
    'aR2 = array-from-fn 'R2;
    'ar = array-from-fn 'r;
    (Rmem 'aR2) (l) = 'aR2[x] U (Rmem 'R2)(xs)
    (Rbool 'ar)(v1) = (Rmem 'aR2)(xs)
    (Rbool 'ar)(v2) = 'aR2[x]
    (Rbool 'ar)(v3) = (Rbool 'ar)(v2) U (Rbool 'ar)(v1)
    ---------------------------------------------
    (Rbool 'ar)(v3) = (Rmem 'aR2)(l) ??

This VC can be encoded in Z3 and discharged.
    
Now, let us consider the addk example which uses the higher-order
list.exists:

{% highlight ocaml %}
    (* addk : l -> k -> {l' | {(k)} ⊆ (Rmem RId)(l')}*)
    fun addk (l : string list) (k:string) : bool= 
      (*  Rk r (x) = r - (r - {(x)}) *)
      let
        val f = fn x => (x=k) 
          (* f : x -> {v : bool | 
           *   Rbool {(x)} (v) = {(x)} - ({(x)} - {(k)}) 
           *   Rbool {(k)} (v) = {(k)} - ({(k)} - {(x)}) 
           * Given the type of =, Catalyst can infer this type of f
           *)
        val v = List.exists l f
          (* f is expected to have type
           * f : {x:string} -> {v : bool | (Rbool 'r)(v) = 'R2(x)}
           * for abstract relation 'R2. However, we have no named relation
           * to instantiate 'R2 here. Appropriate way to handle this
           * problem is to create a (ephemeral) named relation over
           * the expression {(x)} - ({(x)} - {(k)}), that binds x.
           * In general, more intelligent the type unifier, more precise
           * is our analysis.
           * However, we defer that to future work. Instead, we ask 
           * users to provide appropriate type to either f or =.
           *)
          (*
           * Assuming = is given type in terms of Rk:
           *  = : x -> k -> {v: bool | 
           *    Rbool (RId(x)) (v) = (Rk (RId(x))) (k) /\
           *    Rbool (RId(k)) (v) = (Rk (RId(k))) (x)
           * we instantiate 'R2 with (Rk (RId(k))) to
           * get the following assertion in our context:
           *
           * (Rbool (RId(k)))(v) = (Rmem (Rk (RId(k))))(l)
           *
           * Note that we do not instantiate 'r with RId(x) as
           * it is not well-formed in current context
           *)

      in
        case v of 
          true => 
            (*  ΛT. λR : {T} relation. (Rbool R)(v) = R *)
              l (* (Rmem (Rk RId(k)))(v4) = {(k)} *)
        | false => 
            (*  ΛT. λR : {T} relation. (Rbool R)(v) = {()} *)
          let
            val v4 = k::l (*  ΛT. λR : {string * T} relation.  
              (Rmem R) (v4) = R(k) U (Rmem R)(l) *)
          in
            v4 (* (Rmem (Rk RId(k)))(v4) = {(k)} *)
          end
      end
{% endhighlight %}

### A note on extensional _inequality_ for relations:###
For addk example, we would ideally like to write the following
post-conditon: {(k)} ⊆ (Rmem RId)(l) But, we cannot prove this
post-condition for true branch, as we do not have assertions in terms
of (Rmem RId) in our context.  We do have that {(k)} = (Rmem (Rk
(RId(k))))(l) in true branch. Given that (Rk (RId(k))(x) ⊆ RId(x) and
r occurs +vely in the parametrized definition of (Rmem r), we should
be able to deduce the post-condition.  However, we do not have such
axioms for extensional inequality (subsumption) of relations
Nevertheless, we write the post-condition: {(k)} = (Rmem (Rk
(RId(k))))(l) which is equivalent to {(k)} ⊆ (Rmem RId)(l); so we lose
nothing.
    

Now, let us write higher-order List.exists using higher-order foldl
function:

{% highlight ocaml %}
    (* 
     * Abstract ('r,'R2) in 
     * List.exists22 : l -> (f : {x:'a} -> {v : bool | 
     *  (Rbool 'r)(v) = 'R2(x)} )
     *  -> {z : bool | (Rbool 'r)(z) = (Rmem 'R2)(l)}
     *)
    fun List.exists22 f l =
      let
        val g = fn (x,acc) => 
          let
            val v1 = f x
            val v2 = acc orelse v1
          in
            v2
          end 
            (* 
             * From the type of f and orelse, Catalyst synthesizes
             * following type for g:
             * g : x -> acc -> {z : bool | 
             * (Rbool 'r) (z) = 'R2(x) U (Rbool 'r)(acc)}
             *)
        val v3 = foldl g false l
          (* Recall that the type of foldl is (stronger than):
           * Abstract ('Rf, 'rf) in
           * foldl : l -> b -> 
           *   {f : x -> acc-> {z | 'Rf(z) = 'rf(x) U 'Rf(acc)}}  ->
           *   {z | 'Rf(z) = (Rmem 'rf)(l) U 'Rf(b)}
           * We instantiate abstract 'Rf with (Rbool 'r), and
           * 'rf iwth 'R2, so that g satisfies the required type of
           * folding function. Due to the result type of foldl, we have
           * this: 
           * (Rbool 'r)(z) = (Rmem 'R2)(l) U (Rbool 'r)(false)
           * Since (Rbool 'r)(false) = {()}, we have:
           * (Rbool 'r)(z) = (Rmem 'R2)(l)
           * which is the required post-condition!
           *)
      in
        v3
      end
{% endhighlight %}

Now, let us attempt List.zip:

{% highlight ocaml %}
    (* Recall that:
     * List.zip : l1 -> l2 -> {l | (Rmem (Rfst RId))(l) = (Rmem RId)(l1) 
     *                          /\ (Rmem (Rsnd RId))(l) = (Rmem RId)(l2)}
     * Where,
     *  relation Rfst R (x,y) = R(x)
     *  relation Rsnd R (x,y) = R(y)
     *)
     fun List.zip l1 l2 = case (l1,l2) of
        ([],[]) => []
      | (x1::xs1, x2::xs2) => (*  ΛT. λR : {'a * T} relation.  
          (Rmem R) (l1) = R(x1) U (Rmem R)(xs1)
               ΛT. λR : {'a * T} relation.  
          (Rmem R) (l2) = R(x2) U (Rmem R)(xs2) *)
        let
          val v1 = (x1,x2)
          val v2 = zip xs1 xs2
            (* (Rmem (Rfst RId))(v2) = (Rmem RId)(xs1) /\ 
             * (Rmem (Rsnd RId))(v2) = (Rmem RId)(xs2)
             *)
          val v3 = v1::v2 (*  ΛT. λR : {'a * T} relation.  
            (Rmem R) (v3) = R(v1) U (Rmem R)(v2) *)
        in
          v3 (* (Rmem (Rfst RId))(v3) = (Rmem RId)(l1) /\ 
              * (Rmem (Rsnd RId))(v3) = (Rmem RId)(l2) ??
              *)
        end
      | _ => raise (Fail "List.zip")

{% endhighlight %}

Elaboration process proceeds in same way as eq, map etc:
    
    Initial VC:
    ΛT. λR : {'a * T} relation.  
       (Rmem R) (l1) = R(x1) U (Rmem R)(xs1)
    ΛT. λR : {'a * T} relation.  
       (Rmem R) (l2) = R(x2) U (Rmem R)(xs2)
    v1.1 = x1; v1.2 = x2; (* Standard encoding tuples in Catalyst *)
    (Rmem (Rfst RId))(v2) = (Rmem RId)(xs1) /\ 
    (Rmem (Rsnd RId))(v2) = (Rmem RId)(xs2)
     ΛT. λR : {'a * T} relation.  
         (Rmem R) (v3) = R(v1) U (Rmem R)(v2)
    -----------------------------------------------
    (Rmem (Rfst RId))(v3) = (Rmem RId)(l1) /\ 
    (Rmem (Rsnd RId))(v3) = (Rmem RId)(l2) ??
    
    
    First elaboration:
    ΛT. λR : {'a * T} relation.  
       (Rmem R) (l1) = R(x1) U (Rmem R)(xs1)
    ΛT. λR : {'a * T} relation.  
       (Rmem R) (l2) = R(x2) U (Rmem R)(xs2)
    v1.1 = x1; v1.2 = x2; 
    R1 = Rfst RId; R2 = Rsnd RId;
    (Rmem R1)(v2) = (Rmem RId)(xs1) /\ 
    (Rmem R2)(v2) = (Rmem RId)(xs2)
     ΛT. λR : {'a * T} relation.  
         (Rmem R) (v3) = R(v1) U (Rmem R)(v2)
    -----------------------------------------------
    (Rmem R1)(v3) = (Rmem RId)(l1) /\ 
    (Rmem R2)(v3) = (Rmem RId)(l2) ??
    
    
    Second elaboration:
    (Rmem RId) (l1) = RId(x1) U (Rmem RId)(xs1)
    (Rmem RId) (l2) = RId(x2) U (Rmem RId)(xs2)
    v1.1 = x1; v1.2 = x2; 
    R1 = Rfst RId; R2 = Rsnd RId;
    (Rmem R1)(v2) = (Rmem RId)(xs1) /\ 
    (Rmem R2)(v2) = (Rmem RId)(xs2)
    (Rmem R1)(v3) = R1(v1) U (Rmem R1)(v2)
    (Rmem R2)(v3) = R2(v1) U (Rmem R2)(v2)
    -----------------------------------------------
    (Rmem R1)(v3) = (Rmem RId)(l1) /\ 
    (Rmem R2)(v3) = (Rmem RId)(l2) ??
    
    
    Third elaboration:
    (Rmem RId) (l1) = {(x1)} U (Rmem RId)(xs1)
    (Rmem RId) (l2) = {(x2)} U (Rmem RId)(xs2)
    v1.1 = x1; v1.2 = x2; 
    R1 = Rfst RId; R2 = Rsnd RId;
    (Rmem R1)(v2) = (Rmem RId)(xs1) /\ 
    (Rmem R2)(v2) = (Rmem RId)(xs2)
    (Rmem R1)(v3) = {(v1.1)} U (Rmem R1)(v2)
    (Rmem R2)(v3) = {(v1.2)} U (Rmem R2)(v2)
    -----------------------------------------------
    (Rmem R1)(v3) = (Rmem RId)(l1) /\ 
    (Rmem R2)(v3) = (Rmem RId)(l2) ??
    
    
    Fourth elaboration (Array'ize higher-order arguments):
    aRId = array-from-fn RId;
    R1 = Rfst RId; R2 = Rsnd RId;
    aR1 = array-from-fn R1;
    aR2 = array-from-fn R2;
    (Rmem aRId) (l1) = {(x1)} U (Rmem aRId)(xs1)
    (Rmem aRId) (l2) = {(x2)} U (Rmem aRId)(xs2)
    v1.1 = x1; v1.2 = x2; 
    (Rmem aR1)(v2) = (Rmem aRId)(xs1) /\ 
    (Rmem aR2)(v2) = (Rmem aRId)(xs2)
    (Rmem aR1)(v3) = {(v1.1)} U (Rmem aR1)(v2)
    (Rmem aR2)(v3) = {(v1.2)} U (Rmem aR2)(v2)
    -----------------------------------------------
    (Rmem aR1)(v3) = (Rmem aRId)(l1) /\ 
    (Rmem aR2)(v3) = (Rmem aRId)(l2) ??

Now, the VC can be encoded in Z3 and discharged.
    
Consider first-order List.exists with a slight change - instead of
using "orelse", we return true if recursive call returns true:

    
{% highlight ocaml %}
    fun List.exists12 l k = case l of
     (* relation Rk r (x) = r - (r - {(x)}) *)
     (* relation Rbool R (true) = R | (false) = {()} *)
     (*  = : x1 -> x2 -> {v: bool | 
            Rbool (RId(x1)) (v) = {(x1)} - ({(x1)} - {(x2)}) /\
            Rbool (RId(x2)) (v) = {(x2)} - ({(x2)} - {(x1)})} *)
      [] => false
    | x::xs => (*  ΛT. λR : {'a * T} relation.  
        (Rmem R) (l) = R(x) U (Rmem R)(xs) *)
      let
        val v1 = List.exists11 xs k 
          (* Rbool {(k)} (v1) = Rmem (Rk {(k)})(xs) *)
      in
        case v1 of 
            true =>  (* Rbool {(k)} (v1) = {(k)} *)
            true 
            (*  ΛT. λR : {T} relation. (Rbool R)(res) = R *)
            (* Rbool {(k)} (res) = (Rmem (Rk {(k)}))(l) ?? *)
          | false => (* Rbool {(k)} (v1) = {()} *)
            (x=k)
            (*  ΛT. λR : {T} relation. (Rbool R)(res) = {()} *)
            (* Rbool {(k)} (res) = (Rmem (Rk {(k)}))(l) ?? *)
      end
{% endhighlight %}

Verification process:

    
    Initial VC:
    For True Branch:
    ΛT. λR : {'a * T} relation.  
     (Rmem R) (l) = R(x) U (Rmem R)(xs)
    Rbool {(k)} (v1) = Rmem (Rk {(k)})(xs)
    Rbool {(k)} (v1) = {(k)}
    ΛT. λR : {T} relation. (Rbool R)(res) = R 
    ----------------------------------------
    Rbool {(k)} (res) = (Rmem (Rk {(k)}))(l)
    For False Branch:
    ΛT. λR : {'a * T} relation.  
     (Rmem R) (l) = R(x) U (Rmem R)(xs)
    Rbool {(k)} (v1) = Rmem (Rk {(k)})(xs)
    Rbool {(k)} (v1) = {()}
    ΛT. λR : {T} relation. (Rbool R)(res) = {()}
    ----------------------------------------
    Rbool {(k)} (res) = (Rmem (Rk {(k)}))(l)
    
    
    First elaboration:
    For True Branch:
    r1 = {(k)}; R1(x) = r1 - (r1 - {(x)})
    ΛT. λR : {'a * T} relation.  
     (Rmem R) (l) = R(x) U (Rmem R)(xs)
    Rbool r1 (v1) = (Rmem R1)(xs)
    Rbool r1 (v1) = {(k)}
    ΛT. λR : {T} relation. (Rbool R)(res) = R 
    ----------------------------------------
    Rbool r1 (res) = (Rmem R1)(l)
    For False Branch:
    r1 = {(k)}; R1(x) = r1 - (r1 - {(x)})
    ΛT. λR : {'a * T} relation.  
     (Rmem R) (l) = R(x) U (Rmem R)(xs)
    Rbool r1 (v1) = (Rmem R1)(xs)
    Rbool r1 (v1) = {()}
    ΛT. λR : {T} relation. (Rbool R)(res) = {()}
    ----------------------------------------
    Rbool r1 (res) = (Rmem R1)(l)
    
    
    Second elaboration:
    For True Branch:
    r1 = {(k)}; R1(x) = r1 - (r1 - {(x)})
    (Rmem R1) (l) = R1(x) U (Rmem R1)(xs)
    Rbool r1 (v1) = (Rmem R1)(xs)
    Rbool r1 (v1) = {(k)}
    (Rbool r1)(res) = r1
    ----------------------------------------
    Rbool r1 (res) = (Rmem R1)(l)
    For False Branch:
    r1 = {(k)}; R1(x) = r1 - (r1 - {(x)})
    (Rmem R1) (l) = R1(x) U (Rmem R1)(xs)
    Rbool r1 (v1) = (Rmem R1)(xs)
    Rbool r1 (v1) = {()}
    (Rbool r1)(res) = {()}
    ----------------------------------------
    Rbool r1 (res) = (Rmem R1)(l)
    
    
    Third elaboration:
    For True Branch:
    r1 = {(k)}; R1(x) = r1 - (r1 - {(x)})
    ar1 = array-from-fn r1;
    aR1 = array-from-fn R1;
    (Rmem aR1) (l) = aR1[x] U (Rmem aR1)(xs)
    Rbool ar1 (v1) = (Rmem aR1)(xs)
    Rbool ar1 (v1) = {(k)}
    (Rbool ar1)(res) = ar1
    ----------------------------------------
    Rbool ar1 (res) = (Rmem aR1)(l)
    For False Branch:
    r1 = {(k)}; R1(x) = r1 - (r1 - {(x)})
    ar1 = array-from-fn r1;
    aR1 = array-from-fn R1;
    (Rmem aR1) (l) = aR1[x] U (Rmem aR1)(xs)
    Rbool ar1 (v1) = (Rmem aR1)(xs)
    Rbool ar1 (v1) = {()}
    (Rbool ar1)(res) = {()}
    ----------------------------------------
    Rbool ar1 (res) = (Rmem aR1)(l)

The VC can now be encoded in Z3, and discharged.

In the above example, it has to be observed that, although the
semantics of orelse are implicit in List.exists12, our analysis was
able to discharge the verification condition. This is a testament to
the generality of our encoding boolean values
    
Informal Description of the verification algorithm
---------------------------------------------------

In the first step, type-checking process generates high-level
verification conditions (VCs), which are potentially higher-order. We
then elaborate VCs multiple times, each time expanding definitions of
fully applied relations and instantiating parametric relations with
appropriate relations in the context. We repeat this process till
there are no more relations to be expanded and parametric relations
are instantiated with all appropriate relations in the context. The
resultant VC is first-order. In the final step, VC is encoded in
SMT-LIB language by encoding relations as uninterpreted boolean
functions, and (actual) relational arguments as Z3 arrays relations
(so that we get extensional equality).

