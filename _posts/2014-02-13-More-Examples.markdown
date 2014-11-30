---
layout: post
title:  "Examples"
date:   2014-02-13 12:23:41
--- 
More Examples of Verification With Structural Relations
-------------------------------------------------------
## 1. Tree Examples ##

 First, a simple binary-tree

    datatype 'a tree = Leaf of 'a
                     | Branch of 'a tree * 'a * 'a tree
    (* Relations *)
    relation Rroot (Branch(l,n,r)) = {(n)} | (Leaf n) = {(n)};
    relation Rtmem = Rroot*;
    (*
     * Total-Order of all elements
     *)
    relation Rto (Branch (l,n,r)) = (Rtmem(l) X {(n)}) U 
                        ({(n)} X Rtmem(r)) U (Rtmem(l) X Rtmem(r))
               | (Leaf n) = {()};
    relation Rtos = Rto*;
    (*
     * Post-Order relation
     *)
    relation Rpo (Branch (l,n,r)) = (Rtmem(l) X {(n)}) 
                        U (Rtmem(r) X {(n)}) U (Rtmem(l) X Rtmem(r))
               | (Leaf n) = {()};
    relation Rpos = Rpo*;
    (*
     * In-Order relation
     *)
    relation Rino (Branch (t1,x,t2)) = 
      (Rtmem(t1) X {(x)}) U ({(x)} X Rtmem(t2)) | (Leaf) = {()} ;
    relation Rinos = Rino*;
    
    preOrder : {tr} -> { l | Rmem(l) = Rtmem(tr) /\ Robs(l) = Rtos(tr)};
    fun preOrder t = case t of
        Leaf x => [x]
      | Branch z =>
        let
          val (l,x,r) = z
        in
          concat (concat (preOrder l) [x]) (preOrder r)
        end

    postOrder : {tr} -> {l | Rmem(l) = Rtmem(tr) /\ Robs(l) = Rpos(tr)};
    fun postOrder t = case t of
        Leaf x => [x]
      | Branch (l,x,r) => concat (concat (postOrder l) 
                    (postOrder r)) [x] 

Assume split function that splits l to (l1,l2) such that l = l1++l2

    split : {l} -> {(l1,l2) | Robs(l) = Robs(l1) U Robs(l2) 
                        U (Rmem(l1) X Rmem(l2))}
  
Function inOrder creates a tree whose in-order is occurs-before order
of the list:

    inOrderTree : {l} -> {t | Rinos(t) = Robs(l1)}
    fun inOrderTree l = case l of
      [] => Leaf
    | [x] => Branch(Leaf,x,Leaf)
    | _ => let val (l1,x::l2) = split l 
      in Branch(inOrderTree l1, x, inOrderTree l2) end

Function removeFirst is same as removeMin for binary search tree.

    removeFirst : {t} -> {(x,t') | Rinos(t) = ({(x)} X Rtmem(t))
                                  U Rinos(t')}
    fun removeFirst t = case t of Leaf => raise Error
      | Branch (Leaf,x,t2) => (x,t2)
      | Branch (t1,x,t2) => let val (x',t1') = removeFirst t1 
          in (x',Branch (t1',x,t2))

## 2. Okasaki's Red-Black tree ##

    datatype colour = R | B                                          

    datatype 'a tree = E | T of colour * 'a tree * 'a * 'a tree  

Relations for RB tree:

    relation Rroot (T(c,l,n,r)) = {(n)} | E = {()};
    relation Rmem = Rroot*;
    relation Rto (T (c,l,n,r)) = (Rmem(l) X {(n)}) 
                U ({(n)} X Rmem(r)) U (Rmem(l) X Rmem(r)) | E = {()};
    relation Rtos = Rto*;

Tree balance function :

    balance : t -> {t' | Rmem(t') = Rmem(t) /\ Rtos(t') = Rtos(t)};
    fun balance (t:'a tree) : 'a tree = case t of
        T (B,T (R,T (R,a,x,b),y,c),z,d) => 
                            T (R,T (B,a,x,b),y,T (B,c,z,d))
      | T (B,T (R,a,x,T (R,b,y,c)),z,d) => 
                            T (R,T (B,a,x,b),y,T (B,c,z,d))
      | T (B,a,x,T (R,T (R,b,y,c),z,d)) => 
                            T (R,T (B,a,x,b),y,T (B,c,z,d))
      | T (B,a,x,T (R,b,y,T (R,c,z,d))) => 
                            T (R,T (B,a,x,b),y,T (B,c,z,d))
      | _ => t


## 3. Map Examples ##

Type of Map:

    ('R1,'R2) map : l -> (x -> {y | 'R2(y) = 'R1(x)}) -> {v | (Rmem
        'R2)(v) = (Rmem 'R1)(l) /\ (Robs 'R2)(v) = (Robs 'R1)(l)}

Example 1 - Projection:
 Invariant : Rob((x1,x2), (y1,y2)) <=> Rob(x1,y1)

    project : l -> {v | (Robs RId)(v) = (Robs Rfst)(l)}
    val project = fn l =>
      let
        val fst = fn (x,y) => x
        val newl = map (Rfst,RId) l fst
      in
        newl
      end

Example 2 - List of lists to List of trees
Invariant : For every list l in ll, there exists a tree t
in tl such that in-order of tree is same as order of elements in
the list. Conversely, for every tree t in tl, there exists a list
l in ll with similar property.
A stronger invariant that asserts order of all such orders is
also possible. 

    toTrees : {ll: 'a list list} -> {tl : 'a tree list | 
        (Rmem Rinos)(tl) = (Rmem Robs)(ll)}
    val toTrees = fn ll => map ll inOrderTree 
  
In further examples, I will use unparametrized relations to also
denote parametric relations instantiated with trivial RId relation.
Therefore, 

    Robs(l) <=> (Robs RId)(l).

## 4. Fold Examples ##

Let me start with a very simple type for fold:

    ('R1,'R2) fold_left : l -> b -> ((* f : *){x} -> {acc} 
        -> {z | 'R2(z) = 'R1(x) U 'R2(acc)})
        -> {v | 'R2(v) = (Rmem 'R1)(l) U 'R2(b)}
 
The type only talks about how membership relation of list is
related to the result. Therefore, fold\_right too would have
similar type. Straightforward example for such type is folding a
list into a tree, which preserves members:

     makeTree : {l : int list} -> {v : int tree | Rtmem(v) = Rmem(}
     val makeTree = fn l =>
      (* I make relation instantiations explicit. *)
      fold_left (RId, Rtmem) l Leaf treeInsert

A more precise type for fold should relate the order of elements
in the argument list to some order of the result. The intuition is as
following: Let us say the result type ('b) has some notion of order
and a relation to describe the order such that, the higher-order
argument (f) of fold has post-condition in terms of such a relation;
i.e., it says something about how the order relation of its result (z)
relates to its arguments (x, and acc). But, x comes from list, and f
is applied over elements of the list in a pre-defined order.
Therefore, it is possible to derive invariant relating order relation
of the list to order relation of the result type, given the assertion
describing the order in which f is applied over the list.  
Here are such types fold\_left and fold\_right:

    ('R1,'R2,'R3) fold_left : l -> b -> ({x} -> {acc} 
        -> {z | 'R2(z) = 'R1(x) U 'R2(acc) /\ 
                'R3(z) = ('R1(x) X 'R2(acc)) U 'R3(acc)})
        -> {v | 'R2(v) = (Rmem 'R1)(l) U 'R2(b) /\ 
                'R3(v) = (Roas 'R1)(l) U 'R3(b) U 
                  ('R2(b) X (Rmem 'R1)(l))}

    ('R1,'R2,'R3) fold_right : l -> b -> ({x} -> {acc} 
        -> {z | 'R2(z) = 'R1(x) U 'R2(acc) /\ 
                'R3(z) = ('R1(x) X 'R2(acc)) U 'R3(acc)})
        -> {v | 'R2(v) = (Rmem 'R1)(l) U 'R2(b) /\ 
                'R3(v) = (Robs 'R1)(l) U 'R3(b) U 
                  ((Rmem 'R1)(l) X 'R2(b))}

Observe the difference in post-conditions of fold\_left and
fold\_right.In the following implementation of rev using fold\_left, I
make relation instantiation explicit. As usual, for the sake of
clarity, I use Rmem in place of (Rmem RId), Robs in place of (Robs
RId), and so on.

    (* Auxiliary def: Cons *)
     val Cons = fn x => fn xs => x::xs
     (R) rev : {l : 'a list} -> {v : 'a list | Rmem[R](v) = Rmem[R](l) /\
                                               Robs[R](v) = Roas[R](l)}
     val rev  = fn l => fold_left (RId, Rmem, Robs) l [] Cons 

   
Using fold\_right in place of fold\_left in the above code,
results in an identity function for lists:

     idList : {l : 'a list} -> {v : 'a list | Robs(v) = Robs(l)}
     val idList  = fn l => fold_right (RId, Rmem, Robs) l [] Cons 
   

 As a result, using fold\_right and expecting list to be reversed
 results in failure of type checking. Similarly, append (i.e.,
 concat) has to be implemented with fold\_right:

    (R) concat : {l1} -> {l2} -> {v | Rmem[R](v) = Rmem[R](l1) U Rmem[R](l2) /\
                                      Robs[R](v) = Robs[R](l1) U Robs[R](l2) U
                                                  (Rmem[R](l1) X Rmem[R](l2))}
    val concat = fn l1 => fn l2 => fold_right (RId, Rmem, Robs)
          l1 l2 Cons

Using fold\_left, or passing [] in place of l2 results in type
error

The Quicksort Example
======================

The F\* reviewer's [example](http://rise4fun.com/FStar/dsE)

Catalyst encoding:
{% highlight ocaml %}
    (*
     * Let us parametrize the module over a relation
     * R that relates x:'a to all y:'a, such that y >= x
     *)
    R :: 'a :-> {'a};

    (*
     * RIn r1 r2 = r1, if r1 ⊆ r2. ∅ otherwise
     * RNin r1 r2 = r1, if r1 ∩ r2 = ∅. ∅ otherwise.
     *)
    RIn r1 r2 = r1 - (r1 - r2);
    RNin r1 r2 = r1 - r2;

    (*
     * (fr1 p x) = {(x)}, if x \notin R(p) (i.e., if x<p). ∅ otherwise.
     * (fr2 p x) = {(x)}, if x ∈ R(p) (i.e., if x >= p). ∅ otherwise.
     * (fr3 (x,y)) = {(x,y)}, if y ∈ R(x) (i.e., y >= x). ∅ otherwise.
     *)
    let fr1 = \p.\(x). RNin {(x)} (R(p))
    let fr2 = \p.\(x). RIn {(x)} (R(p))
    let fr3 = \(x,y). {(x)} X RIn {(y)} (R(x))

    (*
     * partition takes a pivot p, a list l, and produces two lists l1 and
     * l2. Elements of l1 are elements of l less than p, whereas elements
     * of l2 are elements of l greater than or equal to p.
     *)
    partition : p -> l -> {x -> y -> {v | v=true <=> {(y)} ⊆ R(x)}}
                  -> {l1 | Rmem(l1) = bind(Rmem(l),fr1 p) } * 
                     {l2 | Rmem(l2) = bind(Rmem(l), fr2 p)}
    fun partition p l cmp = case l of
        [] => ([],[])
      | x::xs =>
        let
          val (l1',l2') = partition p xs cmp
        in
          if cmp x p then (x::l1',l2')
          else (l1',x::l2')
        end

    (*
     * quicksort takes a list l, and produces a list v such that
     * 1. v has same elements as l, and
     * 2. Robs(v,x1,x2) => (x2 >= x1)
     *)
    quicksort : l -> {x -> y -> {v | v=true <=> {(y)} ⊆ R(x)}}
                  -> {v | Rmem(v) = Rmem(l)
                       /\ Robs(v) = bind (Robs(v),fr3)}
    fun quicksort l cmp = case l of
        [] => []
      | x::xs =>
        let
          val (l1,l2) = partition x l cmp
          val l1' = quicksort l1 cmp
          val l2' = quicksort l2 cmp
          val l' = append l1' l2'
        in
          l'
        end 
{% endhighlight %}

