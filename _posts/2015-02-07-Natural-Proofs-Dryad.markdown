---
layout: post
title:  "Paper Review - Qiu et al's Natural Proofs (PLDI'13)"
--- 

The paper proposes a proof technique called _natural proofs_ for
reasoning with programs that manipulate data structures. As per
authors, the distinguishing aspects of natural proofs are:

1. They are amenable to complete automated reasoning
2. They provide sound but incomplete procedures (??)
3. They capture common reasoning tactics in program verification.

Authors develop a dialect of separation logic called _Dryad_. They do
away with explicit quantification allowed by separation logic, and
instead allow recursive definitions (like Catalyst does with
structural relations). For proofs, they develop proof tactics
involving disciplined unfolding of recursive definitions (this is what
Catalyst does for pattern matches). Natural proofs can be encoded into
decidable fragment of FOL, mostly the set theory.

"The work in this paper is motivated by the **opinion** that entirely
decidable logics are too restrictive, in general, to support the
verification of heap manipulating programs. ... Our aim is to build
completely automatic, sound but incomplete proof techniques that can
solve a large class of properties involving complex data-structures".
In other words, they propose a logic that is undecidable in general.

Let $$\mathcal{N}$$ be a subset of all proofs that can be represented
in a certain way ($$\mathcal{N}$$ is possibly a restricted grammar to
represent certain kinds of proofs). Let us say that $$\mathcal{N}$$
has following pleasant properties:

1. Large class of valid VCs of real-world programs have a proof in
   $$\mathcal{N}$$
2. Searching for proof in $$\mathcal{N}$$ is efficiently decidable
   (possibly utilizing SMT solvers).

Then $$\mathcal{N}$$ is very useful for program verification; for a
given VC, we can efficiently search for a proof in $$\mathcal{N}$$,
and if one doesn't exist, we can be reasonable confidant that the VC
is invalid. Authors claim that the set of natural proofs has such
pleasant properties (the concept of natural proofs itself was
introduced in their POPL'12 paper). "Natural proofs are hence a fixed
set of proof tactics whose application is itself expressible in a
decidable logic (??)". **The aim of this paper is to provide natural
proofs for general properties of structure, data and seperation.**

Dryad: A separation logic with determined heaplets
--------------------------------------------------

Separation logic is built to express _strict specifications_ - logical
formulas must naturally refer to _heaplets_, and by default the
smallest heaplet over which a formula needs to refer to (Compare this
with heap specs in classical logic, where the formula needs to refer
to the entire heap). This facilitates the frame rule:

$$
  \frac {
    \{P\}C\{Q\}\quad
    disjoint(\{R\},\{P,Q\})
  }
  {
    \{P*R\}C\{Q*R\}
  }
$$

The equivalent of `x:tree` in a heap manipulating program is a tree
rooted at `x`, which can be described in separation logic with
recursive definitions as:

$$tree(x) \;=\; (n=NIL \wedge emp) \vee (x \mapsto (l,r) * tree(l) * tree(r))$$

The formula, parameterized on `x`, expresses the fact that either
`x=null` (hence heaplet is $$emp$$ty) or `x` points to a location
storing roots of left and right subtrees, such that `x`,`l`, and `r`
are disjoint. The disjointness comes from the fact that the formula
$$(x \mapsto (l,r) * tree(l) * tree(r))$$ can be expanded to:

$$(x \mapsto (l,r) * l \mapsto ... * r \mapsto ...)$$

By definition, formulas combined using _spatial conjunction operator_
($$ * $$) are defined over disjoint heaplets.

As shown above, Dryad permits recursive definitions to define
sets/multi-sets of integers, and sets of locations, using least
fixed-points. However, unlike seperation logic, Dryad does not allow
explicit quantification. Also, in Dryad, the heaplet for a recursive
formula is _determined_ by the syntax as opposed to semantics in
classical seperation logic (CSL). In CSL, a formula of form
$$\alpha * \beta$$ says that the heaplet can be partitioned into _any_
two disjoint heaplets, one satisfying $$\alpha$$ and other $$\beta$$.
In Dryad, if there is a way to parition the heaplet, there is
precisely one way to do so. This eliminates the implicit existential
quantification entailed by the semantics of $$ * $$ in CSL.

Example
-------

The example they use in the paper is the `heapify` function on the
max heap data structure. The function is given below:

{% highlight c %}
    void heapify (loc x) 
    {
      if (x.left = nil)
        s := x.right;
      else if (x.right = nil)
        s := x.left;
      else {
        lx := x.left;
        ly := x.right;
        if (lx.key < rx.key)
          s := x.right;
        else
          s := x.left;
      }
      if (s != nil && s.key > x.key) {
        t := s.key;
        s.key := x.key;
        x.key := t;
        heapify(s);
      }
    }
{% endhighlight %}

To write a Dryad specification for heapify, we define two recursive
seperation logic predicates:

    mheap(x) =    (x=nil /\ emp) 
               \/
                    (x --{key,left,right}-> (k,l,r))
                  * (mheap(l) /\ k ≥ keys(l))
                  * (mheap(r) /\ k ≥ keys(r))

    keys(x) = 
      (x=nil /\ emp): ∅;
      (x --{key,left,right}-> (k,l,r) * true): {k} ∪ keys(l) ∪ keys(r);

Then, we can write a hoare specification for `heapify` as following:
    
    {x≠nil /\ mheap(x) /\ keys(x)=K} heapify(x) {mheap(x) /\ keys(x)=K}

Observe that `heapify` is a state manipulating program; so, we cannot
write a type specification. Instead, we write a hoare triple with pre
and post-conditions asserting invariants on same `x`. Also observe
that we had to use an existential `K` to refer to set of keys in the
maxheap before the `heapify`.

Main aspect of their approach is to reduce reasoning about heaplet
semantics and seperation logic constructs to reasoning about sets of
locations, making use of set operators like union, intersection and
membership. Intuitively, they associate a set of locations to each
spatial atomic formula, which is considered the domain of the heaplet
satisfying the formula (**How is this different from heaplet semantics
in CSL?**). In other words, heaplet is determined syntactically for
each formula. For example, the heaplet associated with the formula
$$x \mapsto ...$$ is $$\{x\}$$. For recursive predicates like `mheap`,
the domain of the heaplet is defined recursively as `reach(x)`:

    reach(x) = 
      (x=nil): ∅;
      (x --{key,left,right}-> (k,l,r)): {x} ∪ reach(l) ∪ reach(r);

Once we have captured heaplet semantics in classical logic, we can
translate pre and post conditions on `heapify`, which are seperatiol
logic formulas on heaplets, to classical logic formulas on entire
heap. For e.g, let $$G_{pre}_{}$$ denote the set representation of
heaplet in classical logic. Then, the classical logic translation
of the pre-condition of `heapify` is (after simplifying `x≠nil /\
x=nil` to `⊥`):

$$
  G_{pre}_{} \;=\; \{x\} \,\cup\,  reach(l) \,\cup\, reach(r) 
  \;\wedge\; x \notin reach(l) \;\wedge\; x \notin reach(r) \;\wedge\;
  reach(l) \,\cap\,reach(r) \,=\, \emptyset \;wedge\; x \neq nil
  \;wedge\; mheap(l) \;wedge\; mheap(r) \;wedge\; G_{pre}_{}=reach(x) 
$$
