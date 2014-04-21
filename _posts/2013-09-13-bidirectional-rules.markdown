---
layout: post
title:  "Bidirectional Rules"
date:   2013-09-13 11:23:41
---

# TYPE CHECKING#

## Bidirectional Rules ##

Since expressions in our language are only partially annotated (annotations 
only at function boundaries), the type checking process turned out to be a
bi-directional one. Intuitively, this means that I synthesize types as I 
analyze the program and check them against the expected type whenever there
is an annotation.  To present this precisely, I have re-formulated type-checking 
rules as bi-directional rules, i.e., rules representing two judgements:

First : Γ ⊢ e =&gt; τ , which is read as : "under context gamma, expression e 
synthesizes type tau"

Second : Γ ⊢ e &lt;= τ, which is read as : "under context gamma, expression e 
is checked against type tau"

Here are the rules (presence of Σ is explained below)


      Γ(x) = τ
    -------------  [T-Synt-Var]
      Γ ⊢ x => τ
      

      Γ ⊢ e₁ => (x:τ₁)→τ₂   Γ ⊢ e₂ <= τ₁
    -----------------------------------------------   [T-Synt-App]
      Γ ⊢ e₁ e₂ => [e₂/x] τ₂
      

      Γ ⊢ e₁ => τ₁    Γ[x↦τ₁] ⊢ e₂ => τ₂
    --------------------------------------------  [T-Synth-Let]
    Γ ⊢ let x = e₁ in e₂ end => Σ(x:τ₁).τ₂


          Γ[x→τ₁] ⊢ e <= τ₂
    -------------------------------------  [T-Check-Abs]
     Γ ⊢ λ(x:τ₁):τ₂.e <= (x:τ₁)→τ₂

     
      Γ ⊢ e => τ₁  τ₁<:τ₂
    -----------------------------  [T-Meet]
        Γ ⊢ e <= τ₂ 


        fresh(x)
    -------------------------------  [Encode-Sum]
    ⟦Σ{ν:T|r}.τ⟧ = r[x/ν] ∧ ⟦τ⟧


I introduced existential (Σ) types to account for local name bindings. However,
they only appear during the type checking process and the type language exposed 
to user does not contain existentials. This avoids many problems that come with 
dependent sum types. Accordingly, our rules for existentials are different from 
corresponding rules of, say Calculus of Constructions, as we do not have usual
elimination form for sum types. Existentials are eliminated while generating 
verification condition through Skolemization (instantiating existentially bound
variable with fresh variable). Rule Encode-Sum captures this.

## Records and Tuples ##

Record types and tuple types are both as product types with predefined
names for bound variables inside constituent types. For tuple types,
bound variables are named after natural numbers, whereas for records, names
are user-defined. At pattern-matching sites, matched variables are assigned
types of corresponding components of the product. For example,


{% highlight ocaml %}
    var v0 = {name = "foo", id=1} (* v0 : {name:string|true}*{id:int|true}  *)
    var v1 = ("foo","bar")   (* v1 : {1:string|true}*{2:string|true} *)
    var (name,...) = v0  (* name : {ν:string|true} *)
    var (x,y) = v1  (* x : {ν:string|true}  and y : {ν:string|true} *)
{% endhighlight %}

tuple/record accessor functions like #1 or #foo are converted to 
corresponding case-match sites.

# A-NORMALIZATION #

A-Normalization is a simple affair for a language with no type annotations. For 
Standard ML, even at the AST level, there are optional annotations for generali-
zation of type-variables at let-bindings. MLton elaborates AST to full type-ann-
otated CoreML. Owing to the simplicity of CoreML and considering that we require 
ML types for verification, I decided to analyze program at CoreML level. Therefore,
A-Normalization in my case generates ANormalCoreML.t from CoreML.t. Since I couldn't
find an existing method for a-normalizing type-annotated polymorphic language with
patterns and let-bindings, I adapted simple A-Normalization for CoreML. Here are 
some salient aspects of the algorithm:

## Type Variables. ##

Here is an example that demonstrates the effect of the procedure on a binding with
polymorphic nested expression and a nested pattern:

{% highlight ocaml %}
  var ('a1,'a2,'a3) (f,(g,h)) = (fn x => x, (fn y => y, fn z => z))
{% endhighlight %}

elaborates to:

{% highlight ocaml %}
  var ('a19,'a20,'a21) v4 = fn z => z
  var ('a16,'a17,'a18) v3 = fn y => y
  var ('a13,'a14,'a15) v2 = (v3 ('a13,'a14,'a15), v4 ('a13,'a14,'a15))
  var ('a10,'a11,'a12) v1 = fn x => x
  var ('a7,'a8,'a9) (f,v0) = (v1 ('a7,'a8,'a9),v2 ('a7,'a8,'a9))
  var ('a4,'a5,'a6) (g,h) = v0 ('a4,'a5,'a6)
{% endhighlight %}

I would like to point out that elaboration is semantics preserving even in presence of
type variable generalization and instantiation.

## Case-Match Expression ##

Case match expression is a non-trivial case. Consider the following 
case-match expression.

{% highlight ocaml %}
  case x of cons(x1,(cons(x2,Nil)) => e1
   | cons (x1,cons(x2,xs)) => e2
   | _ => e3
{% endhighlight %}

An elaboration that preseves dynamic semantics of above case-match 
statement is difficult to achive. To see why, consider an naive 
attempt that results in an (incomplete) elaborated form similar to this:

{% highlight ocaml %}
  case x of 
    cons (x1,v0) => 
      case v0 of cons(x2,Nil) => e1 | _ => <?1>
  | cons (x2,v1) =>
      case v1 of cons(x2,xs) => e2 | _ => <?2>
  | _ => e3
{% endhighlight %}

Two problems can be identified with above structure:
1. It is not clear what should go in holes &lt;?1&gt; and &lt;?2&gt;.
2. Observe that the patterns in first two rules of the match statement
are identical. Therefore, the two patterns need to be collapsed and further
elaboration needs to be performed.

However, an elaboration that preserves static semantics is much easier to achieve 
with help of a branch expression (similar to guard expressions in guarded command 
language) : 

    branch
      (assume (x=cons(x1,v0)); assume(v0 = cons(x2,Nil)); e1)
      (assume (x=cons(x2,v1)); assume(v1 = cons(x2,xs)); e2)
      (e3)

The above branch statement has type T if all branch expressions have type T.
It is easy to see that this preserves static semantics of original case-match
