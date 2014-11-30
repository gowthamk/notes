---
layout: post
title:  "Deriving Consistency Contracts from Integrity Constraints"
---

Introduction
=============

Consitency contracts in Quelea are assertions over an axiomatic
execution of a concurrent program manipulating a replicated object.
Although the manifest purpose of a contract is to prevent certain
interleavings from ever occuring, the real goal is to maintain
application-specific invariants, called integrity constraints. For
example, integrity constraint for Bank Account is that balance should
never go below zero. While integrity constraints for any application
domain are usually well-understood, constructing axiomatic
specifications that prevent a concurrent program from violating
integrity constraints, but at the same time are not overly restrictive
is a difficult and error-prone activity. The process is unguided, and
relies on programmers' awareness of anomalies possible under
concurrency so that they can write relevant contracts only to prevent
them. In this context, there is need for a methodical procedure to
derive weakest axiomatic speciications from desired application-level
integrity constraints.

In this document, I describe such a process for the BankAccount
example. I start with a Quelea implementation of BankAccount RDT sans
any contracts, but with an integrity constraint specified as a return
type of `getBalance` operation. By performing _backward reasoning_,
similar to the one used in weakest pre-conditon derivation, I arrive
at weakest axiomatic contracts required to enforce the integrity
constraint. However, the reasoning I present is no where near as
mechanical as WP. The aim of this article to just demonstrate that it
is possible to formally derive axiomatic specifications from integrity
constraints.


Bank Account
============

Consider the BankAccount example with following definitions and types:

{% highlight ocaml %}
    datatype BAEff = Deposit of Int | Withdraw of Int

    type BankAccount = BAEff List

    type PosInt = {v: Int | v>=0}

    getBalance : BankAccount -> unit -> PostInt * BAEff
    fun getBalance ctxt () = 
        let val bal = foldl ba 0 
          (fn b => fn sum => 
            case b of Deposit x => sum + x
             | GetBalance => sum
             | Withdraw x => sum - x)
        in
            (bal, SOME GetBalance)
        end

    withdraw : BankAccount -> Int -> Bool * BAEff option
    fun withdraw ctxt amt = 
      if (getBalance ba >= amt) 
      then  (True, SOME (Withdraw amt))
      else (False, NONE)

    deposit : BankAccount -> Int -> unit * BAEff
    fun deposit ctxt amt = ((), Deposit amt)
{% endhighlight %}

The bank account implementor has specified that getBalance has to
return a positive integer always. No other specification has been
written. Note that this is a typical implementation of a sequential
BankAccount.

How do we go about deriving a consistency contract? Since we have some
information about the expected behaviour of getBalance, let us start
there. getBalance computes balance by folding over the input set of
effects (represented as list `ctxt`). This input set of effects is the
_visibility set_ for the effect (η) produced by the current getBalance
function. This set is sometimes denoted vis(η). Since ctxt is the list
representation of this set, we have:

    Rmem(ctxt) = vis(η)   ---> Membership Hypothesis

Where Rmem(l) is the set of all elements in l. Note that, as a
notational convenence, we use (a ∈ vis(η)) and vis(a,η)
interchangeably.

One way to ensure that the result of foldl is &gt;=0 is by ensuring
that this invariant holds locally for every prefix of the input list.
This can be done by verifying that folding function has type:

    BAEff -> {v: Int | v>=0} -> {v: Int | v>=0} 

But, not all lists representing vis(η) admit such local reasoning even
though the result of folding the entire list is &gt;=0, . For eg,
consider the following list representing vis(η) = {Withdraw 10,
Withdraw 20, Deposit 100}:

    [Withdraw 10, Withdraw 20, Deposit 100]

The result of folding first two elements of the list is &lt;0.
Nevertheless, such logs can always be reordered:

    [Deposit 100, Withdraw 10, Withdraw 20]

Infact, as a result of our backward reasoning, we even derive the
ordering requirements on the list representation of vis(η) so as to
satisfy the &gt;=0 constraint for every prefix of the list.

Let us verify whether the folding function used in getBalance has
required type. The definition of getBalance is reproduced below:

{% highlight ocaml %}
    getBalance : BankAccount -> unit -> PostInt * BAEff option
    fun getBalance ctxt () = 
        let val bal = foldl ba 0 
          (fn b => fn sum => 
            case b of Deposit x => sum + x
             | Withdraw x => sum - x)
        in
            (bal, NONE)
        end
{% endhighlight %}

Observe that verification fails for the `case Withdraw` because we
have no assurance that sum &gt;= x.  For the verification to succeed,
we need a proof that (sum&gt;=x). Since sum is effectively the result
of applying getBalance on a prefix of the ctxt preceding the Withdraw
effect (call it ctxt'), we have:

    (sum >= x) <=> (getBalance(ctxt') >= x). 

Although the above assertion is a result of simple rewriting, it
provides us with an insight: (sum &gt;= x) holds if and only if
getBalance returns an amount &gt;=x whenever (Withdraw x) effect is
appended to ctxt.

The only operation generating a Withdraw effect is withdraw, and this
effect is produced only under the condition (getBalance(ctxt'') &gt;=
x), where ctxt'' is the context (a list representation of the
visibility set) for withdraw. In order for the verification to go
through, we require a φ such that:

    φ ∧ (x>=0) ∧ (getBalance(ctxt'') >= x) ⊢ (getBalance(ctxt') >= x)

Recall that arguments of Withdraw and Deposit are non-negative
amounts. This is the reason we have (x&gt;0) before turnstile. The
above constraint is of the form:

    (x>=0) ∧ φ ∧ (z>=x) ⊢ (y>=x)

The weakest non-trivial solution to φ is (y&gt;=z). Further, (x&gt;=0)
lets us deduce (z&gt;=0 ∧ y&gt;=0). This means, we now require a φ'
such that:

    (getBalance(ctxt')>=0) ∧ (getBalance(ctxt'')>=0) ∧ φ' ⊢ getBalance(ctxt') >= getBalance(ctxt'')

The only information we have about ctxt' and ctxt'' is that they
contain effects of type Deposit and Withdraw. The trivial solution to
φ is (ctxt' = Nil ∧ ctxt'' = Nil), but we are not interested in this
solution. Neither is the trivial solution weakest. The weakest φ which
proves the validity of above assertion is the conjunction of two
assertions stated below:

1. ∀(a ∈ ctxt''). isDeposit(a) => a ∈ Rmem(ctxt')
2. ∀(a ∈ ctxt'). isWithdraw(a) => a ∈ Rmem(ctxt'')

Basically, if all Deposits present in ctxt'' are present in ctxt', and
if all Withdraws present in ctxt' are present in ctxt'', then there is
no way getBalance on ctxt' returns an amount less than what it returns
on ctxt''.

Recall that we started from getBalance operation, and ctxt'' is
nothing but the context (a list representation of the visibility set)
of a Withdraw operation, which is visible to the current getBalance
operation (see definition of getBalance above).  Lets call that
withdraw operation as b. If we denote the effect of the current
getBalance operation with η, then (1) can be rephrased as:

    ∀a. isDeposit(a) ∧ vis(a,b) => a ∈ Rmem(ctxt')       —> 1(a)

ctxt' is a prefix of getBalance’s context before the operation b. In
the spirit of Catalyst, lets denote the left-to-right order in a list
as Robs, such that if x occurs-before y in a list l, then (x,y) ∈
Robs(l), or equivalently Robs(l,x,y) <=> true. Since ctxt' is the
prefix of ctxt preceding 'b', we have :

    a ∈ Rmem(ctxt') <=> a ∈ Rmem(ctxt) ∧ Robs(ctxt,a,b)

Since Rmem(ctxt) is simply vis(η) (see _Membership Hypothesis_ above),
we have:

    a ∈ ctxt' <=> vis(a,η) ∧ Robs(ctxt,a,b)

Using the above assertion to rewrite 1(a), we get:

    ∀a. isDeposit(a) ∧ vis(a,b) => vis(a,η) ∧ Robs(ctxt,a,b)     —> 1(b)

Now, b is some Withdraw effect in visibility set of current
getBalance. We don’t have a handle on b. So, lets generalize b in
1(b):

    ∀(a,b). vis(b,η) ∧ isWithdraw(b) ∧ isDeposit(a) ∧ vis(a,b) => 
            vis(a,η) ∧ Robs(ctxt,a,b)     —> 1(c)

Since (A => B ∧ C) => (A => B)  ∧ (A ∧ B => C), the
above assertion can be split as:

    ∀(a,b). vis(b,η) ∧ isWithdraw(b) ∧ isDeposit(a) 
                             ∧ vis(a,b) => vis(a,η)           —> 1(d)
    ∀(a,b). vis(b,η) ∧ isWithdraw(b) ∧ isDeposit(a) 
              ∧ vis(a,b) ∧ vis(a,η)=> Robs(ctxt,a,b)          —> 1(e)

Observe that while 1(d) is the **actual Quelea contract over
getBalance**, 1(e) gives us a necessary (but not sufficient) condition
on reordering needed to satisfy the local invariant of fold. 1(e)
effectively insists that we reorder all deposits before withdraws in
ctxt. Further, an environment with 1(d) and 1(e) cannot derive False;
so, we have one consistent set of pre-conditions for getBalance to
return non-negative balance.

Now, lets consider the second conjunct of φ. As with the previous
conjunct, we name the Withdraw operation, whose visibility set is
ctxt'' as b. Therefore, (2) becomes:

    ∀a. (a ∈ Rmem(ctxt')) ∧  isWithdraw(a) ∧ a≠b => vis(a,b)   —> 2(a)

With similar reasoning we did with the first conjunct, we replace
ctxt' with ctxt recording the re-ordering assumption:

    ∀a. isWithdraw(a) ∧ vis(a,η) ∧ Robs(ctxt,a,b)  => vis(a,b)   —> 2(b)

Generalizing ‘b’:

    ∀(a,b).  isWithdraw(a) ∧ vis(a,η) ∧ isWithdraw(b) ∧ vis(b,η) 
                                  ∧ Robs(ctxt,a,b) => vis(a,b)   —> 2(c)

The above assertion effectively says that if two Withdraw effects (w1
and w2) are visible to a get balance, then w1 can occur before w2 in
the context only if w1 is visible to w2. The assertion expresses a
constraint over ordering of effects in ctxt, but it does not give us
the contract needed. To derive the contract, we need to remove the
reference to Robs(ctxt,a,b) from 2(c), since it is a local property.
For this, we start with the observation that by changing the order of
bound variables, 2(c) can be equivalently rephrased as:

    ∀(b,a).  isWithdraw(b) ∧ vis(b,η) ∧ isWithdraw(a) ∧ vis(a,η) 
                                      ∧ Robs(ctxt,b,a) => vis(b,a)   —> 2(d)

Since (A => B) ∧ (C => D) => (A ∨ C => B ∨ D), we get
the following from 2(c) and 2(d):

    ∀(a,b).  isWithdraw(a) ∧ vis(a,η) ∧ isWithdraw(b) ∧ vis(b,η) 
            ∧ Robs(ctxt,a,b) ∨ Robs(ctxt,b,a) => vis(a,b) ∨ vis(b,a)  —> 2(e)

Recall that Rmem and Robs relations satisfy the following property for
a list l:

    ∀(a,b). (a ∈ Rmem(l)) ∧ (b ∈ Rmem(l)) ∧ a≠b => (a,b) ∈ Robs(l) ∨ (b,a) ∈ Robs(l)

Basically, if a and b are elements in a list l, then either a occurs
before b or the converse is true. Substituting ctxt for l, followed by
substituting  vis(a,η) for a (a ∈ Rmem(ctxt)) in the above lemma, we
get:

    ∀(a,b). vis(a,η) ∧ vis(b,η) ∧ a≠b => Robs(ctxt,a,b) ∨ Robs(ctxt,b,a)  —> 2(f)

We get the following from 2(e) and 2(f):

    ∀(a,b).  isWithdraw(a) ∧ vis(a,η) ∧ isWithdraw(b) ∧ vis(b,η) ∧ a≠b  
                                            => vis(a,b) ∨ vis(b,a)  —> 2(h)

Observe that above is a syntactically valid formula in our contract
language.  It says that if getBalance sees two withdraws, then one of
them must be visible to other. While, assertions 1(d) and 2(h)
are axiomatic specifications that guarantee that getBalance never
returns a negative balance, the ordering guarantees expressed in 1(e)
and 2(c) sufficient to make sure that no intermediate result of foldl
in getBalance is a negative number. 

Assertion 2(h) imposes total order on only those withdraw operations
that are visible to getBalance. This consistent with the observation
that if there are no getBalance operations in an execution, there is
no need for total order withdraws. Unfortunately, 2(h) is not
WellFormed as per our classification rules. This is because 2(h)
constraints visibility between Withdraw effects already generated.
Concretely, RHS of implication in 2(h) is vis(a,b), where neither a
nor b is the current effect. 

The weakest well-formed contract stronger than 2(h) is a contract on
withdraw operation (note: not getBalance) that imposes total order on
all withdraws (η in the formula below is a Withdraw effect):

    ∀a. isWithdraw(a) ∧ a≠η => vis(a,η) ∨ vis(η,a)

Conclusion
==========

By primarily relying on membership and ordering properties of lists,
we have formally derived Quelea contracts on getBalance and withdraw.
