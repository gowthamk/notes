---
layout: post
title:  "Haskell Comparision"
---

Possible plan for the talk

1. Higher-order verification is inherently difficult.
  a. Decision procedures are atmost first-order
  b. Combination of theories is undecidable
2. Most widely used higher-order functions are morphisms over
   algebraic datatypes - map, fold, zip etc. 
3. It is helpful to think of their invariants in terms of shapes of
   these algebras.
4. Consider reverse function. Can we relate the shapes of input and
   result lists? Our aim is to scale this approach to higher-order;
   so, straightforward SMT based solutions do not work.
5. Observe that we can do it with structural relations.
6. Structural relations scale to polymorphism and higher-order
   functions.
6. With relations, there is no need for specialized theories, such as
   theory of algebraic datatypes. Furthermore, first-order equational
   and relational logic is decidable.
7. Demonstrate encoding
8. Case studies

