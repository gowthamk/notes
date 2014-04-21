---
layout: post
title:  "Implementation Observations"
---
# Observations about parametric relations #

## Introduction ##

Here, we record observations that we make about parametric relations
while we are in the process of implementing verification algorithm.

## 1. Params - Type variables analogy ##

Parameters are to relations what type variables are to ML type
constructors. Just as type variables range over monotypes, params
range over simple projections. Just as a type scheme is fully
instantiated, a parametric relation has to be fully instantiated. Just
as a type var can be instantiated with another type var, a param can
be instantiated with another param. Just as type var cannot be
instantiated with a type scheme, a parameter cannot be instantiated
with a parametric relation.

However, while type var ranges over all monotypes, a param has a
colon-arrow associated with it, which restricts the relations that it
can be instantiated with.
