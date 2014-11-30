---
layout: post
title:  "Broom Type System - Related Work"
---

Broom System
============

For the sake of the discussion, we assume that system comprises of a
set of actors, each with an Actor Id (_actId_). An actor is an
instantiation of a class that belongs to an application. All actors
run on the same machine sharing same physical memeory, and communicate
by message passing. 

Memory Management
=================

In Broom, memory is allocated to actors in terms of blocks called regions. Three
kinds of regions can be identified in Broom:

+ Private Regions : A private region is a block of memory that is
  private to the actor to which is was allocated. Memory for local
  variables of methods within the actor, and data structures that are
  private to the actor are allocated in its private regions. Actor's
  private regions can be made to abide by the LIFO discipline, with
  following characteristics:

  1. A private stack region is allocated to an actor whenever it
     executes a method call. Such region essentially seves as an
     activation record for the method being called. As with activation
     records, private stack regions form a stack of regions, where
     regions at higher addresses in the stack (stack is assumed to
     grow downwards) have longer lifetime than those at lower
     addresses. A private stack region can be deallocated as soon as
     its corresponding method call returns.
  2. A private heap region is allocated to an actor at the beginning
     of actor's life time, and outlives all its stack regions. Data
     stored in actor's heap region is assumed to persist throughout
     the lifetime of the actor.

+ Transferable Regions : A transferable region is a block of memory
  that is allocated/deallocated to an actor on demand. Subsequent to
  the allocation, the actor to which the transferable region is
  allocated is its unique _owner_. Owner of a transferable region can
  allocated/deallocate objects into the region. An actor can chose to
  transfer the ownership to another actor (whence _transferable_
  region). Subsequent to the transfer, the former is no longer allowed
  to refer into the region. It can be observed that a transferable
  region and the act of ownership transfer effectively model a
  message, and the act of passing the message between different
  actors, respectively.  Ownership transfer effectively ends the
  lifetime of transferable region as far as its owner is concerned.
  Alternatively, the owner of a transferable region can chose to
  deallocate it, marking the real end of region's life time.
  Transferable regions mark the departure from LIFO discipline among
  lifetimes of regions. Following observations can be made:

  1. Depending on when it is allocated and deallocated, a transferable
     region can outlive multiple private (stack) regions of its owner,
     or it may outlive none. Example for first case is when a
     transferable region is allocated at the beginning of actor's
     lifetime, updated throughout its lifetime via multiple method
     calls, and is transferred to another actor, or simply
     deallocated, just before the end of actor's life time. 

