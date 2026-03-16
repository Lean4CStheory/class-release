/-
Copyright (c) 2025 Sorrachai Yingchareonthawornhcai.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornhcai

Copied from the cslib project:
https://github.com/leanprover-community/cslib

Vendored into Lean4CStheory for stability with mathlib v4.24.0.
No functional changes have been made.
-/

import Mathlib

/-!
# TimeM: Time Complexity Monad

`TimeM α` represents a computation that produces a value of type `α`
while also recording an associated time cost.

This abstraction is useful when modeling algorithms where the implementation
and its cost should be tracked together. A `TimeM` value stores both the
result of the computation and the accumulated running time.

## Structure

A value of type `TimeM α` contains two components:

* `ret : α`
  The returned value of the computation.

* `time : ℕ`
  The accumulated time cost associated with the computation.

This allows algorithms to return their output while also carrying a
cost metric that can be analyzed separately.

## Design Principles

The design follows a few simple principles:

1. **Pure inputs, timed outputs**
   Inputs remain ordinary values, while outputs include both the result
   and the recorded cost.

2. **Explicit cost accounting**
   Time is recorded explicitly through `tick` operations rather than
   being inferred automatically.

3. **Separation of concerns**
   Functional correctness typically concerns `.ret`, while
   complexity analysis typically concerns `.time`.

## Typical Usage

A common workflow when using `TimeM` is:

1. Implement an algorithm in `TimeM` so that important steps contribute
   to the recorded cost.
2. Reason about the algorithm’s functional behavior using `.ret`.
3. Define a mathematical cost function representing the intended
   complexity model.
4. Prove that the recorded `.time` value is bounded by that cost model.

This separation makes it possible to reason about correctness and
complexity independently.

## Core Operations

The following operations define the behavior of the `TimeM` monad:

* `pure a`
  Returns `a` with time cost `0`.

* `bind m f`
  Runs computation `m`, feeds its result into `f`, and accumulates the
  total time cost.

* `tick a c`
  Returns value `a` while recording cost `c`.

* `✓ a`
  Notation for `tick a` with default cost `1`.

These operations allow algorithm implementations to accumulate cost
in a controlled and explicit way.

## Example Intuition

A computation step that produces a result and incurs unit cost can be written as:

`✓ result`

If a computation performs a recursive call followed by additional work,
the total cost is accumulated automatically through `bind`.

## Notes

`TimeM` models time through explicit annotations. The recorded values
represent a chosen cost model and are not automatically validated as
true runtime measurements. Formal analysis should therefore justify the
relationship between the recorded cost and the intended complexity bound.
-/

namespace Lean4CStheory.Time

/--
A monad for computations that return a value together with a recorded time cost.

A value of type `TimeM α` stores:
- `ret  : α`   — the returned result
- `time : ℕ`   — the accumulated time cost
-/
structure TimeM (α : Type*) where
  ret  : α
  time : ℕ

namespace TimeM

/--
Return a value with zero time cost.

This is the `TimeM` analogue of a pure computation:
it produces a result but records no work.
-/
@[scoped grind =]
def pure {α} (a : α) : TimeM α :=
  ⟨a, 0⟩

/--
Sequential composition of timed computations.

If `m` computes a value of type `α`, and `f` continues the computation using
that value, then:
- the final returned value is the result of `f m.ret`,
- the final time is the sum of the time of `m` and the time of `f m.ret`.

This is the operation that makes recorded cost accumulate across recursive
and multi-step computations.
-/
@[scoped grind =]
def bind {α β} (m : TimeM α) (f : α → TimeM β) : TimeM β :=
  let r := f m.ret
  ⟨r.ret, m.time + r.time⟩

/--
`TimeM` carries a monad structure.

This allows the use of standard monadic notation such as `do` blocks
when writing timed algorithms.
-/
instance : Monad TimeM where
  pure := pure
  bind := bind

/--
Return a value while charging a specified time cost.

`tick a c` produces the value `a` and records cost `c`.
If the cost argument is omitted, the default cost is `1`.
-/
@[simp, grind =]
def tick {α : Type*} (a : α) (c : ℕ := 1) : TimeM α :=
  ⟨a, c⟩

/--
Notation for `tick` and result extraction.

* `✓ a, c` means “return `a` and charge cost `c`”
* `✓ a` means “return `a` and charge cost `1`”
* `⟪tm⟫` extracts the returned value of a timed computation
-/
scoped notation "✓" a:arg ", " c:arg => tick a c
scoped notation "✓" a:arg => tick a
scoped notation:max "⟪" tm "⟫" => (TimeM.ret tm)

/--
A unit-valued computation with cost `1`.

This is convenient when a computation step does not need to return
meaningful data but should still contribute one unit of time.
-/
def tickUnit : TimeM Unit :=
  ✓ ()

/--
The time of a pure computation is `0`.
-/
@[simp] theorem time_of_pure {α} (a : α) :
  (pure a).time = 0 := rfl

/--
The time of a bound computation is the sum of the times of its two stages.
-/
@[simp] theorem time_of_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (bind m f).time = m.time + (f m.ret).time := rfl

/--
The time recorded by `tick a c` is exactly `c`.
-/
@[simp] theorem time_of_tick {α} (a : α) (c : ℕ) :
  (tick a c).time = c := rfl

/--
The returned value of a bound computation is the returned value
produced by the second stage.
-/
@[simp] theorem ret_bind {α β} (m : TimeM α) (f : α → TimeM β) :
  (bind m f).ret = (f m.ret).ret := rfl

/-
These simp attributes allow Lean to simplify monadic expressions involving
`pure` and `bind` more easily in later proofs.
-/
attribute [simp] Bind.bind Pure.pure TimeM.pure TimeM.bind

end TimeM
end Lean4CStheory.Time
