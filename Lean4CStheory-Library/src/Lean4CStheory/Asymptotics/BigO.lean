import Mathlib

namespace Lean4CStheory.Asymptotics

/-!
# Big-O Notation

This file defines asymptotic upper-bound relations used in runtime analysis.

Two versions are provided:

* `BigO` for functions `ℕ → ℕ`
* `BigOR` for functions `ℕ → ℝ`

The natural-valued version is convenient for many discrete cost functions,
while the real-valued version is useful when logarithms, real powers, or
other non-integer growth rates appear.

The intended reading of

`f =O g`

is:

> beyond some threshold input size, `f(n)` is at most a constant multiple of `g(n)`.

Similarly, `f =OR g` gives the corresponding notion for real-valued functions.

## Purpose of this file

This file provides:
- the definitions of `BigO` and `BigOR`,
- basic closure and comparison lemmas,
- simple example bounds,
- and a few helper lemmas for polynomial upper bounds.

These lemmas are intended to support asymptotic proofs in algorithm files.
-/

/-!
## Definition of Big-O for `ℕ → ℕ`
-/

/--
`BigO f g` means that `f` is asymptotically bounded above by `g`.

Formally, there exist constants `C` and `n₀` such that for all `n ≥ n₀`,
the inequality `f n ≤ C * g n` holds.
-/
def BigO (f g : ℕ → ℕ) : Prop :=
  ∃ C n₀ : ℕ, ∀ n ≥ n₀, f n ≤ C * g n

/-- Notation for natural-valued Big-O. -/
notation f " =O " g => BigO f g

/-!
## Definition of Big-O for `ℕ → ℝ`

This real-valued version is useful when the target bound involves logarithms,
fractional exponents, or other real-valued expressions.
-/

/--
`BigOR f g` means that the real-valued function `f` is asymptotically bounded
above by the real-valued function `g`.

Formally, there exist a nonnegative constant `C` and a threshold `N₀` such that
for all `n ≥ N₀`, the inequality `f n ≤ C * g n` holds.
-/
def BigOR (f g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, f n ≤ C * g n

/-- Notation for real-valued Big-O. -/
notation f " =OR " g => BigOR f g

/-!
## Basic properties of Big-O

The lemmas in this section provide a small core toolbox for routine
asymptotic arguments.
-/

/--
Reflexivity of Big-O.

Every function is asymptotically bounded by itself.
-/
theorem BigO_refl (f : ℕ → ℕ) : f =O f := by
  refine ⟨1, 0, ?_⟩
  intro n hn
  simp

/--
Transitivity of Big-O.

If `f =O g` and `g =O h`, then `f =O h`.
-/
theorem BigO_trans {f g h : ℕ → ℕ} :
  (f =O g) → (g =O h) → (f =O h) := by
  intro ⟨C₁, n₁, h₁⟩
        ⟨C₂, n₂, h₂⟩
  refine ⟨C₁ * C₂, max n₁ n₂, ?_⟩
  intro n hn
  have h₁' := h₁ n (le_of_max_le_left hn)
  have h₂' := h₂ n (le_of_max_le_right hn)
  nlinarith

/--
Monotonicity under pointwise inequality.

If `f n ≤ g n` for all `n`, and `g =O h`, then `f =O h`.
-/
theorem BigO_of_le {f g h : ℕ → ℕ} :
  (∀ n, f n ≤ g n) → (g =O h) → (f =O h) := by
  intro hfg
        ⟨C, n₀, hg⟩
  refine ⟨C, n₀, ?_⟩
  intro n hn
  exact le_trans (hfg n) (hg n hn)

/-!
## Simple example bounds

These lemmas illustrate direct uses of the definition and provide
basic asymptotic facts that often occur in later proofs.
-/

/--
Constant functions are `O(1)`.

That is, the function `fun _ => c` is asymptotically bounded by
the constant function `fun _ => 1`.
-/
theorem BigO_const (c : ℕ) :
  (fun _ => c) =O (fun _ => 1) := by
  refine ⟨c, 0, ?_⟩
  intro n hn
  simp

/--
A constant multiple of `n` is `O(n)`.

That is, `fun n => c * n` is asymptotically bounded by `fun n => n`.
-/
theorem BigO_linear (c : ℕ) :
  (fun n => c * n) =O (fun n => n) := by
  refine ⟨c, 0, ?_⟩
  intro n hn
  rfl

/-!
## Closure properties

The lemmas in this section record a few common ways to build new Big-O bounds
from existing ones.
-/

/--
Big-O is preserved under adding the same function to both sides.

If `f =O g`, then `f + h =O g + h`.
-/
theorem BigO_add {f g h : ℕ → ℕ} :
  (f =O g) →
  ((fun n => f n + h n) =O (fun n => g n + h n)) := by
  intro ⟨C, n₀, hf⟩
  refine ⟨C + 1, n₀, ?_⟩
  intro n hn
  have hf' := hf n hn
  nlinarith

/--
Big-O is preserved under multiplication by a constant on the left.

If `f =O g`, then `fun n => c * f n =O g`.
-/
theorem BigO_mul_const {f g : ℕ → ℕ} (c : ℕ) :
  (f =O g) → ((fun n => c * f n) =O g) := by
  intro ⟨C, n₀, hf⟩
  refine ⟨c * C, n₀, ?_⟩
  intro n hn
  have hf' := hf n hn
  nlinarith

/-!
## Polynomial helper lemmas

These lemmas are intended for routine runtime bounds in algorithm files,
especially when a recurrence has already been reduced to a simple polynomial
upper bound.
-/

/--
A linear function is `O(n²)`.

This records the standard fact that `n ≤ n²` for all sufficiently large `n`.
-/
theorem linear_bigO_quadratic :
  (fun n => n) =O (fun n => n^2) := by
  refine ⟨1, 1, ?_⟩
  intro n hn
  nlinarith

/--
Any polynomial of degree at most `2` is `O(n²)`.

Concretely, the function `fun n => a*n^2 + b*n + c` is asymptotically
bounded by `fun n => n^2`.
-/
theorem poly2_bigO_quadratic (a b c : ℕ) :
  (fun n => a*n^2 + b*n + c) =O (fun n => n^2) := by
  refine ⟨a + b + c, 1, ?_⟩
  intro n hn

  have h1 : b * n ≤ b * n^2 := by
    have : n ≤ n^2 := by
      nlinarith
    nlinarith

  have h2 : c ≤ c * n^2 := by
    have : 1 ≤ n^2 := by
      nlinarith
    nlinarith

  nlinarith

end Lean4CStheory.Asymptotics
