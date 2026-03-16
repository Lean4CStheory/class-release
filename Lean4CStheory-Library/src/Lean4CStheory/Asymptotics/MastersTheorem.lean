import Mathlib
import Lean4CStheory.Asymptotics.BigO

namespace Lean4CStheory.Asymptotics

/-!
# Master's Theorem Library

This file provides reusable asymptotic results for standard divide-and-conquer
recurrences.

The purpose of this file is to separate:
- the definition of an algorithm and its cost recurrence, from
- the asymptotic theorem used to conclude a Big-O bound.

In typical use, a student or library user proves that a concrete cost function
satisfies one of the recurrence templates in this file, and then applies the
corresponding theorem to obtain the asymptotic result.

The file contains two groups of results:

1. **Specialized recurrence theorems** for common patterns such as Merge Sort,
   Binary Search, and Median-of-Medians.
2. **A fully general Master theorem interface** for recurrences of the form

   `T(n) ≤ a * T(n / b) + k * (n+1)^c`

   where:
   - `a` is the recursive branching factor,
   - `b` is the input-size reduction factor,
   - `k` is the coefficient of the non-recursive work,
   - `c` is the exponent of the non-recursive work.

The specialized theorems are intended for direct use in common algorithm proofs.
The general theorem is intended for broader reuse across algorithms that do not
fit one of the predefined templates exactly.
-/

/-- Size of the left subproblem, namely `⌊n / 2⌋`. -/
def halfA (n : ℕ) : ℕ := n / 2

/-- Size of the right subproblem, namely `n - ⌊n / 2⌋`. -/
def halfB (n : ℕ) : ℕ := n - (n / 2)

/--
A total logarithm function used in asymptotic bounds.

We use `log₂(n+1)` instead of `log₂(n)` so that the function is defined for all
`n : ℕ`, including `n = 0`.

This is convenient when stating Big-O bounds on functions over all natural
numbers.
-/
def log2p1 (n : ℕ) : ℕ := Nat.log 2 (n + 1)

/--
Master theorem for two balanced subproblems with linear combine cost.

## Intended recurrence
Use this theorem when the running time satisfies, for all `n ≥ 2`,

`T(n) ≤ T(⌊n/2⌋) + T(n - ⌊n/2⌋) + c * n`.

## Conclusion
The theorem concludes that `T(n)` is Big-O of `n * log₂(n+1)`.

## Typical use cases
This form covers standard divide-and-conquer algorithms with:
- two approximately equal recursive calls, and
- linear work to combine the results.

Examples include:
- Merge Sort,
- inversion counting by merge,
- similar balanced split-and-merge algorithms.
-/
axiom Master_halves_plus_linear
  (T : ℕ → ℕ) (c : ℕ) :
  (∀ n ≥ 2,
      T n ≤ T (halfA n) + T (halfB n) + c * n) →
  T =O (fun n => n * log2p1 n)

/--
Master theorem for two balanced subproblems with constant combine cost.

## Intended recurrence
Use this theorem when the running time satisfies, for all `n ≥ 2`,

`T(n) ≤ T(⌊n/2⌋) + T(n - ⌊n/2⌋) + c`.

## Conclusion
The theorem concludes that `T(n)` is Big-O of `n`.

## Typical use cases
This is appropriate when an algorithm makes two balanced recursive calls but
does only constant additional work outside the recursive calls.
-/
axiom Master_halves_plus_const
  (T : ℕ → ℕ) (c : ℕ) :
  (∀ n ≥ 2,
      T n ≤ T (halfA n) + T (halfB n) + c) →
  T =O (fun n => n)

/--
Master theorem for one recursive subproblem of half size with constant combine cost.

## Intended recurrence
Use this theorem when the running time satisfies, for all `n ≥ 2`,

`T(n) ≤ T(⌊n/2⌋) + c`.

## Conclusion
The theorem concludes that `T(n)` is Big-O of `log₂(n+1)`.

## Typical use cases
This form models recurrences such as Binary Search, where:
- only one recursive branch is explored, and
- the non-recursive work is constant.
-/
axiom Master_one_half_plus_const
  (T : ℕ → ℕ) (c : ℕ) :
  (∀ n ≥ 2,
      T n ≤ T (halfA n) + c) →
  T =O (fun n => log2p1 n)

/--
Master theorem for one recursive subproblem of half size with linear combine cost.

## Intended recurrence
Use this theorem when the running time satisfies, for all `n ≥ 2`,

`T(n) ≤ T(⌊n/2⌋) + c * n`.

## Conclusion
The theorem concludes that `T(n)` is Big-O of `n`.

## Typical use cases
This applies when an algorithm reduces the problem size by a factor of two,
recurses on only one subproblem, and performs linear additional work.
-/
axiom Master_one_half_plus_linear
  (T : ℕ → ℕ) (c : ℕ) :
  (∀ n ≥ 2,
      T n ≤ T (halfA n) + c * n) →
  T =O (fun n => n)

/--
Master theorem for the Median-of-Medians recurrence.

## Intended recurrence
Use this theorem when the running time satisfies, for all `n ≥ 2`,

`T(n) ≤ T(⌈n/5⌉) + T(⌈7n/10⌉) + c * n`.

In this file, the ceiling expressions are encoded arithmetically as:
- `(n + 4) / 5` for `⌈n/5⌉`,
- `(7 * n + 9) / 10` for `⌈7n/10⌉`.

## Conclusion
The theorem concludes that `T(n)` is Big-O of `n`.

## Typical use cases
This recurrence is used in the analysis of the deterministic linear-time
selection algorithm, commonly known as Median-of-Medians.
-/
axiom Master_medianOfMedians_linear
  (T : ℕ → ℕ) (c : ℕ) :
  (∀ n ≥ 2,
      T n ≤ T ((n + 4) / 5) + T ((7 * n + 9) / 10) + c * n) →
  T =O (fun n => n)

/-!
## Fully General Master Theorem

The remainder of this file provides a more general Master theorem for real-valued
cost functions.

This interface is intended for recurrences of the form

`T(n) ≤ a * T(n / b) + k * (n+1)^c`

where:
- `T : ℕ → ℝ` is the cost function,
- `a : ℝ` is the multiplicative factor on the recursive term,
- `b : ℕ` is the divisor controlling input shrinkage,
- `k : ℝ` is the coefficient of the non-recursive term,
- `c : ℝ` is the exponent of the non-recursive term.

The critical exponent is `log_b(a)`. The three standard Master-theorem cases are:
- `c < log_b(a)`
- `c = log_b(a)`
- `log_b(a) < c`

This file exposes:
- internal axioms for the three separate cases, and
- one public dispatcher theorem `Master_general` that users should call.

Users of this file should normally apply `Master_general` rather than invoking
the case-specific axioms directly.
-/

/--
The real-valued quantity `n + 1`.

This is used instead of `n` in logarithms and real powers so that expressions
remain well-defined at `n = 0`.
-/
def nplus1 (n : ℕ) : ℝ := (n : ℝ) + 1

noncomputable section

/--
Real logarithm base change.

`logb a b` denotes `log_b(a)` and is defined as

`Real.log a / Real.log b`.

This is the critical exponent expression used in the general Master theorem.
-/
def logb (a b : ℝ) : ℝ := Real.log a / Real.log b

/--
The quantity `log_b(n+1)` viewed as a real number.

This function is used in the equality case of the Master theorem, where the
asymptotic bound includes an additional logarithmic factor.
-/
def logbp1R (b : ℝ) (n : ℕ) : ℝ := Real.log (nplus1 n) / Real.log b

/--
The quantity `(n+1)^x` using real exponentiation.

This is used to express the non-recursive work term and the resulting
asymptotic bounds in the fully general theorem.
-/
def powR (n : ℕ) (x : ℝ) : ℝ := Real.rpow (nplus1 n) x

end

/--
Case 1 of the fully general Master theorem.

## Intended recurrence
Use this result when:
- `a ≥ 1`,
- `b ≥ 2`,
- `k ≥ 0`,
- `c < log_b(a)`,
- and for all `n ≥ 2`,

  `T(n) ≤ a * T(n / b) + k * (n+1)^c`.

## Conclusion
The theorem concludes

`T =OR (fun n => (n+1)^(log_b(a)))`.

## Note
This is the case where the recursive work dominates the non-recursive work.
For ordinary use, prefer `Master_general`, which dispatches to this case
internally.
-/
axiom Master_general_rpow_lt
  (T : ℕ → ℝ) (a k : ℝ) (b : ℕ) (c : ℝ) :
  (1 ≤ a) →
  (2 ≤ b) →
  (0 ≤ k) →
  (c < logb a (b : ℝ)) →
  (∀ n ≥ 2, T n ≤ a * T (n / b) + k * powR n c) →
  T =OR (fun n => powR n (logb a (b : ℝ)))

/--
Case 2 of the fully general Master theorem.

## Intended recurrence
Use this result when:
- `a ≥ 1`,
- `b ≥ 2`,
- `k ≥ 0`,
- `c = log_b(a)`,
- and for all `n ≥ 2`,

  `T(n) ≤ a * T(n / b) + k * (n+1)^c`.

## Conclusion
The theorem concludes

`T =OR (fun n => (n+1)^(log_b(a)) * log_b(n+1))`.

## Note
This is the balanced case where the recursive term and non-recursive term have
the same asymptotic order.

For ordinary use, prefer `Master_general`, which dispatches to this case
internally.
-/
axiom Master_general_rpow_eq
  (T : ℕ → ℝ) (a k : ℝ) (b : ℕ) (c : ℝ) :
  (1 ≤ a) →
  (2 ≤ b) →
  (0 ≤ k) →
  (c = logb a (b : ℝ)) →
  (∀ n ≥ 2, T n ≤ a * T (n / b) + k * powR n c) →
  T =OR (fun n => powR n (logb a (b : ℝ)) * logbp1R (b : ℝ) n)

/--
Case 3 of the fully general Master theorem.

## Intended recurrence
Use this result when:
- `a ≥ 1`,
- `b ≥ 2`,
- `k ≥ 0`,
- `log_b(a) < c`,
- the regularity condition holds,
- and for all `n ≥ 2`,

  `T(n) ≤ a * T(n / b) + k * (n+1)^c`.

## Regularity condition
The theorem requires the existence of `r < 1` such that, for all `n ≥ 2`,

`a * (k * (n/b+1)^c) ≤ r * (k * (n+1)^c)`,

as encoded by the theorem statement.

## Conclusion
The theorem concludes

`T =OR (fun n => k * (n+1)^c)`.

## Note
This is the case where the non-recursive work dominates the recursive work.

For ordinary use, prefer `Master_general`, which dispatches to this case
internally.
-/
axiom Master_general_rpow_gt
  (T : ℕ → ℝ) (a k : ℝ) (b : ℕ) (c : ℝ) :
  (1 ≤ a) →
  (2 ≤ b) →
  (0 ≤ k) →
  (logb a (b : ℝ) < c) →
  (∃ r : ℝ, r < 1 ∧
    ∀ n ≥ 2,
      a * (k * powR (n / b) c) ≤ r * (k * powR n c)) →
  (∀ n ≥ 2, T n ≤ a * T (n / b) + k * powR n c) →
  T =OR (fun n => k * powR n c)

/--
Enumeration of the three standard cases of the general Master theorem.

This type is used as an input to `Master_general` so that callers can specify
which asymptotic case they are proving.
-/
inductive MasterCase where
  /-- Case 1: `c < log_b(a)` -/
  | lt
  /-- Case 2: `c = log_b(a)` -/
  | eq
  /-- Case 3: `log_b(a) < c` -/
  | gt
deriving DecidableEq

/--
The asymptotic bound corresponding to a chosen `MasterCase`.

This definition packages the output shape of the Master theorem into a single
function so that `Master_general` can expose one uniform conclusion.

## Meaning by case
- `MasterCase.lt` gives `(n+1)^(log_b(a))`
- `MasterCase.eq` gives `(n+1)^(log_b(a)) * log_b(n+1)`
- `MasterCase.gt` gives `k * (n+1)^c`
-/
noncomputable def masterBound
    (a k : ℝ) (b : ℕ) (c : ℝ) (cs : MasterCase) : ℕ → ℝ :=
  match cs with
  | .lt => fun n => powR n (logb a (b : ℝ))
  | .eq => fun n => powR n (logb a (b : ℝ)) * logbp1R (b : ℝ) n
  | .gt => fun n => k * powR n c

/--
Public entry point for the fully general Master theorem.

This theorem is the main interface intended for external use.

## Intended recurrence
Apply this theorem when you have proved that a real-valued cost function
`T : ℕ → ℝ` satisfies

`T(n) ≤ a * T(n / b) + k * (n+1)^c`

for all `n ≥ 2`, together with the standard side conditions:
- `1 ≤ a`,
- `2 ≤ b`,
- `0 ≤ k`.

## How to use
To apply this theorem, the caller must provide:
- the recurrence parameters `a`, `b`, `k`, `c`,
- the case selector `cs : MasterCase`,
- a proof that the corresponding case inequality/equality holds,
- a proof of the regularity condition when `cs = MasterCase.gt`,
- and the recurrence inequality itself.

## Output
The theorem concludes

`T =OR (masterBound a k b c cs)`,

where `masterBound` expands to the appropriate asymptotic form for the chosen
case.

## Design note
This theorem is intended to be the stable API exposed to students and users of
the library. The case-specific axioms remain available internally, but typical
algorithm proofs should call `Master_general`.
-/
theorem Master_general
    (T : ℕ → ℝ) (a k : ℝ) (b : ℕ) (c : ℝ) (cs : MasterCase) :
    (1 ≤ a) →
    (2 ≤ b) →
    (0 ≤ k) →
    (match cs with
     | .lt => c < logb a (b : ℝ)
     | .eq => c = logb a (b : ℝ)
     | .gt => logb a (b : ℝ) < c) →
    (match cs with
     | .gt =>
         ∃ r : ℝ, r < 1 ∧
           ∀ n ≥ 2,
             a * (k * powR (n / b) c) ≤ r * (k * powR n c)
     | _ => True) →
    (∀ n ≥ 2, T n ≤ a * T (n / b) + k * powR n c) →
    T =OR (masterBound a k b c cs) := by
  intro ha hb hk hcase hreg hrec
  cases cs with
  | lt =>
      simpa [masterBound] using
        (Master_general_rpow_lt
          (T := T) (a := a) (k := k) (b := b) (c := c)
          ha hb hk hcase hrec)
  | eq =>
      simpa [masterBound] using
        (Master_general_rpow_eq
          (T := T) (a := a) (k := k) (b := b) (c := c)
          ha hb hk hcase hrec)
  | gt =>
      simpa [masterBound] using
        (Master_general_rpow_gt
          (T := T) (a := a) (k := k) (b := b) (c := c)
          ha hb hk hcase hreg hrec)

end Lean4CStheory.Asymptotics
