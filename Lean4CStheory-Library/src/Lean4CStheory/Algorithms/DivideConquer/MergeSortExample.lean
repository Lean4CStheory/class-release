import Mathlib
import Lean4CStheory.Asymptotics.MastersTheorem

set_option autoImplicit false

open List
open Lean4CStheory.Asymptotics

/-!
# Divide and Conquer Example: Merge Sort

This file is a worked example showing how to formalize a
**divide-and-conquer algorithm** in Lean.

The goal of this file is not only to define Merge Sort, but also to show a
general template that students can follow for their own chosen algorithm.

## Suggested workflow for your own algorithm

If you choose a divide-and-conquer algorithm, your file should follow the
same broad pattern as this one:

1. **Define the algorithm**
   - identify the divide step,
   - identify the recursive calls,
   - identify the combine step.

2. **State a correctness specification**
   - for example: output is sorted, valid, optimal, etc.
   - in this example, correctness is stated as sortedness.

3. **Define a size-based cost function**
   - this should depend only on the input size `n`,
   - not on the actual input values.

4. **Write the recurrence in theorem-ready form**
   - the Master theorem needs the recurrence written in a precise shape.

5. **Apply the Master theorem**
   - conclude the final asymptotic bound.

## What this example does

This example uses Merge Sort.

- The algorithm splits the list into two halves,
- recursively sorts each half,
- and merges the results.

The final asymptotic result is the standard `O(n log n)` bound, expressed
in the real-valued asymptotic notation used by `MastersTheorem`.
-/

namespace Lean4CStheory.Algorithms.DivideConquer

namespace MergeSort

section alg_def
/-!
## Section 1: Algorithm definition

This section contains the helper definitions and the algorithm itself.

### What students should learn from this section
Your divide-and-conquer algorithm should clearly show:
- the **divide** step,
- the **recursive** step,
- the **combine** step.

In this example:
- `split` is the divide step,
- the recursive calls in `mergeSort` are the conquer step,
- `merge` is the combine step.

This section shows **two definitions** of the algorithm:

* Textbook (*partial*) definitions: This is the textbook description of the algorithm, almost identical to the pseudocode you can see from any algorithm book. It's *partial* because Lean cannot verify that the recursion is well-founded (i.e., guaranteed to terminate). This is the easier version to read, but it is not fully rigorous.

* Rigorous (*total*) definitions: This is the more formal Lean style. It includes termination proofs and gives a fully total definition.

-/

/-!
  ### Helper definitions
-/
/--
A boolean version of “`a ≤ b`” using the `Ord` comparison interface.

We use this helper so that the code for `merge` is easier to read.
-/
def leq {α : Type} [Ord α] (a b : α) : Bool :=
  compare a b != .gt

/--
Split a list into two roughly equal halves.

If the input has length `n`, this returns:
- the first `⌊n/2⌋` elements,
- the remaining elements.
-/
def split {α : Type} (xs : List α) : List α × List α :=
  let half := xs.length / 2
  (xs.take half, xs.drop half)


/-!
  ### The textbook (partial) definition of Merge Sort

  Using `partial def` to avoids explicit termination proofs.
-/

/--
  Merge two sorted `List` to a single sorted `List`.
  Although it is declared as `partial`, it is actually a total def.
  See the definition of `merge` below.
-/
partial def mergeAlg {α : Type} [Ord α] : List α → List α → List α
| [], ys => ys
| xs, [] => xs
| a :: as, b :: bs =>
    if leq a b then
      a :: mergeAlg as (b :: bs)
    else
      b :: mergeAlg (a :: as) bs

/--
This version or mergeSort clearly shows the divide-conquer-combine structure:
- split,
- recursively solve the two subproblems,
- merge the results.
-/
partial def mergeSortAlg {α : Type} [Ord α] : List α → List α
| xs =>
  if xs.length < 2 then
    xs
  else
    let (left, right) := split xs
    mergeAlg (mergeSortAlg left) (mergeSortAlg right)


/-
  ### The rigorous (total) definition of Merge Sort

  This version includes termination proofs.
-/

/-- The left half list returned by `split` is shorter than the input list -/
lemma split_left_shorter {α : Type} (xs : List α) (h : ¬ xs.length < 2) :
    (split xs).1.length < xs.length := by
  simp [split]
  have hlen : 2 ≤ xs.length := by omega
  have hpos : 0 < xs.length := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hlen
  have hdivlt : xs.length / 2 < xs.length :=
    Nat.div_lt_self hpos (by decide : 1 < (2 : ℕ))
  have hle : xs.length / 2 ≤ xs.length := Nat.div_le_self _ _
  simpa [List.length_take, Nat.min_eq_left hle] using hdivlt

/-- The right half list returned by `split` is shorter than the input list -/
lemma split_right_shorter {α : Type} (xs : List α) (h : ¬ xs.length < 2) :
    (split xs).2.length < xs.length := by
  simp [split]
  have hlen : 2 ≤ xs.length := by omega
  have hpos : 0 < xs.length := lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hlen
  have hhalfpos : 0 < xs.length / 2 := by
    exact Nat.div_pos hlen (by decide : 0 < (2 : ℕ))
  have hsublt : xs.length - xs.length / 2 < xs.length := by
    exact Nat.sub_lt hpos hhalfpos
  simpa [List.length_drop] using hsublt

/--
  Merge two sorted lists into a single sorted list.
  The definition is **identital** to the partial def `mergeAlg` above.
  The reason that we don't need to provide a termination proof here is because
  Lean can automatically reason the termination regarding list concatenations.
-/
def merge {α : Type} [Ord α] : List α → List α → List α
| [], ys => ys
| xs, [] => xs
| a :: as, b :: bs =>
    if leq a b then
      a :: merge as (b :: bs)
    else
      b :: merge (a :: as) bs

/-- The merger sort definition with termination proofs -/
def mergeSort {α : Type} [Ord α] : List α → List α
| xs =>
  if h : xs.length < 2 then
    xs
  else
    match hsplit : split xs with
    | (left, right) =>
        -- These two facts are proof-only: Lean uses them to verify that the
        -- recursive calls are on smaller lists, even though they are not
        -- explicit inputs to the final `merge` expression.
        have hleft : left.length < xs.length := by
          simpa [hsplit] using split_left_shorter xs h
        have hright : right.length < xs.length := by
          simpa [hsplit] using split_right_shorter xs h
        merge (mergeSort left) (mergeSort right)
termination_by
  -- The recursion is justified by the length decrease of the input list.
  xs => xs.length

end alg_def

section correctness_spec
/-!
## Section 2: Correctness specification

This section records what it means for the algorithm to be correct.

### What students should learn from this section
A good first step is to write down a precise correctness specification,
even if the full proof is not done yet.

In this example, correctness means:
- the output of `mergeSort` is sorted.

For another divide-and-conquer algorithm, the specification may instead be:
- optimal value,
- valid partition,
- same multiset of elements,
- correct search answer,
- etc.
-/

/--
A boolean sortedness checker for lists.

This is used as a simple, computable correctness specification.
-/
def isSortedList {α : Type} [Ord α] : List α → Bool
| [] => true
| [_] => true
| a :: b :: xs => leq a b && isSortedList (b :: xs)

/--
Correctness specification for Merge Sort.

This proposition says that the output of `mergeSort xs` is sorted.
-/
def mergeSortCorrect {α : Type} [Ord α] (xs : List α) : Prop :=
  isSortedList (mergeSort xs) = true

end correctness_spec

/-!
## Section 3: Size-based cost model

To apply the Master theorem, we define a recurrence depending only on the
input size `n`.

### What students should learn from this section
The cost function should:
- take a natural number `n`,
- represent the worst-case cost on inputs of size `n`,
- follow the same recursive structure as the algorithm.

For Merge Sort, the recurrence is:

`T(n) = T(⌊n/2⌋) + T(n - ⌊n/2⌋) + n`

with base cases `T(0) = 0` and `T(1) = 0`.
-/

/--
Worst-case Merge Sort cost as a function of input size.
-/
def mergeSortCostN : ℕ → ℕ
| 0 => 0
| 1 => 0
| n + 2 =>
    let n' := n + 2
    let a := n' / 2
    let b := n' - a
    mergeSortCostN a + mergeSortCostN b + n'

/--
Real-valued version of the cost function.

The general Master theorem in this library is stated for functions
`ℕ → ℝ`, so we cast the natural-valued recurrence into the reals.
-/
def mergeSortCostNR (n : ℕ) : ℝ :=
  (mergeSortCostN n : ℝ)

/-!
## Section 4: Recurrence assumption in Master-theorem form

The general Master theorem in `MastersTheorem` is designed for recurrences of
the form

`T(n) ≤ a * T(n / b) + k * (n+1)^c`

where:
- `T : ℕ → ℝ` is the cost function,
- `a` is the number of recursive subproblems,
- `b` is the shrink factor in the recursive call,
- `k * (n+1)^c` is the non-recursive work done outside the recursive calls.

### How to match your algorithm to this form

When you analyze your own divide-and-conquer algorithm, you should identify:

- **`T`**:
  the real-valued version of your size-based cost function.

- **`a`**:
  how many recursive subproblems appear.
  For Merge Sort, there are `2` recursive calls.

- **`b`**:
  how much the input shrinks in each recursive call.
  For Merge Sort, each recursive call works on roughly half the input,
  so `b = 2`.

- **`k`**:
  the constant factor multiplying the non-recursive work.
  For Merge Sort, the combine step is linear, so we use `k = 1`.

- **`c`**:
  the exponent in the non-recursive work term `(n+1)^c`.
  Since Merge Sort does linear combine work, we use `c = 1`.

### Why we use a real-valued function

The theorem `Master_general` works with functions of type `ℕ → ℝ`.
Our recurrence `mergeSortCostN` is natural-valued, so we define
`mergeSortCostNR` by casting it into the reals.

### Why this section uses an axiom

In a full formal development, one would usually prove that the recurrence for
`mergeSortCostNR` really has the exact form required by `Master_general`.

In this example file, that bridge is packaged as an axiom:

`mergeSortCost_eqsplit_bound_R`

This keeps the focus on the main lesson of the example:
**how to use the general Master theorem once the recurrence has been written in
the correct form**.

### What students should do in their own file

For your own divide-and-conquer algorithm, you should:
1. define your size-based cost function,
2. convert it to a real-valued version if needed,
3. write a lemma or assumption in the exact theorem-ready form
   `T(n) ≤ a * T(n / b) + k * powR n c`,
4. then apply `Master_general`.
-/

/--
Merge Sort recurrence in the exact form needed by the general Master theorem.

For Merge Sort, we use the parameters:
- `a = 2` because there are two recursive calls,
- `b = 2` because the input size is halved,
- `k = 1` because the combine work is linear,
- `c = 1` because linear work corresponds to `(n+1)^1`.
-/
axiom mergeSortCost_eqsplit_bound_R :
  ∀ n ≥ 2,
    mergeSortCostNR n ≤ (2 : ℝ) * mergeSortCostNR (n / 2) + (1 : ℝ) * powR n 1

/-!
## Section 5: Final asymptotic theorem

This section shows how to call the general Master theorem.

The theorem we use is:

`Master_general`

Its inputs are:
- the cost function `T`,
- the recurrence parameters `a`, `b`, `k`, `c`,
- the case selector `cs : MasterCase`,
- proofs of the required side conditions,
- and the recurrence inequality itself.

### Step-by-step interpretation for Merge Sort

We apply `Master_general` with:

- `T := mergeSortCostNR`
- `a := 2`
- `b := 2`
- `k := 1`
- `c := 1`
- `cs := MasterCase.eq`

### Why `MasterCase.eq`?

The critical exponent is `log_b(a)`, which here is

`log_2(2) = 1`

and our non-recursive exponent is also `c = 1`.

So this is exactly the **equality case** of the Master theorem:
- recursive work and non-recursive work have the same exponent,
- therefore the final bound gets an extra logarithmic factor.

### What the side-condition proofs mean

The call to `Master_general` also needs proofs that:

- `1 ≤ a`
- `2 ≤ b`
- `0 ≤ k`
- `c = log_b(a)`   because we chose `MasterCase.eq`
- the regularity condition for the `gt` case is trivial here, because we are
  not in that case
- the recurrence assumption `mergeSortCost_eqsplit_bound_R` holds

### Reading the final result

The output is written using the library function `masterBound`, which expands
the asymptotic result according to the selected case.

For the equality case, this becomes

`(n+1)^(log_b(a)) * log_b(n+1)`

For Merge Sort, that is the standard `O(n log n)` growth rate.

### What students should do in their own file

When using `Master_general` for your own algorithm:
1. identify `a`, `b`, `k`, `c`,
2. decide whether you are in case `lt`, `eq`, or `gt`,
3. prove the corresponding side condition,
4. provide the recurrence inequality,
5. apply `Master_general`.
-/

/--
Final asymptotic bound for Merge Sort using the general Master theorem.

This is the final theorem of the example:
it shows how a divide-and-conquer recurrence is turned into an asymptotic bound
using the theorem library.
-/
theorem mergeSortCost_bigO_via_general_OR :
  mergeSortCostNR
    =OR (fun n => powR n (logb 2 (2 : ℝ)) * logbp1R (2 : ℝ) n) := by
  simpa [masterBound] using
    (Master_general
      (T := mergeSortCostNR) (a := 2) (k := 1) (b := 2) (c := 1) (cs := MasterCase.eq)
      (by norm_num)
      (by decide)
      (by norm_num)
      (by
        have hlog : Real.log (2 : ℝ) ≠ 0 := by
          have h : (2 : ℝ) ≠ 0 ∧ (2 : ℝ) ≠ 1 ∧ (2 : ℝ) ≠ -1 := by
            norm_num
          exact (Real.log_ne_zero).2 h
        simp [logb, hlog])
      (by trivial)
      mergeSortCost_eqsplit_bound_R)

end MergeSort

end Lean4CStheory.Algorithms.DivideConquer
