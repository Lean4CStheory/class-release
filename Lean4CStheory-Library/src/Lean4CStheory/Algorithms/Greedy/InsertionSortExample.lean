import Mathlib
import Mathlib.Data.List.Sort
import Lean4CStheory.Time.TimeM
import Lean4CStheory.Asymptotics.BigO

namespace Lean4CStheory.Algorithms.Greedy

/-!
# Greedy Example: Insertion Sort (TimeM + Correctness + Cost + Big-O)

This file is a worked example showing how to formalize a **greedy-style
algorithm** in Lean.

The goal of this file is not only to define insertion sort, but also to give a
clear model that students should follow when writing their own greedy-algorithm
file.

## Expected structure for a greedy-algorithm file

If you choose a greedy algorithm, your file is expected to follow the same
basic structure as this one:

1. **Define the algorithm in `TimeM`**
   - identify the local greedy step,
   - define the full recursive or iterative algorithm,
   - use `TimeM` so that the implementation records running time.

2. **Prove correctness**
   - connect your implementation to a trusted specification, or
   - prove the key correctness property directly.

3. **Define a worst-case cost model**
   - write a mathematical cost function that is simpler to analyze than the raw
     implementation time.

4. **Relate measured time to the cost model**
   - prove that the `.time` recorded by `TimeM` is bounded by your cost function.

5. **Convert to a size-based cost function**
   - define a function `Nat → Nat` that represents worst-case cost on inputs of
     size `n`.

6. **Prove the asymptotic bound**
   - prove a clean upper bound for the size-based cost,
   - then conclude the final Big-O theorem.

## What this example does

This example uses insertion sort and develops three parallel stories:

1. **Algorithm:** insertion sort is implemented in the timing monad `TimeM`.
2. **Correctness:** the implementation is connected to Mathlib’s insertion sort,
   so we obtain key correctness properties.
3. **Time analysis:** a worst-case cost function is defined, the measured runtime
   is bounded by that cost, and the final asymptotic bound `O(n^2)` is proved.

## How to read this file
- `def` introduces a *definition* (a function or a new concept).
- `theorem` / `lemma` introduce a *statement* with a proof.
- Proofs start with `:= by` and then use tactics.
- `simp` means “simplify by rewriting using definitions and standard rules”.
- `induction xs` means “prove it for `[]` and for `x :: xs` assuming it holds for `xs`”.
- `by_cases h : P` splits the proof into the cases `P` and `¬P`.
- `TimeM α` is a type of computations that return an `α` and also record a `time : Nat`.
  - `.ret` extracts the computed result
  - `.time` extracts the recorded time
- `✓ v` means “return value `v` and add one unit of time”.
-/

open Lean4CStheory.Time
open TimeM
open Lean4CStheory.Asymptotics

/-!
## 1. Algorithm Definition (in TimeM)

We define two functions:

- `insert x xs`: insert one element `x` into an already-sorted list `xs`.
- `insertionSort xs`: sort a list by sorting the tail and inserting the head.

Both are defined in `TimeM` so we can later reason about `.time`.

### What students should learn from this section
A greedy-algorithm file should begin by making the algorithmic structure clear,
and in this project it is expected that the algorithm itself is written in
`TimeM`, just as it is here.

In this example:
- `insert` is the **local greedy step**,
- `insertionSort` is the full algorithm built from that step.

For another greedy algorithm, your local greedy step may be:
- choosing the next interval,
- taking the next minimum edge,
- selecting the next job,
- choosing the next coin,
- or another locally optimal action.

The important point is that your implementation should follow the same pattern
as this example:
- define the greedy step,
- define the full algorithm in `TimeM`,
- and make it possible to reason later about the recorded running time.
-/

/--
`insert x xs` inserts `x` into the list `xs`, assuming `xs` is already sorted.

### Intuition
- If the list is empty, the result is `[x]`.
- Otherwise, compare `x` with the head `y`:
  - if `x ≤ y`, then `x` belongs at the front,
  - else, keep `y` and insert `x` into the tail.

### Why TimeM?
We want a model where each important step costs time.
Here, every branch returns using `✓ ...`, which charges 1 unit.
-/
def insert (x : ℕ) : List ℕ → TimeM (List ℕ)
| [] =>
    ✓ [x]
    -- Base case: inserting into empty list just produces `[x]`.
| y :: ys =>
    -- We compare `x` to the head element `y`.
    if x ≤ y then
      -- If `x` is small enough, it goes before `y`.
      ✓ (x :: y :: ys)
    else
      -- Otherwise we keep `y` and recursively insert into the tail `ys`.
      do
        let ys' ← insert x ys
        -- `ys'` is the recursive result (in TimeM).
        ✓ (y :: ys')
        -- Prepend `y` back to the result.

/--
`insertionSort xs` sorts the list `xs` using insertion sort.

### Intuition
- Empty list is already sorted.
- For `x :: xs`:
  1) sort `xs`,
  2) insert `x` into the sorted tail.

### Why this matches textbook insertion sort
It literally implements: "sort the tail, then insert the head".
-/
def insertionSort : List ℕ → TimeM (List ℕ)
| [] =>
    ✓ []
    -- Empty list sorted.
| x :: xs =>
    do
      let xs' ← insertionSort xs
      -- First recursively sort the tail.
      insert x xs'
      -- Then insert the head into the sorted tail.

/-!
## 2. Correctness Proofs

The goal of this section is to show the functions above compute the “expected” result.

Mathlib already contains:
- `List.orderedInsert` (insert into a sorted list),
- `List.insertionSort` (the standard insertion sort implementation),
- `List.sorted_insertionSort` (proof the result is sorted).

We connect our `TimeM` implementations to these standard definitions using `.ret`.

### What students should learn from this section
When proving correctness, it is often much easier to connect your implementation
to an existing specification than to start from scratch.

This example follows that strategy:
1. show `insert` matches Mathlib’s `orderedInsert`,
2. show `insertionSort` matches Mathlib’s `insertionSort`,
3. then reuse the library theorem that insertion sort is sorted.

For your own greedy algorithm, try to identify:
- a trusted specification,
- a simpler mathematical description,
- or a library theorem you can reduce to.
-/

/--
Correctness of `insert`:

`(insert x xs).ret` (our computed result) equals the standard library’s
`List.orderedInsert` (with comparator `≤`).

### Proof idea
Induct on the list `xs`:
- if `xs = []`, both sides are `[x]`,
- if `xs = y :: ys`, split on whether `x ≤ y`.
-/
theorem insert_correct (x : ℕ) (xs : List ℕ) :
  (insert x xs).ret = List.orderedInsert (· ≤ ·) x xs := by
  -- Induction over the list being inserted into.
  induction xs with
  | nil =>
      -- Simplify using the definitions of `insert` and `orderedInsert`.
      simp [insert, List.orderedInsert]
  | cons y ys ih =>
      -- Split on the comparison used by the algorithm.
      by_cases h : x ≤ y
      ·
        -- Case: `x ≤ y`, so insertion is at the front.
        simp [insert, h, List.orderedInsert]
      ·
        -- Case: `¬(x ≤ y)`, so we recurse into the tail.
        -- `ih` is the induction hypothesis for the recursive call.
        simp [insert, h, List.orderedInsert, ih]

/--
Correctness of `insertionSort`:

Our returned value equals Mathlib’s `List.insertionSort`.

### Proof idea
Induct on `xs`:
- base case: `[]`,
- step case: `x :: xs` and use `insert_correct`.
-/
theorem insertionSort_correct (xs : List ℕ) :
  (insertionSort xs).ret =
    List.insertionSort (· ≤ ·) xs := by
  induction xs with
  | nil =>
      -- Base case reduces by definitions.
      simp [insertionSort]
  | cons x xs ih =>
      -- Step case: simplify recursion and use the induction hypothesis + insert correctness.
      simp [insertionSort, ih, insert_correct]

/--
Sortedness:

The result returned by our `insertionSort` is sorted.

### Why this is easy once we have `insertionSort_correct`
Mathlib already proves `List.sorted_insertionSort`. We rewrite our result
to the standard one, and reuse that theorem.
-/
theorem insertionSort_sorted (xs : List ℕ) :
  List.Sorted (· ≤ ·) (insertionSort xs).ret := by
  -- Replace our `.ret` with the library insertion sort, then use its sortedness theorem.
  simpa [insertionSort_correct] using
    List.sorted_insertionSort (· ≤ ·) xs

/--
Length preservation:

Insertion sort does not change the length of the list.

### Reason
Mathlib’s insertion sort preserves length, and we can rewrite using correctness.
-/
lemma insertionSort_length (xs : List ℕ) :
  (insertionSort xs).ret.length = xs.length := by
  -- Rewrite to the standard insertion sort; simp knows it preserves length.
  simp [insertionSort_correct]

/-!
## 3. Exact Cost Model (worst-case)

We now define explicit cost functions and prove our measured `TimeM` time
is bounded by them.

Important idea:
- The algorithm’s `.time` is the time that was actually recorded by `TimeM`.
- The cost functions below are *mathematical upper bounds* (worst-case).
- The theorems `*_time_le` connect the two.

### What students should learn from this section
For asymptotic analysis, it is often helpful to separate:
- the **recorded time** of the implementation,
- from a simpler **mathematical cost function** that is easier to analyze.

This example uses that pattern:
- `insert` and `insertionSort` produce measured times through `TimeM`,
- `insertCost` and `insertionSortCost` are clean worst-case upper bounds,
- the proofs `insert_time_le` and `insertionSort_time_le` connect the two.

For your own greedy algorithm, this is the expected recipe:
1. define the algorithm,
2. define a worst-case cost function,
3. prove the implementation time is bounded by the cost function.
-/

/--
Worst-case cost of `insert x xs`.

We choose the bound `xs.length + 1`:
- in the worst case, insertion scans the entire list (`xs.length` steps),
- plus a base/tick cost.

This is a simple linear bound suitable for asymptotic reasoning.
-/
def insertCost (xs : List ℕ) : ℕ :=
  xs.length + 1

/--
Worst-case cost of insertion sort, defined recursively on the list.

- For `[]`, cost is 1.
- For `_ :: xs`, we:
  1) sort the tail (`insertionSortCost xs`),
  2) insert the head into that sorted tail (worst-case `insertCost xs`).

This produces the familiar quadratic recurrence.
-/
def insertionSortCost : List ℕ → ℕ
| [] => 1
| _ :: xs => insertionSortCost xs + insertCost xs

/--
Worst-case time bound for `insert`.

Statement:
`(insert x xs).time ≤ insertCost xs`

### Proof idea
Induct on `xs`.
- In the `x ≤ y` case, we return immediately.
- In the `¬(x ≤ y)` case, time is the recursive time plus a constant,
  so we use the induction hypothesis.
-/
theorem insert_time_le (x : ℕ) (xs : List ℕ) :
  (insert x xs).time ≤ insertCost xs := by
  induction xs with
  | nil =>
      -- Compute both sides directly.
      simp [insert, insertCost]
  | cons y ys ih =>
      by_cases h : x ≤ y
      ·
        -- Immediate return, easy bound.
        simp [insert, insertCost, h]
      ·
        -- Recursive case: time grows by one tick over the recursive call.
        simp [insert, insertCost, h]
        -- The goal becomes a successor inequality; `Nat.succ_le_succ` lifts `ih`.
        simpa [insertCost] using Nat.succ_le_succ ih

/--
Worst-case time bound for `insertionSort`.

Statement:
`(insertionSort xs).time ≤ insertionSortCost xs`

### Proof idea
Induct on `xs`:
- Base case is direct.
- Step case:
  1) apply IH to bound time of sorting the tail,
  2) apply `insert_time_le` to bound insertion time,
  3) use length preservation to rewrite `insertCost (sortedTail)` to `insertCost xs`,
  4) add the inequalities.
-/
theorem insertionSort_time_le (xs : List ℕ) :
  (insertionSort xs).time ≤ insertionSortCost xs := by
  induction xs with
  | nil =>
      simp [insertionSort, insertionSortCost]
  | cons x xs ih =>
      -- Unfold the algorithm and the cost recurrence.
      simp [insertionSort, insertionSortCost]
      -- `insert_time_le` bounds the insertion step, but it talks about the sorted tail.
      have hinsert := insert_time_le x (insertionSort xs).ret
      -- We want the insert bound in terms of the original `xs`, so we rewrite lengths.
      have hlen : insertCost (insertionSort xs).ret = insertCost xs := by
        simp [insertCost, insertionSort_length xs]
      have hinsert' :
        (insert x (insertionSort xs).ret).time ≤ insertCost xs := by
        simpa [hlen] using hinsert
      -- Combine (time to sort tail) + (time to insert head).
      exact Nat.add_le_add ih hinsert'

/-!
## 4. Size-based cost function

Big-O is phrased as a statement about functions `Nat → Nat`.
So we convert list-cost into size-cost by measuring the cost on a canonical
list of length `n`.

The particular contents of the list do not matter for worst-case bounds,
so we use `List.replicate n 0`.

### What students should learn from this section
A list-based cost function is useful for connecting the implementation to its
runtime, but asymptotic notation is usually cleaner when written as a function
of the input size.

So the standard move is:
- start with a cost function on inputs,
- then define a size-based version `Nat → Nat`,
- and do the final asymptotic proof on that size-based function.

This is the standard step expected in a greedy-algorithm analysis file.
-/

/--
`insertionSortCostN n` is the worst-case cost on inputs of size `n`.

It is defined by applying `insertionSortCost` to a list of length `n`.
-/
def insertionSortCostN (n : ℕ) : ℕ :=
  insertionSortCost (List.replicate n 0)

/--
A recurrence for `insertionSortCostN`.

It states that the cost on size `n + 1` is:
- cost on size `n`,
- plus `(n + 1)` (the insert cost into a list of length `n`).

This is the standard insertion sort recurrence.
-/
lemma insertionSortCostN_succ (n : ℕ) :
  insertionSortCostN (n + 1) = insertionSortCostN n + (n + 1) := by
  -- Expand definitions and compute lengths of `replicate`.
  simp [insertionSortCostN, insertionSortCost, insertCost, List.replicate]

/--
A quadratic upper bound:

`insertionSortCostN n ≤ n^2 + n + 1`

This gives a concrete polynomial upper bound that is easy to use for Big-O.
-/
lemma insertionSortCostN_le (n : ℕ) :
  insertionSortCostN n ≤ n^2 + n + 1 := by
  induction n with
  | zero =>
      -- Base case: check directly.
      simp [insertionSortCostN, insertionSortCost]
  | succ n ih =>
      -- First lift the IH by adding `(n + 1)` to both sides.
      have h1 :
          insertionSortCostN n + (n + 1) ≤ (n^2 + n + 1) + (n + 1) :=
        Nat.add_le_add_right ih (n + 1)

      -- Then show the polynomial on the right fits the next-square form.
      have h2 :
          (n^2 + n + 1) + (n + 1) ≤ (n + 1)^2 + (n + 1) + 1 := by
        nlinarith

      -- Combine and rewrite using the recurrence from `insertionSortCostN_succ`.
      simpa [insertionSortCostN_succ] using le_trans h1 h2

/-!
## 5. Asymptotic analysis (Big-O)

We now prove the standard statement:

Insertion sort runs in `O(n^2)` time in the worst case.

The strategy is:
1) show `insertionSortCostN n ≤ n^2 + n + 1` (previous lemma),
2) show `n^2 + n + 1 = O(n^2)` (a general polynomial fact in your `BigO.lean`),
3) combine them using `BigO_of_le`.

### What students should learn from this section
The final asymptotic theorem usually does **not** require a huge proof.
Most of the work is done earlier by:
- defining the right cost function,
- proving a clean upper bound,
- and choosing the right helper theorem from the asymptotics library.

So the final Big-O theorem often looks short because the file has already done
the hard conceptual work.

For your own greedy algorithm, your final section should answer:
- what is the asymptotic running time,
- and which earlier lemmas justify that bound?
-/

/--
Insertion sort is `O(n^2)` in the worst case.
-/
theorem insertionSort_bigO :
  insertionSortCostN =O (fun n => n^2) := by
  apply BigO_of_le
  · intro n
    exact insertionSortCostN_le n
  · -- A helper lemma: any quadratic polynomial `n^2 + a*n + b` is `O(n^2)`.
    simpa using poly2_bigO_quadratic 1 1 1

end Lean4CStheory.Algorithms.Greedy
