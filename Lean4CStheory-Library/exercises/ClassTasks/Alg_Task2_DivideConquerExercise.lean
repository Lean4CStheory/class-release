/- Copyright (c) Kelin Luo, 2025.  All rights reserved. -/

-- Instructions for Lean Task Project
-- 1. Coding Environment
--     * Complete this task in the Lean online editor: https://live.lean-lang.org/
--     * Submit a single Lean file that compiles without errors.
-- 2. Learning Resources
--     * Official Lean documentation:
--       https://leanprover-community.github.io/learn.html
--       https://leanprover-community.github.io/mathematics_in_lean/
-- 3. Use of AI Tools
--     * You may use AI tools (ChatGPT, GitHub Copilot, etc.) to:
--         - understand Lean syntax
--         - understand tactics
--         - debug errors
--         - explain examples
--     * If AI tools are used, you must include the prompts as comments
--       starting with:  -- Prompt:
-- 4. Submission Format
--     * The file must be clean, readable, and well-commented.
--     * Your own solutions must be clearly distinguishable from AI references.

import Mathlib
import Lean4CStheory.Asymptotics.MastersTheorem

set_option autoImplicit false

open List
open Lean4CStheory.Asymptotics

/-!
# Divide-and-Conquer Exercise Template

In this task, you will choose **one** divide-and-conquer algorithm and write
your own Lean file by following the same structure as the
**Divide and Conquer Example: Merge Sort** file.

## Choose one algorithm
You must choose exactly one of the following:

1. Count Inversions Problem
2. Quick Sort for Sorting Problem
3. Selection Problem
4. Polynomial Multiplication Problem

## What you should do
You should follow the **same overall structure** as the Merge Sort example file.

This means your file should contain:

1. **Algorithm definition**
2. **Correctness specification**
3. **Size-based cost model**
4. **Recurrence assumption in Master-theorem form**
5. **Final asymptotic theorem**

Do not copy the Merge Sort algorithm itself.
Instead, use the example file as a model for how to organize and explain your
own chosen algorithm.

## Important note
This template only gives the structure of the file.
You are expected to write the actual definitions, specifications, recurrence,
and theorem statements for your chosen algorithm by following the example file.
-/

namespace Lean4CStheory.Algorithms.DivideConquer

namespace StudentChoice

/-!
## Section 0: Student information

Before writing the file, clearly indicate which algorithm you chose.

Examples:
- Count Inversions
- Quick Sort
- Selection
- Polynomial Multiplication
-/

/-!
Write a short comment here stating your chosen algorithm.

Example:
`Chosen algorithm: Quick Sort`
-/

/-!
## Section 1: Algorithm definition

In this section, define the helper functions and the main algorithm.

### What this section should contain
Your divide-and-conquer algorithm should clearly show:
- the **divide** step,
- the **recursive** step,
- the **combine** step.

As in the Merge Sort example file, you may choose either of the following styles:

### Option 1: total definitions
Use `def` with `termination_by` and `decreasing_by`
if you want Lean to verify termination.

### Option 2: partial definitions
Use `partial def` if your main goal is to present the algorithm structure
more simply.

### What students should do here
Using the Merge Sort example as a guide, write:
- any helper definitions needed by your algorithm,
- the main recursive algorithm definition.

Do **not** leave this section empty in your final submission.
-/

/-!
Write your helper definitions and your main algorithm here.
-/

/-!
## Section 2: Correctness specification

In this section, state what it means for your algorithm to be correct.

### What this section should contain
You do not necessarily need to prove full correctness unless your instructor
asks for it, but you should write down a precise correctness specification.

### Examples by algorithm
- **Count Inversions:** the returned number equals the true inversion count.
- **Quick Sort:** the output is sorted and contains the same elements.
- **Selection:** the output is the correct kth smallest element.
- **Polynomial Multiplication:** the output equals the correct polynomial product.

### What students should do here
Using the Merge Sort example as a guide, write:
- any helper predicates or specifications you need,
- the main correctness specification for your chosen algorithm.
-/

/-!
Write your correctness specification here.
-/

/-!
## Section 3: Size-based cost model

In this section, define a cost recurrence depending only on the input size.

### What this section should contain
Your cost function should:
- take a natural number `n`,
- represent the worst-case cost on inputs of size `n`,
- follow the same recursive structure as your algorithm.

### What students should do here
Using the Merge Sort example as a guide, write:
- a natural-valued size-based recurrence,
- a real-valued version if needed for the Master theorem.
-/

/-!
Write your size-based cost function here.
-/

/-!
## Section 4: Recurrence assumption in Master-theorem form

The general Master theorem in `MastersTheorem` is designed for recurrences of
the form

`T(n) ≤ a * T(n / b) + k * (n+1)^c`

where:
- `T : ℕ → ℝ` is the cost function,
- `a` is the number of recursive subproblems,
- `b` is the shrink factor in each recursive call,
- `k * (n+1)^c` is the non-recursive work.

### What students should do here
Using your own recurrence, identify:
- `T`
- `a`
- `b`
- `k`
- `c`

Then write a lemma or assumption in the exact theorem-ready form expected by
`Master_general`.

The Merge Sort example file shows how this step should look.
-/

/-!
Write your recurrence assumption here.
-/

/-!
## Section 5: Final asymptotic theorem

In this section, apply the general Master theorem.

The theorem you should use is:

`Master_general`

### What students should do here
You should:
1. identify the correct values of `a`, `b`, `k`, `c`,
2. determine whether your recurrence is in case `lt`, `eq`, or `gt`,
3. prove the required side condition,
4. provide the recurrence inequality,
5. conclude the final asymptotic bound.

The Merge Sort example file shows the expected structure of this theorem.
-/

/-!
Write your final asymptotic theorem here.
-/

/-!
## Submission checklist

Before submitting, make sure that you have:

1. chosen exactly one algorithm,
2. written the actual algorithm definitions,
3. stated a correctness specification appropriate for your algorithm,
4. defined a size-based cost function,
5. matched your recurrence to the theorem-ready Master form,
6. applied `Master_general` with the correct parameters and case,
7. kept the file readable and well-commented.
-/

end StudentChoice

end Lean4CStheory.Algorithms.DivideConquer
