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
import Mathlib.Data.List.Sort
import Lean4CStheory.Time.TimeM
import Lean4CStheory.Asymptotics.BigO

set_option autoImplicit false

open Lean4CStheory.Time
open TimeM
open Lean4CStheory.Asymptotics

/-!
# Greedy Exercise Template

In this task, you will choose **one** greedy algorithm and write your own Lean
file by following the same structure as the
**Greedy Example: Insertion Sort** file.

## Choose one algorithm
You must choose exactly one of the following:

1. Interval Scheduling Problem
2. Box Packing Problem
3. Optimum Caching Problem
4. Huffman Coding Problem


## What you should do
You should follow the **same overall structure** as the greedy example file.

This means your file should contain:

1. **Algorithm definition in `TimeM`**
2. **Correctness proofs or correctness specification**
3. **Exact cost model**
4. **Measured-time bound**
5. **Size-based cost function**
6. **Final Big-O theorem**

## Important note
This template only gives the structure of the file.
You are expected to write the actual definitions, specifications, cost
functions, and theorem statements for your chosen algorithm by following the
example file.

For a greedy algorithm submission in this project, it is expected that the
algorithm itself is written in `TimeM`, just as it is in the insertion sort
example.
-/

namespace Lean4CStheory.Algorithms.Greedy

namespace StudentChoice

/-!
## Section 0: Student information

Before writing the file, clearly indicate which greedy algorithm you chose.
-/

/-!
Write a short comment here stating your chosen algorithm.

Example:
`Chosen algorithm: Interval Scheduling`
-/

/-!
## Section 1: Algorithm Definition (in TimeM)

In this section, define the helper functions and the main greedy algorithm.

### What this section should contain
Your greedy algorithm should clearly show:
- the **local greedy step**,
- the **full algorithm** built from that step.

As in the insertion sort example, your implementation is expected to use
`TimeM`, so that the algorithm records running time and can later be analyzed
using `.time`.

### What students should do here
Using the insertion sort example as a guide, write:
- any helper definitions needed by your algorithm,
- the local greedy step,
- the full greedy algorithm in `TimeM`.

Do **not** leave this section empty in your final submission.
-/

/-!
Write your helper definitions and your main `TimeM` algorithm here.
-/

/-!
## Section 2: Correctness proofs or correctness specification

In this section, explain what it means for your greedy algorithm to be correct.

### What this section should contain
You should either:
- prove correctness properties directly, or
- connect your implementation to a trusted specification, or
- at minimum state a clear correctness specification if a full proof is not required.

### Examples
Depending on the algorithm, correctness might mean:
- the output is sorted,
- the output is optimal,
- the selected set is valid,
- the returned cost is minimal,
- the result matches a trusted specification.

### What students should do here
Using the insertion sort example as a guide, write:
- any helper lemmas you need,
- the main correctness theorem(s) or specification(s) for your chosen algorithm.
-/

/-!
Write your correctness statements and proofs here.
-/

/-!
## Section 3: Exact cost model (worst-case)

In this section, define a mathematical cost function for your algorithm.

### What this section should contain
Your cost function should:
- be simpler to analyze than the raw implementation,
- represent a worst-case upper bound,
- follow the same recursive or iterative structure as the algorithm.

### What students should do here
Using the insertion sort example as a guide, write:
- a cost function for the local greedy step if needed,
- a cost function for the full greedy algorithm.

This cost model should be stated separately from the `.time` recorded by `TimeM`.
-/

/-!
Write your worst-case cost definitions here.
-/

/-!
## Section 4: Relating measured time to the cost model

In this section, prove that the `.time` recorded by your `TimeM` implementation
is bounded by your mathematical cost function.

### What this section should contain
You should prove theorem(s) of the form:
- local-step runtime ≤ local-step cost
- full algorithm runtime ≤ full cost

### What students should do here
Using the insertion sort example as a guide, prove that the implementation time
is bounded by the cost model you defined in the previous section.
-/

/-!
Write your runtime upper-bound theorem(s) here.
-/

/-!
## Section 5: Size-based cost function

Big-O is usually stated as a theorem about functions of input size.

So in this section, you should convert your cost model into a function
`Nat → Nat` that represents worst-case cost on inputs of size `n`.

### What this section should contain
You should define:
- a size-based cost function,
- and any recurrence or upper-bound lemmas needed for asymptotic analysis.

### What students should do here
Using the insertion sort example as a guide, define:
- a function `Nat → Nat`,
- and prove a clean upper bound that will be useful for the final Big-O proof.
-/

/-!
Write your size-based cost function and supporting lemmas here.
-/

/-!
## Section 6: Final asymptotic theorem (Big-O)

In this section, prove the final asymptotic bound for your greedy algorithm.

### What this section should contain
You should:
- use the size-based cost function from the previous section,
- use a previously proved upper bound,
- apply the appropriate helper theorem(s) from `BigO.lean`,
- conclude the final `=O` theorem.

### What students should do here
Using the insertion sort example as a guide, prove the final Big-O theorem for
your chosen greedy algorithm.

Your final theorem should answer:
- what is the asymptotic running time,
- and which earlier lemmas justify that result?
-/

/-!
Write your final asymptotic theorem here.
-/

/-!
## Submission checklist

Before submitting, make sure that you have:

1. clearly stated your chosen greedy algorithm,
2. defined the algorithm in `TimeM`,
3. included correctness proofs or a correctness specification,
4. defined a worst-case cost model,
5. proved the measured runtime is bounded by that cost,
6. converted the cost into a size-based function,
7. proved the final Big-O theorem,
8. kept the file readable and well-commented.
-/

end StudentChoice

end Lean4CStheory.Algorithms.Greedy
