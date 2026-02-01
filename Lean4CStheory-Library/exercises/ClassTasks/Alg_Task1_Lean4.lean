/- Copyright (c) Kelin Luo, 2025.  All rights reserved. -/

-- Instructions for Lean Task Project
-- 1. Coding Environment
--     * Complete this task as instructed.
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

/- Task 1: 12 points (worth 2.5% of your final grade). -/

import Mathlib
import Mathlib.Tactic

/-!
=====================================
Lean Tactics Reference
=====================================

The following tactics are used throughout this task:

* rw        : rewrite a goal or hypothesis using an equality
* simp      : simplify expressions using rewrite rules
* calc      : structure multi-step equalities or inequalities
* linarith  : solve linear arithmetic goals and inequalities
* nlinarith : solve nonlinear arithmetic goals
* ring      : normalize algebraic expressions involving addition and multiplication
* constructor : split goals of the form A ∧ B
* intro     : introduce universally quantified variables or assumptions
* norm_num  : evaluate numeric expressions and close simple arithmetic goals
* induction : prove statements about recursively defined objects (e.g., ℕ)

You are expected to understand how and why these tactics are applied in the examples
and exercises, and to follow similar proof patterns in your own solutions.
-/

/-! # Section 0: Math Basics (4 points) -/
/-!
This section focuses on equations and inequalities.
Follow the structure of the examples when solving the exercises.
-/

-- Example 0.1
example {a b : ℝ} (h1 : a = 3) (h2 : b = -1) : a + b = 2 :=
  calc
    a + b = 3 + b := by rw [h1]
    _ = 3 + (-1) := by rw [h2]
    _ = -1 + 3 := by rw [add_comm]
    _ = 2 := by norm_num

-- (1 point) Exercise 0.1
example {a b : ℝ} (h1 : a = 3) (h2 : b = 4) : a + 2 * b = 11 :=
  sorry

-- Example 0.2
example {n : ℕ} (h1 : c = 1) : 2 * n + 10 ≥ c * 2 := by
  rw [h1]
  simp

-- (1 point) Exercise 0.2
example {n : ℕ} (h1 : c = 3) : 5 * n + 6 ≥ c := by
  sorry

-- Example 0.3
example {n : ℕ} (h1 : c = 5) : 4 * n ≤ c * n := by
  rw [h1]
  calc
    4 * n ≤ 5 * n := by
      have h : 0 ≤ n := Nat.zero_le n
      linarith

-- Example 0.3 (alternative proof)
example {n : ℕ} (h1 : c = 5) : 4 * n ≤ c * n := by
  rw [h1]
  linarith

-- (1 point) Exercise 0.3
example {n : ℕ} (h1 : c = 2) : 4 * n + 3 ≥ c * (n + 1) := by
  sorry

-- Example 0.4
example {n : ℕ} (h1 : n ≥ 1) (h2 : c = 1) :
  12 * n^2 ≥ c * (2 * n + 10) := by
  calc
    12 * n^2 = 12 * n * n := by ring
    _ ≥ 2 * n + 10 := by nlinarith
    _ = c * (2 * n + 10) := by rw [h2]; ring

-- Example 0.5
example {n : ℕ} (h1 : n ≥ 2) (h2 : c₁ = 1) (h3 : c₂ = 4) :
  c₁ * n ≤ 2 * n + 5 ∧ n + 1 ≤ c₂ * n := by
  rw [h2, h3]
  constructor
  · linarith [h1]
  · linarith [h1]

-- (1 point) Exercise 0.4
example {n : ℕ} (h1 : n ≥ 10) (h2 : c₁ = 1) (h3 : c₂ = 10) :
  c₁ * (2 * n + 1) ≤ 5 * n ∧ 5 * n ≤ c₂ * (2 * n + 1) := by
  sorry

/-! # Section 1: Asymptotic Analysis in Lean (5 points) -/
/-!
This section introduces Big-O, Big-Omega, and Big-Theta.
You are expected to follow the definitions exactly.
-/

-- Definition of Big-O
def isBigO (f g : ℕ → ℝ) : Prop :=
  ∃ (c n₀ : ℝ), 0 < c ∧ ∀ n : ℕ, n ≥ n₀ → f n ≤ c * g n

-- (1 point) Exercise 1.1
-- Define Big-Omega using the same style as Big-O.
def isBigOmega (f g : ℕ → ℝ) : Prop :=
  sorry

-- (1 point) Exercise 1.2
-- Define Big-Theta using Big-O and Big-Omega.
def isBigTheta (f g : ℕ → ℝ) : Prop :=
  sorry

-- Example 1.2
example : isBigO (fun n ↦ (2 : ℝ) * n + 4) (fun n ↦ n) := by
  use 3, 4
  constructor
  · linarith
  intro n hn
  calc
    (2 : ℝ) * n + 4 ≤ 2 * n + n := by linarith [hn]
    _ = 3 * n := by ring

-- (1 point) Exercise 1.3
example : isBigO (fun n ↦ (3 : ℝ) * n + 2) (fun n ↦ n) := by
  sorry

-- (1 point) Exercise 1.4
example : isBigOmega (fun n ↦ (3 : ℝ) * n + 2) (fun n ↦ n) := by
  sorry

-- (1 point) Exercise 1.5
example : isBigTheta (fun n ↦ (3 : ℝ) * n + 2) (fun n ↦ n) := by
  sorry

/-! # Section 2: Recursion and Induction (3 points) -/
/-!
Only structural recursion is permitted.
Do not use subtraction-based recursion.
-/

-- Example 2.1
def sumNR : ℕ → ℝ
  | 0     => 0
  | n + 1 => sumNR n + (n + 1)

example (n : ℕ) : sumNR n = n * (n + 1) / 2 := by
  induction n with
  | zero =>
      simp [sumNR]
  | succ k IH =>
      simp [sumNR, IH]
      ring

-- (2 points) Exercise 2.1
def sumOdd : ℕ → ℕ
  | 0     => 1
  | n + 1 => sumOdd n + (2 * (n + 1) + 1)

example (n : ℕ) : sumOdd n = (n + 1) ^ 2 := by
  induction n with
  | zero =>
      sorry
  | succ k IH =>
      sorry

-- (1 point) Exercise 2.2
-- Define the Fibonacci function fib(n).
-- Only the function definition is required.
def fib : ℕ → ℕ :=
  sorry
