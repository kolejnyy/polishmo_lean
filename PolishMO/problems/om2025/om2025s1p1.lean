import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Basic

import PolishMO.Prime
import PolishMO.Quadratics

open Nat
open Real



/--
**OM2025: STAGE 1 - PROBLEM 1**
---
Problem: Let f(x) = a * x ^ 2 + b * x + c be a quadratic function with no real roots. Show a(2a+3b+6c) > 0. \
\
Solution: Note that a(2a+3b+6c) = a(a/2 + 6 * f(1/2)). Since clearly a * a/2 > 0, it suffices to show that
a * f(1/2) > 0. Since f has no real roots, it has to either be always positive or negative. If f(x) is always
positive, then we must have a > 0, as f(x) → a*x^2 as x → ∞. In particular, a * f(x) > 0. Analogously, in the
negative case, a must be negative, and we reach the same conclusion.
-/
theorem om2025_s1_p1 (a b c : ℝ) (ha : a ≠ 0) (h_no_roots : ∀ (x : ℝ), a * x ^ 2 + b * x + c ≠ 0)
  : a * (2 * a + 3 * b + 6 * c) > 0 := by

  suffices h_simp : a * (a * 3 / 2 + 3 * b + 6 * c) > 0
  have : a * a * 1 / 2 > 0 := mul_pos (mul_pos (mul_self_pos.2 ha) (by norm_num)) (by norm_num)
  linarith

  have : a * (a * (1/2) ^ 2 + b * (1/2) + c) > 0 := no_root_quadratic_mul_lead_is_pos a b c ha h_no_roots (1/2)
  linarith
