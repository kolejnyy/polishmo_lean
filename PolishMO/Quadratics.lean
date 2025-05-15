import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

import Mathlib.Tactic

open Nat
open Real


lemma normalized_quadratic_impl_root (x a b : ℝ) (h : x ^ 2 + a * x + b < 0)
  : ∃ (x : ℝ), x ^ 2 + a * x + b = 0 := by

  have h_decomp : (x + (a/2)) ^ 2 - (a^2/4 - b) < 0 := by linarith
  have : (x + (a/2)) * (x + (a/2)) ≥ 0 := mul_self_nonneg (x + (a/2))
  have hdelta : (a^2/4 - b) > 0 := by linarith
  have hdelta : a^2 - 4 * 1 * b > 0 := by linarith
  have hdisc : ∃ (s : ℝ), discrim 1 a b = s * s := by
    use Real.sqrt (discrim 1 a b)
    rw [discrim, <- Real.sqrt_mul]
    exact (Real.sqrt_mul_self hdelta.le).symm
    exact hdelta.le
  apply exists_quadratic_eq_zero (one_ne_zero) at hdisc
  simp at hdisc
  obtain ⟨y, hy_root⟩ := hdisc
  rw [<- pow_two y] at hy_root
  exact ⟨y, hy_root⟩


lemma no_root_quadratic_mul_lead_is_pos (a b c : ℝ) (ha : a ≠ 0)
  (h_no_roots : ∀ (x : ℝ), a * x ^ 2 + b * x + c ≠ 0)
  : ∀ (x : ℝ), a * (a * x ^ 2 + b * x + c) > 0 := by

  -- Case: a is positive
  by_cases ha_pos : a > 0
  by_contra hneg
  push_neg at hneg
  obtain ⟨x, hneg⟩ := hneg
  rw [le_iff_lt_or_eq] at hneg
  cases' hneg with hl hr
  have : (a * x ^ 2 + b * x + c) < 0 := lt_of_mul_lt_mul_left (by linarith) (ha_pos.le)
  have : x ^ 2 + (b / a) * x + (c / a) < 0 := by
    apply mul_lt_mul_of_pos_right at this
    have inv_a_pos : 0 < (1/a) := one_div_pos.mpr ha_pos
    have : (a * x ^ 2 + b * x + c) * ?a < 0 * ?a := this inv_a_pos
    field_simp [ha_pos] at this
    field_simp [ha_pos]
    rw [mul_comm]
    exact this
  have has_root : ∃ (x : ℝ), x ^ 2 + (b/a) * x + (c/a) = 0 := normalized_quadratic_impl_root x (b/a) (c/a) this
  obtain ⟨y, hy_isroot⟩ := has_root
  rw [<- mul_left_inj' ha] at hy_isroot
  field_simp [ha_pos] at hy_isroot
  rw [mul_comm] at hy_isroot
  exact absurd hy_isroot (h_no_roots y)
  simp at hr
  cases' hr with hrl hrr
  linarith
  exact absurd hrr (h_no_roots x)

  -- Case: a is negative
  simp at ha_pos
  have ha_neg : a < 0 := lt_of_le_of_ne ha_pos ha
  by_contra hneg

  push_neg at hneg
  obtain ⟨x, hneg⟩ := hneg
  rw [le_iff_lt_or_eq] at hneg
  cases' hneg with hl hr
  have hrt: (-a) * (a * x ^ 2 + b * x + c) > (-a) * 0 := by linarith
  have ha_neg : -a ≥ 0 := by linarith
  have hrt2 : (a * x ^ 2 + b * x + c) > 0 := lt_of_mul_lt_mul_left hrt ha_neg
  have : x ^ 2 + (b / a) * x + (c / a) < 0 := by
    apply mul_lt_mul_of_pos_right at hrt2
    have inv_a_pos : 0 < (1/(-a)) := one_div_pos.mpr (by linarith)
    have htur : (a * x ^ 2 + b * x + c) * (1/(-a)) > 0 * (1/(-a)) := hrt2 inv_a_pos
    have : (a * x ^ 2 + b * x + c) * (1/(a)) < 0 * (1/(a)) := by linarith
    field_simp [ha] at this
    field_simp [ha]
    rw [mul_comm]
    exact this
  have has_root : ∃ (x : ℝ), x ^ 2 + (b/a) * x + (c/a) = 0 := normalized_quadratic_impl_root x (b/a) (c/a) this
  obtain ⟨y, hy_isroot⟩ := has_root
  rw [<- mul_left_inj' ha] at hy_isroot
  field_simp [ha_pos] at hy_isroot
  rw [mul_comm] at hy_isroot
  exact absurd hy_isroot (h_no_roots y)
  simp at hr
  cases' hr with hrl hrr
  linarith
  exact absurd hrr (h_no_roots x)
