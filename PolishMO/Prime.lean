import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic


lemma prime_ge_three_if_not_two (q : ℕ) (hq_prime : Nat.Prime q) (hq_ne_two : q ≠ 2) :
  3 ≤ q := by
    have hk_lower : 2 ≤ q-1 := by
      rw [Nat.le_sub_iff_add_le]
      simp
      have : 2 ≤ q := Nat.Prime.two_le hq_prime
      rw [Nat.le_iff_lt_or_eq] at this
      cases' this with hl hr
      exact Nat.succ_le_of_lt hl
      exact absurd hr.symm hq_ne_two
      exact (Nat.Prime.one_le hq_prime)

    have : 2+1 <= (q-1) + 1 := Nat.add_le_add_right hk_lower 1
    rw [Nat.sub_add_cancel] at this
    linarith
    exact Nat.Prime.one_le hq_prime


lemma div_impl_not_prime (n p : ℕ) (hp_ge : p ≥ 2) (hp_lt_n : p < n) (hp_dvd_n : p ∣ n)
  : ¬ (Nat.Prime n) := by
  by_contra hn_prime
  rw [Nat.Prime.dvd_iff_eq hn_prime] at hp_dvd_n
  rw [Nat.lt_iff_le_and_ne] at hp_lt_n
  exact absurd hp_dvd_n hp_lt_n.right.symm
  linarith
