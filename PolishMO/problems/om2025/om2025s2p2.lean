import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Mathlib.FieldTheory.Finite.Basic

import PolishMO.Prime

open Nat

-- Given: q ∣ n - 1, q ≠ 2, q is prime, n ≥ 5
-- Show: q ∣ n * 2^(q-1) - 1

lemma q_divides_n_times_pow_sub_one (n q : ℕ) (hn : n ≥ 5)  (hq : q ∣ n - 1) (hq2 : q ≠ 2) (hq_prime : Nat.Prime q) :
    q ∣ n * 2^(q - 1) - 1 := by

  -- Since q ∣ n - 1, then n ≡ 1 [MOD q]
  have n_mod_q : n ≡ 1 [MOD q] := by
    symm
    rw [modEq_iff_dvd']
    exact hq
    exact (by decide : 1 ≤ 5).trans hn

  have coprime_q_2 : Nat.Coprime q 2 := by
    rw [coprime_primes hq_prime Nat.prime_two]
    exact hq2

  -- FLT: 2^(q - 1) ≡ 1 [MOD q]
  have hmod_pow : 2^(q - 1) ≡ 1 [MOD q] := by
    rw [<- Nat.totient_prime]
    apply Nat.ModEq.pow_totient coprime_q_2.symm
    exact hq_prime

  -- Multiply both sides: n * 2^(q - 1) ≡ n * 1 ≡ 1 [MOD q]
  have flt_n : n * 2^(q - 1) ≡ 1 [MOD q] := Nat.ModEq.mul n_mod_q hmod_pow

  have one_le_x : 1 ≤ n*2^(q-1) :=
    Nat.le_trans (by decide) (mul_le_mul hn (Nat.pow_pos (by norm_num)) zero_le_one (Nat.zero_le n))

  -- So q ∣ n * 2^(q - 1) - 1
  rw [<- (Nat.modEq_iff_dvd' one_le_x)]
  exact flt_n.symm


-- Given q | n - 3, q ≥ 4, q is prime, n ≥ 5
-- Show: q | n * 2^(q-2) - 1

lemma q_divides_n_times_pow_sub_one_p2 (n q : ℕ) (hn : n ≥ 5) (hq : q ∣ n - 2) (hq2 : q ≠ 2) (hq_prime : Nat.Prime q) :
    q ∣ n * 2^(q-2) - 1 := by

    -- Since q | n - 2, then n ≡ 3 [MOD q]
    have n_mod_q : n ≡ 2 [MOD q] := by
      symm
      rw [modEq_iff_dvd']
      exact hq
      exact (by decide : 2 ≤ 5).trans hn

    have coprime_q_2 : Nat.Coprime q 2 := by
      rw [coprime_primes hq_prime Nat.prime_two]
      exact hq2

    -- FLT: 2^(q - 1) ≡ 1 [MOD q]
    have flt : 2^(q - 1) ≡ 1 [MOD q] := by
      rw [<- Nat.totient_prime]
      apply Nat.ModEq.pow_totient coprime_q_2.symm
      exact hq_prime

    -- Multiply both sides: n * 2^(q - 1) ≡ 1 [MOD q]
    have flt_n : n * 2^(q - 2) ≡ 1 [MOD q] := by
      apply Nat.ModEq.trans (Nat.ModEq.mul_right (2^(q-2)) n_mod_q)
      rw [<- Nat.pow_succ', Nat.succ_eq_add_one]

      have one_plus_one_eq_two : 1 + 1 = 2 := Nat.add_one 1
      nth_rewrite 2 [<- one_plus_one_eq_two]
      rw [Nat.sub_add_eq, Nat.sub_add_cancel]

      exact flt

      have hqge2 : q ≥ 2 := Nat.Prime.two_le hq_prime
      exact Nat.sub_le_sub_right hqge2 1

    have one_le_x : 1 ≤ n*2^(q-2) :=
      Nat.le_trans (by decide) (mul_le_mul hn (Nat.pow_pos (by norm_num)) zero_le_one (Nat.zero_le n))

    rw [<- (Nat.modEq_iff_dvd')]
    exact flt_n.symm
    exact one_le_x


/-- Lemma: if n is greater or equal to 5, there exists a prime q dividing some n*2^k-1 -/
lemma exists_q_dividing_x (n : ℕ) (hn : n ≥ 5)
  : ∃ (q k : ℕ), Nat.Prime q ∧ 2 < q ∧ q < n ∧ 2 ≤ k ∧ k ≤ n ∧ q ∣ n * 2^k - 1 := by

  have hzero : 0 < n := by
    linarith

  have one_is_odd : (Odd (n-1)) ∨ (Odd (n-2)) := by
    have one_plus_one_eq_two : 1 + 1 = 2 := Nat.add_one 1

    cases' (Nat.even_or_odd (n-2)) with hl hr
    rw [<- Nat.not_odd_iff_even, <- Nat.odd_add_one, <-one_plus_one_eq_two, Nat.sub_add_eq, Nat.sub_add_cancel] at hl
    left; exact hl
    exact Nat.le_trans (by decide) (Nat.sub_le_sub_right hn 1)
    right; exact hr

  have exists_odd_prime_factor_of_odd_ge_three (m : ℕ) (hm_ge : m ≥ 3) (hm_odd : Odd m) :
    ∃ p, Prime p ∧ p ∣ m ∧ p ≠ 2 := by

    have h2 : 2 ≤ m := Nat.le_trans (by decide) hm_ge
    have h3 : m ≠ 1 := by linarith
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h3

    have m_not_even : ¬ Even m := by
      rw[<- Nat.not_even_iff_odd] at hm_odd
      exact hm_odd

    by_contra! hp_eq
    rw [hp_eq p] at hp_dvd
    rw [Nat.even_iff, Nat.mod_eq_zero_of_dvd] at m_not_even
    trivial
    exact hp_dvd
    exact hp_prime
    exact hp_dvd


  cases' one_is_odd with hl hr
  have hnm1 : n - 1 ≥ 3 := by exact Nat.le_trans (by decide) (Nat.sub_le_sub_right hn 1)

  obtain ⟨q, hq_prime, hq_dvd, hq_ne_two⟩ := exists_odd_prime_factor_of_odd_ge_three (n - 1) hnm1 hl
  have hq_div : q ∣ n * 2 ^ (q - 1) - 1 := q_divides_n_times_pow_sub_one n q hn hq_dvd hq_ne_two hq_prime

  have hk_lower : 2 ≤ q-1 := by
    rw [Nat.le_sub_iff_add_le]
    simp
    have : 2 ≤ q := Nat.Prime.two_le hq_prime
    rw [Nat.le_iff_lt_or_eq] at this
    cases' this with hl hr
    exact Nat.succ_le_of_lt hl
    exact absurd hr.symm hq_ne_two
    exact (Nat.Prime.one_le hq_prime)

  have hkt_lower : 3 <= q := by
    have : 2+1 <= (q-1) + 1 := Nat.add_le_add_right hk_lower 1
    rw [Nat.sub_add_cancel] at this
    linarith
    exact Nat.Prime.one_le hq_prime

  have q_leq_n_sub_one: q <= n-1 := Nat.le_of_dvd (Nat.le_trans (by decide) (Nat.sub_le_sub_right hn 1)) hq_dvd
  have q_le_n : q < n := by
    exact Nat.lt_of_le_pred hzero q_leq_n_sub_one

  have q_sub_one_leq_n : q-1 <= n := by
    have : q - 1 ≤ n - 1 - 1 := Nat.sub_le_sub_right q_leq_n_sub_one 1
    rw [Nat.sub_sub] at this
    exact Nat.le_trans this (Nat.sub_le _ _)

  exact ⟨q, q-1, hq_prime, by linarith, q_le_n, hk_lower, q_sub_one_leq_n, hq_div⟩

  have hn_low : n-2 >= 3 := by exact Nat.le_trans (by decide) (Nat.sub_le_sub_right hn 2)
  obtain ⟨q, hq_prime, hq_dvd, hq_ne_two⟩ := exists_odd_prime_factor_of_odd_ge_three (n - 2) hn_low hr

  have two_lt_q : 2 < q := by
    have : 2 ≤ q := Nat.Prime.two_le hq_prime
    rw [Nat.le_iff_lt_or_eq] at this
    cases' this with hl hr
    exact hl
    exact absurd hr.symm hq_ne_two

  have q_leq_n_sub_two: q <= n-2 := Nat.le_of_dvd (Nat.le_trans (by decide) (Nat.sub_le_sub_right hn 2)) hq_dvd
  have q_lt_n : q < n := by
    apply Nat.lt_of_le_of_lt q_leq_n_sub_two
    exact Nat.sub_lt hzero (by decide)

  have q_sub_two_lt_n : q-2 ≤ n := by
    have : q - 2 ≤ n - 2 := Nat.sub_le_sub_right (Nat.le_of_lt q_lt_n) 2
    exact Nat.le_trans this (Nat.sub_le _ _)

  have q_ge_three : 3 <= q := prime_ge_three_if_not_two q hq_prime hq_ne_two

  rcases Nat.lt_or_eq_of_le q_ge_three with hq_gt_3 | hq_eq_3
  have : q ≠ 3 := by linarith
  have : 5 ≤ q := Nat.Prime.five_le_of_ne_two_of_ne_three hq_prime hq_ne_two this

  -- Case q >= 5
  have q_sub_two_ge_2 : 2 ≤ q-2 := by
    rw [<- Nat.add_le_add_iff_right, Nat.sub_add_cancel]
    simp
    linarith
    linarith

  have hq_div :  q ∣ n * 2 ^ (q - 2) - 1 := q_divides_n_times_pow_sub_one_p2 n q hn hq_dvd hq_ne_two hq_prime
  exact ⟨q, q-2, hq_prime, two_lt_q, q_lt_n, q_sub_two_ge_2, q_sub_two_lt_n, hq_div⟩

  -- Case q = 3
  have n_eq_2_mod_q : n ≡ 2 [MOD q] := by
    symm
    rw [Nat.modEq_iff_dvd']
    exact hq_dvd
    linarith

  have two_pow_3_mod_q : 2 ^ 3 ≡ 2 [MOD q] := by
    rw [<- hq_eq_3]
    decide

  have x_eq_one_mod_q : n * 2 ^ 3 ≡ 1 [MOD q] := by
    have := Nat.ModEq.mul n_eq_2_mod_q two_pow_3_mod_q
    rw [<- hq_eq_3] at this
    rw [<- hq_eq_3]
    simp at this
    simp
    exact this

  have q_div_x : q ∣ n * 2 ^ 3 - 1 := by
    rw [<- Nat.modEq_iff_dvd']
    exact x_eq_one_mod_q.symm
    simp
    linarith

  exact ⟨q, 3, hq_prime, two_lt_q, q_lt_n, (by linarith), (by linarith), q_div_x⟩


lemma exists_k_with_x_not_prime (n : ℕ) (hn : n ≥ 5)
  : ∃ (k : ℕ), 2 ≤ k ∧ k ≤ n ∧ ¬ (Nat.Prime (n * 2 ^ k - 1)) := by

  obtain ⟨q, k, hq_prime, hq_gt_two, hq_lt_n, hk_ge_two, hk_le_n, hq_dvd⟩ := exists_q_dividing_x n hn
  have : q < n * 2 ^ k - 1 := by
    have : n < n * 2 ^ k - 1 := by
      have two_pow_k : 2 ^ 2 ≤ 2 ^ k := by
        exact Nat.pow_le_pow_right (by decide) hk_ge_two
      simp at two_pow_k
      have hnq1 : n * 4 ≤ n * 2 ^ k := Nat.mul_le_mul_left n two_pow_k

      have h_gt : n * 4 > n + 1 := by
        calc
          n * 4 = n * 3 + n * 1 := by rw [Nat.mul_add n 3 1]
              _ ≥ n * 3 + 5 := by linarith
              _ > n + 1 := by linarith
      have n_ge_one : n + 1 ≥ 1 := by linarith
      have h_gt1 : n * 4 - 1 > n := Nat.sub_lt_sub_right n_ge_one h_gt
      have h_gt2 : n * 4 - 1 ≤ n * 2 ^ k - 1 := Nat.sub_le_sub_right hnq1 1

      calc
        n < n * 4 - 1 := h_gt1
        _ ≤ n * 2 ^ k - 1 := h_gt2

    exact Nat.lt_trans hq_lt_n this

  exact ⟨k, hk_ge_two, hk_le_n, div_impl_not_prime (n * 2 ^ k - 1) q (Nat.le_of_lt hq_gt_two) this hq_dvd⟩


lemma om2025_s2_p2_dir_1 (n : ℕ) (hn : n ≥ 2)
  : (∀ k, 2 ≤ k ∧ k ≤ n → Nat.Prime (n * 2 ^ k - 1)) → n = 2 ∨ n = 3 := by

  intro h
  by_contra hne
  push_neg at hne

  have n_eq_4 : n = 4 := by
    have n_ge_4 : n ≥ 4 := by
      by_contra hnge
      push_neg at hnge
      interval_cases n
      simp at hne
      simp at hne

    have n_le_4 : n ≤ 4 := by
      by_contra hnge
      rw [Nat.not_le, Nat.lt_iff_add_one_le] at hnge
      simp at hnge

      obtain ⟨k, hk_ge_two, hk_le_n, hx_nprime⟩ := exists_k_with_x_not_prime n hnge
      have : Nat.Prime (n*2^k-1) := by
        apply h
        exact ⟨hk_ge_two, hk_le_n⟩
      exact absurd this hx_nprime
    linarith

  rw [n_eq_4] at h
  have := h 2
  simp at this
  norm_num at this


lemma om2025_s2_p2_dir_2 (n : ℕ)
  : (n = 2 ∨ n = 3) → (∀ k, 2 ≤ k ∧ k ≤ n → Nat.Prime (n * 2 ^ k - 1)) := by

  intro h

  cases' h with hl hr
  -- Case n=2
  by_contra hne
  push_neg at hne
  rw [hl] at hne
  obtain ⟨k, ⟨hk2, hk2'⟩, hnotprime⟩ := hne
  have : k=2 := by linarith
  rw [this] at hnotprime
  norm_num at hnotprime

  -- Case n=3
  by_contra hne
  push_neg at hne
  rw [hr] at hne
  obtain ⟨k, ⟨hk2, hk2'⟩, hnotprime⟩ := hne
  interval_cases k
  all_goals {norm_num at hnotprime}


/--
**OM2025: STAGE 2 - PROBLEM 2**
---
Problem: Find all integers n ≥ 2, such that for all values k∈{2,...,n}, the number n*2^k-1 is prime. \
Answer: This condition is staisfied only for n ∈ {2,3} \
\
Solution: We can manually check that n ∈ {2,3} satisfies the conditions and that n=4 does not (4 * 2^2-1=15 is not prime).
Hence, it suffices to show that n ≥ 5 does not satisfy this property. Consider two cases:
- n is even: then. n-1 is odd, so has an odd prime divisor p. By Fermat's Litle Theorem, for k=p-1 we hence have
n* 2^k-1 ≡ 1* 2(p-1)-1 ≡ 1-1 ≡ 0 [MOD p], and clearly n * 2^k-1 > p, so n * 2^k-1 is not prime. Finally, note that
2 ≤ p-1 = k and k ≤ p ≤ n, so choosing k=p-1, we reach a contradiction.
- n is odd: similarly as before, n-2 has an odd prime factor q. If q=3, then n*2^3-1 ≡ 2 *8-1 ≡ 0 [MOD q]. Otherwise,
we can take k=q-2, getting n * 2^k-1 ≡ 2 * 2^(q-2) - 1 ≡ 2^(q-1)-1 ≡ 0 [MOD q] by Fermat's Little Theorem. Trivially,
k ∈ {2, ..., n}, so either way, we reach a contradiction.
-/
theorem om2025_s2_p2 (n : ℕ) (hn : n ≥ 2)
  : (∀ k, 2 ≤ k ∧ k ≤ n → Nat.Prime (n * 2 ^ k - 1)) ↔ n = 2 ∨ n = 3 := by
  exact Iff.intro (om2025_s2_p2_dir_1 n hn) (om2025_s2_p2_dir_2 n)
