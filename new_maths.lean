```lean
import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open Nat
open ZMod

-- Lemma: For prime p, C(p-1, k) ≡ (-1)^k mod p
lemma choose_p_minus_one_mod_prime_simple (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : k < p) :
    ((p-1).choose k : ZMod p) = (-1 : ZMod p) ^ k := by
  have hk_le : k ≤ p-1 := by omega
  have : (p-1).choose k = ((p-1).descFactorial k) / k ! := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
  simp_rw [this]
  have h_num : ((p-1).descFactorial k : ZMod p) = (-1 : ZMod p) ^ k * (k ! : ZMod p) := by
    induction' k with m IH
    · simp
    · have : (p-1).descFactorial (m+1) = (p-1-m) * (p-1).descFactorial m := by
        rw [Nat.descFactorial_succ]
      simp_rw [this]
      have : (p-1-m : ZMod p) = (-1 : ZMod p) * (m+1 : ZMod p) := by
        simp [show (p : ZMod p) = 0 from by simp]
      rw [this, IH]
      ring
  rw [h_num]
  field_simp [show (k ! : ZMod p) ≠ 0 from by
    intro h
    have : (k ! : ℕ) ≡ 0 [MOD p] := by simpa using h
    have := hp.dvd_factorial.mpr (by omega : k < p)
    exact this (by simpa [ZMod.nat_cast_zmod_eq_zero_iff_dvd] using h)]

-- Helper lemma: sum of m-th powers of units is 0 for 1 ≤ m ≤ p-2
lemma sum_pow_units_eq_zero (p : ℕ) (hp : p.Prime) (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ p-2) :
    (∑ x in (Finset.Icc 1 (p-1) : Finset (ZMod p)), x ^ m) = 0 := by
  -- The units of Z/pZ are {1, 2, ..., p-1}
  -- For a cyclic group G of order n, sum_{g in G} g^m = 0 if n ∤ m
  -- Here n = p-1, and 1 ≤ m ≤ p-2, so p-1 ∤ m
  have h_units : (Finset.Icc 1 (p-1) : Finset (ZMod p)) = (ZMod p)ˣ := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_Icc.1 hx with ⟨hx1, hx2⟩
      exact Units.mk0 x (by
        intro h
        have : x.val = 0 := by simpa using h
        omega)
    · intro hx
      have hx' : (x : ZMod p) ≠ 0 := Units.ne_zero x
      have : 1 ≤ x.val ∧ x.val ≤ p-1 := by
        constructor
        · by_contra! H
          have : x.val = 0 := by omega
          simp [this] at hx'
        · exact ZMod.val_lt x
      exact Finset.mem_Icc.mpr this
  rw [h_units]
  exact ZMod.sum_pow_units_eq_zero hp hm1 hm2

-- Theorem: For 1 ≤ r ≤ p-2, H_{p-1}^{(r)} ≡ 0 mod p
theorem harmonic_power_sum_mod_prime (p : ℕ) (hp : p.Prime) (h : p > 3) (r : ℕ) (hr : 1 ≤ r) (hr_lt : r ≤ p-2) :
    (∑ k in Finset.Icc 1 (p-1), (k : ZMod p)⁻¹ ^ r) = 0 := by
  -- Since k^{p-1} ≡ 1 mod p for k ≠ 0, we have k^{-r} ≡ k^{p-1-r} mod p
  have h_power : ∀ (k : ZMod p), k ≠ 0 → k⁻¹ ^ r = k ^ (p-1-r) := by
    intro k hk
    calc
      k⁻¹ ^ r = (k⁻¹) ^ r := rfl
      _ = (k ^ (p-2)) ^ r := by rw [ZMod.inv_eq_pow_sub_two hp hk]
      _ = k ^ ((p-2)*r) := by rw [pow_mul]
      _ = k ^ (r*(p-2)) := by rw [mul_comm]
      _ = (k ^ r) ^ (p-2) := by rw [mul_comm, pow_mul]
      _ = (k ^ r)⁻¹ := by rw [ZMod.inv_eq_pow_sub_two hp (pow_ne_zero r hk)]
      _ = k⁻¹ ^ r := by rw [inv_pow]
      -- Actually we need k^{-r} = k^{p-1-r}
      -- Since k^{p-1} = 1, we have k^r * k^{p-1-r} = 1, so k^{p-1-r} = k^{-r}
  -- Simpler: k^{-1} = k^{p-2}, so k^{-r} = k^{r(p-2)} = k^{p-1-r} because k^{p-1} = 1
  have h_power_simple : ∀ (k : ZMod p), k ≠ 0 → k⁻¹ ^ r = k ^ (p-1-r) := by
    intro k hk
    calc
      k⁻¹ ^ r = (k ^ (p-2)) ^ r := by rw [ZMod.inv_eq_pow_sub_two hp hk]
      _ = k ^ ((p-2)*r) := by rw [pow_mul]
      _ = k ^ (r*(p-2)) := by rw [mul_comm]
      _ = (k ^ r) ^ (p-2) := by rw [mul_comm, pow_mul]
      _ = (k ^ r)⁻¹ := by rw [ZMod.inv_eq_pow_sub_two hp (pow_ne_zero r hk)]
      _ = k⁻¹ ^ r := by rw [inv_pow]
  -- Actually, let's use: k^{-r} = (k^{-1})^r = (k^{p-2})^r = k^{(p-2)r}
  -- And since k^{p-1} = 1, we have k^{(p-2)r} = k^{p-1-r} when working mod p-1 in exponent
  -- But in ZMod p, we have k^{p-1} = 1, so k^{a} = k^{b} if a ≡ b mod (p-1)
  have h_power_correct : ∀ (k : ZMod p), k ≠ 0 → k⁻¹ ^ r = k ^ (p-1-r) := by
    intro k hk
    have : k ^ (p-1) = 1 := ZMod.pow_card_sub_one_eq_one hp hk
    calc
      k⁻¹ ^ r = (k⁻¹) ^ r := rfl
      _ = (k ^ (p-2)) ^ r := by rw [ZMod.inv_eq_pow_sub_two hp hk]
      _ = k ^ ((p-2)*r) := by rw [pow_mul]
      _ = k ^ ((p-1-r) + (r-1)*(p-1)) := by
        have : (p-2)*r = (p-1-r) + (r-1)*(p-1) := by
          ring
          omega
        rw [this]
      _ = k ^ (p-1-r) * k ^ ((r-1)*(p-1)) := by rw [pow_add]
      _ = k ^ (p-1-r) * (k ^ (p-1)) ^ (r-1) := by rw [mul_comm, pow_mul]
      _ = k ^ (p-1-r) * 1 ^ (r-1) := by rw [this]
      _ = k ^ (p-1-r) * 1 := by simp
      _ = k ^ (p-1-r) := by simp
  -- Now compute the sum
  calc
    (∑ k in Finset.Icc 1 (p-1), (k : ZMod p)⁻¹ ^ r) =
        (∑ k in Finset.Icc 1 (p-1), (k : ZMod p) ^ (p-1-r)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rcases Finset.mem_Icc.1 hk with ⟨hk1, hk2⟩
      have hk0 : (k : ZMod p) ≠ 0 := by
        intro h
        have : k = 0 := by simpa using h
        omega
      rw [h_power_correct (k : ZMod p) hk0]
    _ = 0 := sum_pow_units_eq_zero p hp (p-1-r) (by omega) (by omega)

-- Special case: r = p-1
theorem harmonic_power_sum_mod_prime_last (p : ℕ) (hp : p.Prime) (h : p > 3) :
    (∑ k in Finset.Icc 1 (p-1), (k : ZMod p)⁻¹ ^ (p-1)) = -1 := by
  -- For r = p-1, k^{-(p-1)} = (k^{-1})^{p-1} = (k^{p-2})^{p-1} = k^{(p-2)(p-1)}
  -- But k^{p-1} = 1, so k^{(p-2)(p-1)} = (k^{p-1})^{p-2} = 1
  have : ∀ (k : ZMod p), k ≠ 0 → (k : ZMod p)⁻¹ ^ (p-1) = 1 := by
    intro k hk
    calc
      k⁻¹ ^ (p-1) = (k⁻¹) ^ (p-1) := rfl
      _ = (k ^ (p-2)) ^ (p-1) := by rw [ZMod.inv_eq_pow_sub_two hp hk]
      _ = k ^ ((p-2)*(p-1)) := by rw [pow_mul]
      _ = (k ^ (p-1)) ^ (p-2) := by rw [← pow_mul, mul_comm (p-1) (p-2)]
      _ = 1 ^ (p-2) := by rw [ZMod.pow_card_sub_one_eq_one hp hk]
      _ = 1 := by simp
  calc
    (∑ k in Finset.Icc 1 (p-1), (k : ZMod p)⁻¹ ^ (p-1)) =
        (∑ k in Finset.Icc 1 (p-1), (1 : ZMod p)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rcases Finset.mem_Icc.1 hk with ⟨hk1, hk2⟩
      have hk0 : (k : ZMod p) ≠ 0 := by
        intro h
        have : k = 0 := by simpa using h
        omega
      simp [this (k : ZMod p) hk0]
    _ = ((p-1) : ℕ) • (1 : ZMod p) := by simp [Finset.sum_const_nsmul]
    _ = (p-1 : ZMod p) := by simp
    _ = -1 := by
      simp [show (p : ZMod p) = 0 from by simp]

-- Complete classification theorem
theorem generalized_wolstenholme_complete (p : ℕ) (hp : p.Prime) (h : p > 3) (r : ℕ) (hr : 1 ≤ r) :
    (∑ k in Finset.Icc 1 (p-1), (-1 : ZMod p) ^ (k-1) * ((p-1).choose k : ZMod p) * (k : ZMod p)⁻¹ ^ r) =
      if r ≤ p-2 then 0 else 1 := by
  -- First, C(p-1, k) ≡ (-1)^k mod p
  have hbinom : ∀ k, k ∈ Finset.Icc 1 (p-1) → ((p-1).choose k : ZMod p) = (-1 : ZMod p) ^ k := by
    intro k hk
    rcases Finset.mem_Icc.1 hk with ⟨hk1, hk2⟩
    exact choose_p_minus_one_mod_prime_simple p hp k (by omega)
  -- Rewrite the sum as -H_{p-1}^{(r)}
  have h_sum_eq : (∑ k in Finset.Icc 1 (p-1), (-1 : ZMod p) ^ (k-1) * ((p-1).choose k : ZMod p) * (k : ZMod p)⁻¹ ^ r) =
      - (∑ k in Finset.Icc 1 (p-1), (k : ZMod p)⁻¹ ^ r) := by
    calc
      (∑ k in Finset.Icc 1 (p-1), (-1 : ZMod p) ^ (k-1) * ((p-1).choose k : ZMod p) * (k : ZMod p)⁻¹ ^ r) =
      (∑ k in Finset.Icc 1 (p-1), (-1 : ZMod p) ^ (k-1) * (-1 : ZMod p) ^ k * (k : ZMod p)⁻¹ ^ r) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hbinom k hk]
      _ = (∑ k in Finset.Icc 1 (p-1), (-1 : ZMod p) ^ (2*k-1) * (k : ZMod p)⁻¹ ^ r) := by
        apply Finset.sum_congr rfl
        intro k hk
        have : (-1 : ZMod p) ^ (k-1) * (-1 : ZMod p) ^ k = (-1 : ZMod p) ^ (2*k-1) := by
          rw [← pow_add, show (k-1 : ℕ) + k = 2*k-1 by omega]
        rw [this]
      _ = (∑ k in Finset.Icc 1 (p-1), -((k : ZMod p)⁻¹ ^ r)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have : (-1 : ZMod p) ^ (2*k-1) = -1 := by
          have : (2*k-1 : ℕ) = 2*k - 1 := by omega
          rw [this]
          simp
        rw [this]
        ring
      _ = - (∑ k in Finset.Icc 1 (p-1), (k : ZMod p)⁻¹ ^ r) := by
        rw [Finset.sum_neg_distrib]
  rw [h_sum_eq]
  by_cases hr_le : r ≤ p-2
  · -- Case 1: 1 ≤ r ≤ p-2
    rw [if_pos hr_le]
    rw [harmonic_power_sum_mod_prime p hp h r hr hr_le, neg_zero]
  · -- Case 2: r ≥ p-1
    rw [if_neg (by omega)]
    have : r = p-1 := by omega
    rw [this]
    rw [harmonic_power_sum_mod_prime_last p hp h]
    simp

-- Test all cases for small primes
example : (∑ k in Finset.Icc 1 4, (-1 : ZMod 5) ^ (k-1) * ((4).choose k : ZMod 5) * (k : ZMod 5)⁻¹ ^ 1) = 0 := by
  native_decide

example : (∑ k in Finset.Icc 1 4, (-1 : ZMod 5) ^ (k-1) * ((4).choose k : ZMod 5) * (k : ZMod 5)⁻¹ ^ 2) = 0 := by
  native_decide

example : (∑ k in Finset.Icc 1 4, (-1 : ZMod 5) ^ (k-1) * ((4).choose k : ZMod 5) * (k : ZMod 5)⁻¹ ^ 3) = 0 := by
  native_decide

example : (∑ k in Finset.Icc 1 4, (-1 : ZMod 5) ^ (k-1) * ((4).choose k : ZMod 5) * (k : ZMod 5)⁻¹ ^ 4) = 1 := by
  native_decide

example : (∑ k in Finset.Icc 1 6, (-1 : ZMod 7) ^ (k-1) * ((6).choose k : ZMod 7) * (k : ZMod 7)⁻¹ ^ 1) = 0 := by
  native_decide

example : (∑ k in Finset.Icc 1 6, (-1 : ZMod 7) ^ (k-1) * ((6).choose k : ZMod 7) * (k : ZMod 7)⁻¹ ^ 2) = 0 := by
  native_decide

example : (∑ k in Finset.Icc 1 6, (-1 : ZMod 7) ^ (k-1) * ((6).choose k : ZMod 7) * (k : ZMod 7)⁻¹ ^ 5) = 0 := by
  native_decide

example : (∑ k in Finset.Icc 1 6, (-1 : ZMod 7) ^ (k-1) * ((6).choose k : ZMod 7) * (k : ZMod 7)⁻¹ ^ 6) = 1 := by
  native_decide
```
