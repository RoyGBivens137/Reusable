/-
Copyright (c) 2025 Zachary Mullaghy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Mullaghy, Gianfranco Romaelle
-/
import FourierBochner.Defs
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.flexible false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.style.show false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false

open Complex Real MeasureTheory Finset
open scoped FourierTransform ComplexConjugate

namespace FourierBochner

/-- Conjugate pairing for characters.

Both conj(character(k,m)) and character(-k,m) are the inverse of character(k,m),
so they must be equal. -/
lemma character_conjugate_pair (n : ℕ) [NeZero n] (k m : ZMod n) :
    conj (character n k m) = character n (-k) m := by
  classical
  unfold character
  -- split on k = 0 because (-k).val is piecewise
  by_cases hk : k = 0
  · subst hk
    simp
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne n)
  -- In the nonzero case: (-k).val = n - k.val
  have hnegval : (-k).val = n - k.val := by
    -- your mathlib has `ZMod.neg_val`
    rw [ZMod.neg_val]
    simp [hk]
  -- Use conj(exp z) = exp(conj z)
  rw [← Complex.exp_conj]
  -- Let r be the real fraction inside (cast to ℝ first, then to ℂ)
  set r : ℂ := ((k.val * m.val : ℝ) / (n : ℝ) : ℂ) with hr
  -- Conjugate flips I, but fixes r because r is real
  have hconj_r : conj r = r := by
    -- r is a quotient of real numbers, hence conj = id
    rw [hr]
    -- Show this equals ofReal of the real division
    have : ((k.val * m.val : ℝ)
     / (n : ℝ) : ℂ) = Complex.ofReal ((k.val * m.val : ℝ) / (n : ℝ)) := by
      push_cast; rfl
    rw [this]
    exact Complex.conj_ofReal _
  have hconj_exp :
      conj (2 * π * I * r) = -(2 * π * I * r) := by
    -- conj distributes; conj(I) = -I; conj(r)=r
    rw [map_mul, map_mul, map_mul, hconj_r]
    simp only [conj_ofReal, conj_I, map_ofNat]
    ring
  -- replace conj(...) by -(...)
  rw [hconj_exp]
  -- goal is now:
  -- exp (-(2π i r)) = exp (2π i * (((-k).val*m.val)/n))
  -- Rewrite the RHS fraction using (-k).val = n - k.val
  -- Need to match the character definition's coercion structure
  have hfrac :
      (((-k).val * m.val : ℝ) / (n : ℝ) : ℂ)
        = (m.val : ℂ) - r := by
    -- Start from the LHS and use hnegval
    rw [hr]
    have hk_le : k.val ≤ n := Nat.le_of_lt (ZMod.val_lt k)
    -- First show (-k).val * m.val = (n - k.val) * m.val
    have hneg_eq : ((-k).val * m.val : ℝ) = ((n - k.val) * m.val : ℝ) := by
      simp only [hnegval]
      rw [Nat.cast_sub hk_le]
    -- Now prove the algebraic identity
    calc (((-k).val * m.val : ℝ) / (n : ℝ) : ℂ)
        = (((n - k.val) * m.val : ℝ) / (n : ℝ) : ℂ) := by rw [hneg_eq]
      _ = (m.val : ℂ) - ((k.val * m.val : ℝ) / (n : ℝ) : ℂ) := by
          push_cast
          have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
          field_simp [hn_ne]
  -- Rewrite the RHS using hfrac, then use exp_add
  -- First, show the RHS exponent can be split
  have h_rhs_split : 2 * π * I * (((-k).val * m.val : ℝ) / (n : ℝ) : ℂ) =
                     (m.val : ℂ) * (2 * π * I) + (-(2 * π * I * r)) := by
    calc 2 * π * I * (((-k).val * m.val : ℝ) / (n : ℝ) : ℂ)
        = 2 * π * I * ((m.val : ℂ) - r) := by rw [hfrac]
      _ = 2 * π * I * (m.val : ℂ) - (2 * π * I * r) := by ring
      _ = (m.val : ℂ) * (2 * π * I) + (-(2 * π * I * r)) := by ring
  rw [h_rhs_split, Complex.exp_add]
  -- Now: exp(-(2πIr)) = exp((m.val)*(2πI)) * exp(-(2πIr))
  -- Show exp((m.val)*(2πI)) = 1
  have hexp_m : Complex.exp ((m.val : ℂ) * (2 * π * I)) = 1 := by
    rw [show (m.val : ℂ) * (2 * π * I) = ((m.val : ℤ) : ℂ) * (2 * π * I) by norm_cast]
    exact Complex.exp_int_mul_two_pi_mul_I (m.val : ℤ)
  rw [hexp_m]
  simp

/-- char_k(-m) = conj(char_k(m)). -/
lemma character_arg_conjugate (n : ℕ) [NeZero n] (k m : ZMod n) :
    character n k (-m) = conj (character n k m) := by
  unfold character
  by_cases hm : m = 0
  · -- If m = 0, then -m = 0
    subst hm
    simp
  -- For m ≠ 0: use (-m).val = n - m.val
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hnegval_m : (-m).val = n - m.val := by
    rw [ZMod.neg_val]
    simp [hm]
  -- Use conj(exp z) = exp(conj z)
  rw [← Complex.exp_conj]
  -- The fraction inside: k.val * m.val / n (viewed as complex)
  set r : ℂ := ((k.val * m.val : ℝ) / (n : ℝ) : ℂ) with hr
  -- This r is real, so conj(r) = r
  have hconj_r : conj r = r := by
    rw [hr]
    have : ((k.val * m.val : ℝ) / (n : ℝ) : ℂ) =
           Complex.ofReal ((k.val * m.val : ℝ) / (n : ℝ)) := by push_cast; rfl
    rw [this]
    exact Complex.conj_ofReal _
  -- conj(2πIr) = -2πIr since conj(I) = -I
  have hconj_exp : conj (2 * π * I * r) = -(2 * π * I * r) := by
    rw [map_mul, map_mul, map_mul, hconj_r]
    simp only [conj_ofReal, conj_I, map_ofNat]
    ring
  rw [hconj_exp]
  -- Now show exp(-(2πIr)) = exp(2πI·((-m).val·k.val/n))
  -- Use (-m).val = n - m.val to match the exponents
  have hfrac : (((-m).val * k.val : ℝ) / (n : ℝ) : ℂ) = (k.val : ℂ) - r := by
    rw [hr]
    have hm_le : m.val ≤ n := Nat.le_of_lt (ZMod.val_lt m)
    have hneg_eq : ((-m).val * k.val : ℝ) = ((n - m.val) * k.val : ℝ) := by
      simp only [hnegval_m]; rw [Nat.cast_sub hm_le]
    calc (((-m).val * k.val : ℝ) / (n : ℝ) : ℂ)
        = (((n - m.val) * k.val : ℝ) / (n : ℝ) : ℂ) := by rw [hneg_eq]
      _ = (k.val : ℂ) - ((k.val * m.val : ℝ) / (n : ℝ) : ℂ) := by
          push_cast
          have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
          field_simp [hn_ne]
  -- Split the RHS exponent
  have h_rhs_split : 2 * π * I * ((k.val * (-m).val : ℝ) / (n : ℝ) : ℂ) =
                     (k.val : ℂ) * (2 * π * I) + (-(2 * π * I * r)) := by
    have h_comm : ((k.val * (-m).val : ℝ)
    / (n : ℝ) : ℂ) = (((-m).val * k.val : ℝ) / (n : ℝ) : ℂ) := by
      congr 1; ring_nf
    calc 2 * π * I * ((k.val * (-m).val : ℝ) / (n : ℝ) : ℂ)
        = 2 * π * I * (((-m).val * k.val : ℝ) / (n : ℝ) : ℂ) := by rw [h_comm]
      _ = 2 * π * I * ((k.val : ℂ) - r) := by rw [hfrac]
      _ = 2 * π * I * (k.val : ℂ) - (2 * π * I * r) := by ring
      _ = (k.val : ℂ) * (2 * π * I) + (-(2 * π * I * r)) := by ring
  rw [h_rhs_split, Complex.exp_add]
  -- exp(k.val * 2πI) = 1
  have hexp_k : Complex.exp ((k.val : ℂ) * (2 * π * I)) = 1 := by
    rw [show (k.val : ℂ) * (2 * π * I) = ((k.val : ℤ) : ℂ) * (2 * π * I) by norm_cast]
    exact Complex.exp_int_mul_two_pi_mul_I (k.val : ℤ)
  rw [hexp_k]; simp

/-- Conjugate pairs multiply to 1: ω_k · ω_{-k} = 1

This is the KEY to phase cancellation -/
lemma character_conjugate_product (n : ℕ) [NeZero n] (k : ZMod n) :
    character n k 1 * character n (-k) 1 = 1 := by
  have h := character_conjugate_pair n k 1
  -- ω_k · ω_{-k} = ω_k · conj(ω_k) = |ω_k|² = 1
  rw [← h]
  -- Need: character(k,1) · conj(character(k,1)) = 1
  have h_on_circle : Complex.normSq (character n k 1) = 1 := by
    unfold character
    -- |e^{iθ}| = 1 for real θ, so |e^{iθ}|² = 1
    simp only [Complex.normSq_eq_norm_sq]
    -- ‖exp(z)‖ = exp(z.re), and our z has real part 0 (purely imaginary)
    rw [Complex.norm_exp]
    -- Compute the real part: (2πI * (real/real)).re = 0
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
               Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, zero_sub]
    norm_num
  -- normSq(z) = z · conj(z), so if normSq(z) = 1, then z · conj(z) = 1
  have : character n k 1 * conj (character n k 1) = Complex.normSq (character n k 1) := by
    exact Complex.mul_conj (character n k 1)
  rw [this, h_on_circle]
  norm_num

-- ============================================================================
-- P-ADIC TOWER STRUCTURE: Solution Permanence + Subdivision
-- ============================================================================

/-- The p^n-th roots embed in p^(n+1)-th roots via the p-adic tower. -/
lemma padic_tower_compatible
  (p n : ℕ) [Fact (Nat.Prime p)]
  (k : ZMod (p ^ (n + 1))) :
  character (p ^ (n + 1)) k 1 = character (p ^ (n + 2)) (p * k.cast) 1 := by
  -- Establish basic facts about p
  have hp : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := Nat.Prime.pos hp
  have hp_ne_zero : p ≠ 0 := Nat.Prime.ne_zero hp
  -- Establish that powers of p are nonzero
  have hp1_ne_zero : p ^ (n + 1) ≠ 0 := pow_ne_zero (n + 1) hp_ne_zero
  have hp2_ne_zero : p ^ (n + 2) ≠ 0 := pow_ne_zero (n + 2) hp_ne_zero
  have hp1_pos : 0 < p ^ (n + 1) := Nat.pos_of_ne_zero hp1_ne_zero
  have hp2_pos : 0 < p ^ (n + 2) := Nat.pos_of_ne_zero hp2_ne_zero
  haveI : NeZero (p ^ (n + 1)) := ⟨hp1_ne_zero⟩
  haveI : NeZero (p ^ (n + 2)) := ⟨hp2_ne_zero⟩
  -- Establish that p^(n+1) and p^(n+2) are > 1
  have hp1_gt_one : 1 < p ^ (n + 1) := by
    calc 1 < p := Nat.Prime.one_lt hp
         _ ≤ p ^ (n + 1) := by
           apply Nat.le_self_pow
           omega
  have hp2_gt_one : 1 < p ^ (n + 2) := by
    calc 1 < p := Nat.Prime.one_lt hp
         _ ≤ p ^ (n + 2) := by
           apply Nat.le_self_pow
           omega
  haveI : Fact (1 < p ^ (n + 1)) := ⟨hp1_gt_one⟩
  haveI : Fact (1 < p ^ (n + 2)) := ⟨hp2_gt_one⟩
  -- Unfold character definition
  unfold character
  congr 1
  -- Simplify 1.val to 1
  rw [ZMod.val_one, ZMod.val_one]
  ring_nf
  -- The goal is now: k.val / ↑(p ^ (n + 1)) = (p * k.cast).val / ↑(p ^ (n + 2))
  -- Key fact: k.cast.val = k.val (since k.val < p^(n+1) < p^(n+2))
  have hk_lt : k.val < p ^ (n + 2) := by
    have h1 : p ^ (n + 1) < p ^ (n + 2) := by
      have : p ^ (n + 2) = p * p ^ (n + 1) := by ring
      rw [this]
      calc p ^ (n + 1) = 1 * p ^ (n + 1) := by ring
           _ < p * p ^ (n + 1) := Nat.mul_lt_mul_of_pos_right (Nat.Prime.one_lt hp) hp1_pos
    exact Nat.lt_trans (ZMod.val_lt k) h1
  have hk_cast_val : (k.cast : ZMod (p ^ (n + 2))).val = k.val := by
    exact ZMod.val_cast_eq_val_of_lt hk_lt
  -- Key fact: (p * k.cast).val = p * k.val (since p * k.val < p^(n+2))
  have hp_mul_k_lt : p * k.val < p ^ (n + 2) := by
    calc p * k.val < p * p ^ (n + 1) := by
           exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt k) hp_pos
         _ = p ^ (n + 2) := by ring
  have hp_val : (p : ZMod (p ^ (n + 2))).val = p := by
    apply ZMod.val_cast_of_lt
    calc p = p ^ 1 := by rw [pow_one]
         _ < p ^ (n + 2) := by
           apply Nat.pow_lt_pow_right (Nat.Prime.one_lt hp)
           omega
  have h_mul_val : ((p : ZMod (p ^ (n + 2))) * k.cast).val = p * k.val := by
    rw [ZMod.val_mul]
    rw [hp_val, hk_cast_val]
    exact Nat.mod_eq_of_lt hp_mul_k_lt
  -- Now prove the division equality in ℂ
  have hp1_ne0_C : (p ^ (n + 1) : ℂ) ≠ 0 := by
    exact_mod_cast hp1_ne_zero
  have hp2_ne0_C : (p ^ (n + 2) : ℂ) ≠ 0 := by
    exact_mod_cast hp2_ne_zero
  have hp_ne0_C : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp_ne_zero
  -- Use the key fact that (p * k.cast).val = p * k.val
  rw [h_mul_val]
  -- Simplify the goal
  -- After ring_nf, the goal is:
  -- π * I * k.val * (p * p^n)⁻¹ * 2 = π * I * (p * k.val) * (p^2 * p^n)⁻¹ * 2
  -- This is true because (p * k.val) / (p^2 * p^n) = k.val / (p * p^n)
  have hpn_ne0 : (p * p ^ n : ℂ) ≠ 0 :=
    mul_ne_zero hp_ne0_C (pow_ne_zero n hp_ne0_C)
  have hp2pn_ne0 : (p ^ 2 * p ^ n : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hp_ne0_C) (pow_ne_zero n hp_ne0_C)
  field_simp [hpn_ne0, hp2pn_ne0]
  push_cast
  ring


/-- Going from p^n to p^(n+1) roots of unity adds (p-1)·p^n new roots. -/
lemma padic_tower_subdivision (p n : ℕ) [Fact (Nat.Prime p)]
    (k : ZMod (p ^ n)) (j : Fin p) (_hj : j.val ≠ 0) :
    character (p^(n+1)) (p * k.val + j.val : ZMod (p^(n+1))) 1 =
    Complex.exp (2 * π * I * ((k.val : ℝ) + (j.val : ℝ) / p) / (p^n : ℝ)) := by
  unfold character
  congr 1
  -- Key: p·k.val + j.val < p^(n+1), so taking .val is the identity
  have h_bound : p * k.val + j.val < p^(n+1) := by
    have hk : k.val < p^n := ZMod.val_lt k
    have hj : j.val < p := j.isLt
    have hp_pos : 0 < p := Nat.Prime.pos (Fact.out)
    -- Since k.val < p^n and j.val < p, we show p * k.val + j.val < p^(n+1)
    -- We split into two cases based on whether k.val + 1 = p^n or k.val + 1 < p^n
    by_cases h : k.val + 1 = p^n
    · -- Case: k.val = p^n - 1 (maximum possible value)
      -- Then p * k.val + j.val ≤ p * (p^n - 1) + (p - 1) = p^(n+1) - 1
      have hk_eq : k.val = p^n - 1 := by omega
      have hp_le : 1 ≤ p^n := Nat.one_le_pow n p hp_pos
      rw [hk_eq]
      have : p * (p^n - 1) + j.val < p * p^n := by
        have hp_le_ppn : p ≤ p * p^n := by
          calc p = p * 1 := by ring
               _ ≤ p * p^n := Nat.mul_le_mul_left p (Nat.one_le_pow n p hp_pos)
        calc p * (p^n - 1) + j.val
            < p * (p^n - 1) + p := Nat.add_lt_add_left hj _
          _ = p * p^n - p + p := by
              rw [Nat.mul_sub_left_distrib]
              simp only [mul_one]
          _ = p * p^n := Nat.sub_add_cancel hp_le_ppn
      calc p * (p^n - 1) + j.val < p * p^n := this
         _ = p^(n+1) := by ring
    · -- Case: k.val + 1 < p^n
      -- Then p * k.val + p ≤ p * p^n, so p * k.val + j.val < p * p^n
      have : k.val + 1 < p^n := by omega
      calc p * k.val + j.val
          < p * k.val + p := Nat.add_lt_add_left hj _
        _ = p * (k.val + 1) := by ring
        _ < p * p^n := Nat.mul_lt_mul_of_pos_left this hp_pos
        _ = p^(n+1) := by ring
  -- Simplify: The ZMod element has .val = p * k.val + j.val because it's < p^(n+1)
  conv_lhs =>
    arg 2
    rw [show (↑p * ↑k.val + ↑↑j : ZMod (p ^ (n + 1))).val = p * k.val + j.val by
      have : (↑p * ↑k.val + ↑↑j :
       ZMod (p ^ (n + 1))) = (↑(p * k.val + j.val) : ZMod (p ^ (n + 1))) := by
        push_cast; rfl
      rw [this, ZMod.val_natCast]
      exact Nat.mod_eq_of_lt h_bound]
  -- Now simplify: (p·k + j)·1 / p^(n+1) = (k + j/p) / p^n
  have hp : (p : ℂ) ≠ 0 := by
    norm_cast; exact Nat.Prime.ne_zero (Fact.out)
  have hpn : ((p^n : ℕ) : ℂ) ≠ 0 := by
    norm_cast; exact pow_ne_zero n (Nat.Prime.ne_zero (Fact.out))
  -- Need Fact instance for ZMod.val_one
  haveI : Fact (1 < p^(n+1)) := ⟨by
    have hp_ge_2 : 2 ≤ p := Nat.Prime.two_le (Fact.out : Nat.Prime p)
    calc 1 < 2 := by omega
         _ ≤ p := hp_ge_2
         _ = p^1 := by ring
         _ ≤ p^(n+1) := Nat.pow_le_pow_right (Nat.Prime.pos (Fact.out)) (by omega)⟩
  rw [ZMod.val_one]
  push_cast
  field_simp [hp, hpn]
  ring

/-- Chord-arc bound on the circle: Distance between two points on the unit circle
is at most the arc length (angle difference).

This is critical for defining a convergence metric -/
lemma norm_exp_I_sub_exp_I_le (θ β : ℝ) :
    ‖Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * β)‖ ≤ |θ - β| := by
  -- Factor: exp(I*θ) - exp(I*β) = exp(I*β) * (exp(I*(θ-β)) - 1)
  have h_factor : Complex.exp (Complex.I * θ) - Complex.exp (Complex.I * β) =
                  Complex.exp (Complex.I * β) * (Complex.exp (Complex.I * (θ - β)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    ring_nf
  rw [h_factor, norm_mul, Complex.norm_exp_I_mul_ofReal]
  -- Cast `(↑θ - ↑β)` to `↑(θ - β)` so the lemma about `I * (x : ℝ)` matches
  have : Complex.I * (↑θ - ↑β) = Complex.I * ↑(θ - β) := by push_cast; rfl
  rw [this, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp [Real.norm_eq_abs]
  calc
    2 * |Real.sin ((θ - β) / 2)| ≤ 2 * |(θ - β) / 2| := by
      apply mul_le_mul_of_nonneg_left Real.abs_sin_le_abs
      norm_num
    _ = |θ - β| := by rw [abs_div]; norm_num; ring

/-- Arg bound for RHP: For complex numbers in the Right Half Plane (Re > 0), -/
lemma abs_arg_sub_le_two_mul_norm_div_min_of_re_pos (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0)
    (hz_re : 0 < z.re) (hw_re : 0 < w.re) :
    |Complex.arg z - Complex.arg w| ≤ 2 * ‖z - w‖ / min ‖z‖ ‖w‖ := by
  have h_min_pos : 0 < min ‖z‖ ‖w‖ := lt_min (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw

  -- In RHP, arg z ∈ (-π/2, π/2), so |arg z - arg w| < π (no branch cut issues)
  have hz_arg_bound : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz_re)
  have hw_arg_bound : |Complex.arg w| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw_re)

  -- Therefore |arg z - arg w| < π
  have h_diff_lt_pi : |Complex.arg z - Complex.arg w| < Real.pi := by
    have h1 : |Complex.arg z - Complex.arg w| ≤ |Complex.arg z - 0| + |0 - Complex.arg w| :=
      abs_sub_le _ 0 _
    simp only [sub_zero, zero_sub, abs_neg] at h1
    calc |Complex.arg z - Complex.arg w|
        ≤ |Complex.arg z| + |Complex.arg w| := h1
      _ < Real.pi / 2 + Real.pi / 2 := add_lt_add hz_arg_bound hw_arg_bound
      _ = Real.pi := by ring

  -- Normalize to unit vectors
  let z' := z / ‖z‖
  let w' := w / ‖w‖

  have hz_norm_ne : (‖z‖ : ℂ) ≠ 0 := by simp [norm_ne_zero_iff.mpr hz]
  have hw_norm_ne : (‖w‖ : ℂ) ≠ 0 := by simp [norm_ne_zero_iff.mpr hw]
  have hz'_norm : ‖z'‖ = 1 := by simp [z', norm_div, norm_norm, div_self (norm_ne_zero_iff.mpr hz)]
  have hw'_norm : ‖w'‖ = 1 := by simp [w', norm_div, norm_norm, div_self (norm_ne_zero_iff.mpr hw)]
  have hz'_ne : z' ≠ 0 := by simp only [z']; exact div_ne_zero hz hz_norm_ne
  have hw'_ne : w' ≠ 0 := by simp only [w']; exact div_ne_zero hw hw_norm_ne

  -- arg is scale-invariant for positive scalars
  have hz_arg : Complex.arg z = Complex.arg z' := by
    simp only [z']
    have h_inv_pos : (0 : ℝ) < ‖z‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hz)
    rw [div_eq_mul_inv, mul_comm, ← Complex.ofReal_inv]
    exact (Complex.arg_real_mul z h_inv_pos).symm
  have hw_arg : Complex.arg w = Complex.arg w' := by
    simp only [w']
    have h_inv_pos : (0 : ℝ) < ‖w‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hw)
    rw [div_eq_mul_inv, mul_comm, ← Complex.ofReal_inv]
    exact (Complex.arg_real_mul w h_inv_pos).symm

  rw [hz_arg, hw_arg]

  -- For RHP points, |arg z - arg w| = |arg(z/w)| = angle(z, w)
  -- because the difference is < π (no wrapping)
  have h_arg_eq_angle : |Complex.arg z' - Complex.arg w'| = InnerProductGeometry.angle z' w' := by
    rw [Complex.angle_eq_abs_arg hz'_ne hw'_ne]
    -- When |arg z' - arg w'| < π, we have arg(z'/w') = arg z' - arg w'
    -- (the division formula: arg(z/w) = arg z - arg w + 2πk, with k=0 when diff ∈ (-π, π))
    have h_diff_lt : |Complex.arg z' - Complex.arg w'| < Real.pi := by
      rw [← hz_arg, ← hw_arg]; exact h_diff_lt_pi
    -- Use the arg_div formula from Mathlib
    have hdiv := Complex.arg_div_coe_angle hz'_ne hw'_ne
    -- arg(z'/w') as a Real.Angle equals arg z' - arg w'
    -- When |diff| < π, the principal value arg(z'/w') equals the difference
    -- This follows from the coe_angle injectivity on (-π, π]
    congr 1
    -- From |diff| < π, we get diff ∈ (-π, π)
    have h_abs := abs_lt.mp h_diff_lt
    have h_in_Ioo : Complex.arg z' - Complex.arg w' ∈ Set.Ioo (-Real.pi) Real.pi := ⟨h_abs.1, h_abs.2⟩
    -- hdiv tells us: (arg(z'/w') : Angle) = (arg z' : Angle) - (arg w' : Angle)
    -- Since arg(z'/w') ∈ (-π, π] (by definition of arg), and arg z' - arg w' ∈ (-π, π),
    -- and (arg z' : Angle) - (arg w' : Angle) = (arg z' - arg w' : Angle),
    -- we have (arg(z'/w') : Angle) = (arg z' - arg w' : Angle)
    -- Since both are in (-π, π], they must be equal as reals.
    have h_div_eq : (z' / w').arg = Complex.arg z' - Complex.arg w' := by
      have h_coe_eq := hdiv
      -- Convert the Real.Angle equality to a real equality
      -- Both sides are in (-π, π], so the coe is injective
      have h_div_in_Ioc : (z' / w').arg ∈ Set.Ioc (-Real.pi) Real.pi :=
        ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
      have h_diff_in_Ioc : Complex.arg z' - Complex.arg w' ∈ Set.Ioc (-Real.pi) Real.pi :=
        Set.Ioo_subset_Ioc_self h_in_Ioo
      -- Use that toReal ∘ coe = id on Ioc (-π, π]
      have h1 : Real.Angle.toReal (↑(z' / w').arg) = (z' / w').arg :=
        Real.Angle.toReal_coe_eq_self_iff.mpr h_div_in_Ioc
      have h2 : Real.Angle.toReal (↑(Complex.arg z' - Complex.arg w')) =
                Complex.arg z' - Complex.arg w' :=
        Real.Angle.toReal_coe_eq_self_iff.mpr h_diff_in_Ioc
      -- h_coe_eq: ↑(z'/w').arg = ↑z'.arg - ↑w'.arg
      -- Use coe_sub: ↑(a - b) = ↑a - ↑b, so ↑z'.arg - ↑w'.arg = ↑(z'.arg - w'.arg)
      rw [← Real.Angle.coe_sub] at h_coe_eq
      -- Now h_coe_eq: ↑(z'/w').arg = ↑(z'.arg - w'.arg)
      -- Apply toReal to both sides
      have h3 := congrArg Real.Angle.toReal h_coe_eq
      rw [h1, h2] at h3
      exact h3
    exact h_div_eq.symm

  -- Use the angle lemma from Mathlib: angle ≤ π/2 * chord, and π/2 < 2
  have h_angle : InnerProductGeometry.angle z' w' ≤ 2 * ‖z' - w'‖ := by
    have := Complex.angle_le_mul_norm_sub hz'_norm hw'_norm
    calc InnerProductGeometry.angle z' w' ≤ Real.pi / 2 * ‖z' - w'‖ := this
      _ ≤ 2 * ‖z' - w'‖ := by
          have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
          gcongr

  -- Bound ‖z' - w'‖ in terms of ‖z - w‖
  -- The bound ‖z/‖z‖ - w/‖w‖‖ ≤ ‖z - w‖ / min(‖z‖, ‖w‖) is exactly true.
  -- Proof via squared norms: ‖z' - w'‖² = 2(1 - cos θ) where θ is the angle,
  -- and ‖z - w‖² / min² = (a² + b² - 2ab·cos θ) / min² ≥ 2(1 - cos θ) when min ≤ max.
  have h_norm_diff : ‖z' - w'‖ ≤ ‖z - w‖ / min ‖z‖ ‖w‖ := by
    have hz_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    -- The key algebraic identity: ‖z*‖w‖ - w*‖z‖‖² = 2*‖z‖*‖w‖*(‖z‖*‖w‖ - Re(z*conj w))
    -- And: ‖z - w‖² = ‖z‖² + ‖w‖² - 2*Re(z*conj w)
    -- The inequality ‖z*‖w‖ - w*‖z‖‖² * min² ≤ ‖z - w‖² * ‖z‖² * ‖w‖² follows algebraically

    -- We'll prove the equivalent: ‖z' - w'‖² ≤ (‖z - w‖ / min)²
    -- which is: ‖z' - w'‖² * min² ≤ ‖z - w‖²
    have h_sq : ‖z' - w'‖^2 * (min ‖z‖ ‖w‖)^2 ≤ ‖z - w‖^2 := by
      -- Expand ‖z' - w'‖² = 2 - 2*Re(z'*conj(w')) = 2 - 2*Re(z*conj(w))/(‖z‖*‖w‖)
      have h_z'w' : z' * starRingEnd ℂ w' = (z * starRingEnd ℂ w) / ((‖z‖ : ℂ) * ‖w‖) := by
        simp only [z', w', div_mul_eq_mul_div, mul_div_assoc]
        rw [map_div₀, Complex.conj_ofReal]
        ring
      have h_norm_sq_z' : ‖z'‖^2 = 1 := by rw [hz'_norm]; ring
      have h_norm_sq_w' : ‖w'‖^2 = 1 := by rw [hw'_norm]; ring
      -- ‖z' - w'‖² = ‖z'‖² + ‖w'‖² - 2*Re(z'*conj(w')) = 2 - 2*Re(z'*conj(w'))
      -- First, compute Re(z' * conj w') using h_z'w'
      have h_re_prod : (z' * starRingEnd ℂ w').re = (z * starRingEnd ℂ w).re / (‖z‖ * ‖w‖) := by
        rw [h_z'w']
      -- Simplify (↑‖z‖ * ↑‖w‖) as a complex number with 0 imaginary part
        have h_prod_re : ((‖z‖ : ℂ) * ‖w‖).re = ‖z‖ * ‖w‖ := by simp
        have h_prod_im : ((‖z‖ : ℂ) * ‖w‖).im = 0 := by simp
        have h_prod_normSq : Complex.normSq ((‖z‖ : ℂ) * ‖w‖) = (‖z‖ * ‖w‖)^2 := by
          rw [← Complex.ofReal_mul, Complex.normSq_ofReal]; ring
        simp only [Complex.div_re, h_prod_re, h_prod_im, h_prod_normSq, mul_zero, add_zero]
        have h_sq_ne : (‖z‖ * ‖w‖)^2 ≠ 0 := by positivity
        field_simp [h_sq_ne]
        ring
      -- Use: ‖a - b‖² = ‖a‖² + ‖b‖² - 2*Re(a*conj(b)) for complex numbers
      have h_norm_sq : ∀ u v : ℂ, ‖u - v‖^2 = ‖u‖^2 + ‖v‖^2 - 2 * (u * starRingEnd ℂ v).re := by
        intro u v
        rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
      have h_expand : ‖z' - w'‖^2 = 2 - 2 * (z * starRingEnd ℂ w).re / (‖z‖ * ‖w‖) := by
        rw [h_norm_sq z' w', h_norm_sq_z', h_norm_sq_w', h_re_prod]
        ring
      -- ‖z - w‖² = ‖z‖² + ‖w‖² - 2*Re(z*conj(w))
      have h_expand2 : ‖z - w‖^2 = ‖z‖^2 + ‖w‖^2 - 2 * (z * starRingEnd ℂ w).re := by
        rw [h_norm_sq z w]
      rw [h_expand, h_expand2]
      have hc : (z * starRingEnd ℂ w).re ≤ ‖z‖ * ‖w‖ := by
        calc (z * starRingEnd ℂ w).re ≤ |(z * starRingEnd ℂ w).re| := le_abs_self _
          _ ≤ ‖z * starRingEnd ℂ w‖ := Complex.abs_re_le_norm _
          _ = ‖z‖ * ‖starRingEnd ℂ w‖ := norm_mul z _
          _ = ‖z‖ * ‖w‖ := by rw [RingHomIsometric.norm_map]
      have hc' : -(‖z‖ * ‖w‖) ≤ (z * starRingEnd ℂ w).re := by
        calc -(‖z‖ * ‖w‖) = -‖z * starRingEnd ℂ w‖ := by
              rw [norm_mul, RingHomIsometric.norm_map]
          _ ≤ (z * starRingEnd ℂ w).re := (abs_le.1 (Complex.abs_re_le_norm _)).1
      set c := (z * starRingEnd ℂ w).re with hc_def
      set a := ‖z‖ with ha
      set b := ‖w‖ with hb
      set m := min a b with hm
      have ha_pos : 0 < a := hz_norm_pos
      have hb_pos : 0 < b := hw_norm_pos
      have hab_pos : 0 < a * b := mul_pos ha_pos hb_pos
      have hm_pos : 0 < m := h_min_pos
      have hm_le_a : m ≤ a := min_le_left _ _
      have hm_le_b : m ≤ b := min_le_right _ _
      -- Goal: (2 - 2*c/(a*b)) * m² ≤ a² + b² - 2*c
      have h_goal : (2 - 2 * c / (a * b)) * m^2 ≤ a^2 + b^2 - 2 * c := by
        have hab_ne : a * b ≠ 0 := ne_of_gt hab_pos
        rw [sub_mul, div_mul_eq_mul_div, mul_comm 2 c, mul_div_assoc]
        rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
      -- 2*m² - (a² + b² - 2*c) ≤ 2*c*m²/(a*b)
      -- LHS = 2*m² - a² - b² + 2*c
      -- When c = a*b (aligned vectors), LHS = 2*m² - a² - b² + 2*a*b = 2*m² - (a-b)²
      -- Since m = min(a,b) ≤ (a+b)/2, we have m² ≤ ((a+b)/2)² = (a²+2ab+b²)/4
      -- And (a-b)² = a² - 2ab + b², so 2*m² - (a-b)² ≤ (a²+2ab+b²)/2 - (a²-2ab+b²) = 3ab - (a²+b²)/2
      -- This is getting complicated. Let me try nlinarith directly.
      -- The goal is: 2 * m² - (a² + b² - c*2) ≤ c * 2 * (m² / (a*b))
        have hm_sq_le_ab : m^2 ≤ a * b := by
          have h1 : m * m ≤ a * b := mul_le_mul hm_le_a hm_le_b (le_of_lt hm_pos) (le_of_lt ha_pos)
          simp only [sq]; exact h1
      -- Multiply through by a*b > 0 and rearrange
        have h_abc_nonneg : a * b - c ≥ 0 := by linarith [hc]
        have h_msq_nonpos : m^2 - a * b ≤ 0 := by linarith [hm_sq_le_ab]
        have h_lhs_nonpos : (m^2 - a * b) * (a * b - c) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h_msq_nonpos h_abc_nonneg
        have h_rhs_nonneg : 0 ≤ a * b * (a - b)^2 := by positivity
      -- The key: after multiplying by a*b, the inequality becomes polynomial
        have h_key : (2 * m^2 - (a^2 + b^2 - c * 2)) * (a * b) ≤ c * 2 * m^2 := by
          calc (2 * m^2 - (a^2 + b^2 - c * 2)) * (a * b)
              = c * 2 * m^2 + (2 * (m^2 - a * b) * (a * b - c) - a * b * (a - b)^2) := by ring
            _ ≤ c * 2 * m^2 + (0 - 0) := by linarith [h_lhs_nonpos, h_rhs_nonneg]
            _ = c * 2 * m^2 := by ring
      -- Convert back using division
        calc 2 * m^2 - (a^2 + b^2 - c * 2)
            ≤ c * 2 * m^2 / (a * b) := by
              rw [le_div_iff₀' hab_pos]
              convert h_key using 1
              ring
            _ = c * 2 * (m^2 / (a * b)) := by ring
      linarith [h_goal]
    -- From squared inequality: ‖z' - w'‖^2 * min^2 ≤ ‖z - w‖^2
    -- Derive: ‖z' - w'‖ ≤ ‖z - w‖ / min
    have h_min_sq_pos : 0 < (min ‖z‖ ‖w‖)^2 := sq_pos_of_pos h_min_pos
    have h_sq' : ‖z' - w'‖^2 ≤ (‖z - w‖ / min ‖z‖ ‖w‖)^2 := by
      rw [div_pow]
      rw [le_div_iff₀ h_min_sq_pos]
      exact h_sq
    have h_rhs_nn : 0 ≤ ‖z - w‖ / min ‖z‖ ‖w‖ := div_nonneg (norm_nonneg _) (le_of_lt h_min_pos)
    exact le_of_sq_le_sq h_sq' h_rhs_nn

  calc |Complex.arg z' - Complex.arg w'|
      = InnerProductGeometry.angle z' w' := h_arg_eq_angle
    _ ≤ 2 * ‖z' - w'‖ := h_angle
    _ ≤ 2 * (‖z - w‖ / min ‖z‖ ‖w‖) := by gcongr
    _ = 2 * ‖z - w‖ / min ‖z‖ ‖w‖ := by ring

/-- The p^n-th roots embed in p^(n+1)-th roots via the p-adic tower. -/
lemma p_tower_embedding (p : ℕ) (hp : 1 < p)
 (n : ℕ) [NeZero (p ^ n)] [NeZero (p ^ (n + 1))] (k : ZMod (p ^ n)) :
    character (p^n) k 1 = character (p^(n+1)) (p * k.val : ZMod (p^(n+1))) 1 := by
  -- Base case: n = 0 means both sides are exp(0) = 1
  by_cases hn : n = 0
  · subst hn
    -- Pattern: if z^1 = 1 (always true), then z^p witnesses the same at position p*0 = 0
    -- Both sides: character maps to exp(0) = 1
    have hk_val : k.val = 0 := by
      have : k.val < 1 := by simpa [pow_zero] using ZMod.val_lt k
      omega
    simp [character, hk_val, pow_zero, pow_one, ZMod.val_zero]
  -- n > 0 case: proceed with arithmetic
  have hp_pos : 0 < p := by linarith [hp]
  unfold character
  -- ensure `p` is positive for inequalities
  have hp_pos : 0 < p := by linarith [hp]
  -- `p * k.val < p^(n+1)` so `(p * k.val : ZMod (p^(n+1))).val = p * k.val`
  have hlt : p * k.val < p ^ (n + 1) := by
    calc
      p * k.val < p * (p ^ n) := by apply Nat.mul_lt_mul_of_pos_left (ZMod.val_lt k) hp_pos
      _ = p ^ n * p := by ring
      _ = p ^ (n + 1) := by rw [← pow_succ]
  have hmod : ((p * k.val : ℕ) : ZMod (p ^ (n + 1))).val = p * k.val := by
    rw [ZMod.val_natCast]; apply Nat.mod_eq_of_lt hlt
  -- compute product `↑p * k.cast` inside `ZMod (p^(n+1))` and show its `val` equals `p * k.val`
  have hmul_val : ((↑p : ZMod (p ^ (n + 1))) * (k.cast : ZMod (p ^ (n + 1)))).val = p * k.val := by
    -- Since n > 0, use modular arithmetic
    rw [ZMod.val_mul, ZMod.val_natCast]
    -- k.cast.val = k.val since k.val < p^n < p^(n+1)
    have hk_cast : (k.cast : ZMod (p ^ (n + 1))).val = k.val := by
      apply ZMod.val_cast_eq_val_of_lt
      have : p ^ n < p ^ (n + 1) := by
        have h_pow_pos : 0 < p ^ n := by
          apply Nat.zero_lt_of_lt
          calc 0 < 1 := by norm_num
            _ ≤ p ^ n := Nat.one_le_pow n p hp_pos
        calc p ^ n = p ^ n * 1 := by ring
          _ < p ^ n * p := Nat.mul_lt_mul_of_pos_left hp h_pow_pos
          _ = p ^ (n + 1) := by rw [← pow_succ]
      exact Nat.lt_trans (ZMod.val_lt k) this
    rw [hk_cast]
    -- p < p^(n+1) when n > 0, so p % p^(n+1) = p
    have hp_mod : p % p ^ (n + 1) = p := by
      apply Nat.mod_eq_of_lt
      have : 1 < p ^ n := by
        have h1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        calc 1 = p ^ 0 := by rw [pow_zero]
          _ < p ^ n := Nat.pow_lt_pow_right hp h1
      calc p = 1 * p := by ring
        _ < p ^ n * p := Nat.mul_lt_mul_of_pos_right this hp_pos
        _ = p ^ (n + 1) := by rw [← pow_succ]
    rw [hp_mod]
    exact Nat.mod_eq_of_lt hlt
  -- now prove equality of rational parameters in ℂ
  -- Need to show k.val * 1.val / p^n = (p * k.val).val * 1.val / p^(n+1)
  -- where (p * k.val) means the ZMod element (p * k.val : ZMod (p^(n+1)))
  congr 1
  push_cast
  -- Show (↑p * ↑k.val : ZMod (p^(n+1))).val = p * k.val using ZMod.val_mul
  have h_prod : ((↑p : ZMod (p ^ (n + 1))) * (↑k.val : ZMod (p ^ (n + 1)))).val = p * k.val := by
    rw [ZMod.val_mul, ZMod.val_natCast, ZMod.val_natCast]
    -- Since n > 0, both p and k.val are < p^(n+1), so their mods are themselves
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hp_lt : p < p ^ (n + 1) := by
      calc p = p ^ 1 := by rw [pow_one]
        _ < p ^ (n + 1) := Nat.pow_lt_pow_right hp (by omega : 1 < n + 1)
    rw [Nat.mod_eq_of_lt hp_lt]
    -- Need to show k.val < p^(n+1)
    have hpn_lt : p ^ n < p ^ (n + 1) := by
      simpa [pow_succ] using (Nat.pow_lt_pow_right hp (Nat.lt_succ_self n))
    have hk_lt : k.val < p ^ (n + 1) := Nat.lt_trans (ZMod.val_lt k) hpn_lt
    rw [Nat.mod_eq_of_lt hk_lt]
    exact Nat.mod_eq_of_lt hlt
  simp only [h_prod]
  -- For n > 0, p^n > 1, so (1 : ZMod (p^n)).val = 1
  have hval1_n : (ZMod.val (1 : ZMod (p ^ n))) = 1 := by
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have h1lt : 1 < p ^ n := by
      calc 1 < p := hp
        _ = p ^ 1 := by rw [pow_one]
        _ ≤ p ^ n := Nat.pow_le_pow_right (by linarith : 1 ≤ p) (by omega : 1 ≤ n)
    -- put the goal in the form simp knows: projection not function application
    change ((1 : ZMod (p ^ n))).val = 1
    -- (1 : ZMod m).val = 1 when 1 < m (with Fact instance)
    haveI : Fact (1 < p ^ n) := ⟨h1lt⟩
    rw [ZMod.val_one]
  -- Similarly for p^(n+1)
  have hval1_succ : (ZMod.val (1 : ZMod (p ^ (n + 1)))) = 1 := by
    have h1lt : 1 < p ^ (n + 1) := by
      calc 1 < p := hp
        _ = p ^ 1 := by rw [pow_one]
        _ ≤ p ^ (n + 1) := Nat.pow_le_pow_right (by linarith : 1 ≤ p) (by omega : 1 ≤ n + 1)
    change ((1 : ZMod (p ^ (n + 1)))).val = 1
    haveI : Fact (1 < p ^ (n + 1)) := ⟨h1lt⟩
    rw [ZMod.val_one]
  -- Rewrite the (ZMod.val 1) factors explicitly
  simp [hval1_n, hval1_succ, mul_assoc, mul_left_comm, mul_comm]
  have hp0c : (p : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp_pos)
  -- Turn ↑(p*k.val) into ↑p * ↑k.val and cancel p
  field_simp [hp0c]
  ring


/-- The n-th roots of unity are dense in S¹. -/
lemma roots_of_unity_dense (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n (_hn : n ≥ N) [NeZero n] (θ : ℝ),
    ∃ k : ZMod n, ‖exp (I * θ) - character n k 1‖ < ε := by
  -- Choose N > π/ε so that π/N < ε
  use Nat.ceil (π / ε) + 1
  intro n hn inst θ
  -- For any θ, find the closest n-th root of unity
  -- The roots are at angles 2πk/n for k = 0, 1, ..., n-1
  -- Choose k ≈ θn/(2π) rounded to nearest integer
  -- Since exp(I*θ) is 2π-periodic, we can work with θ directly
  -- Pick k so that 2πk/n is closest to θ (modulo 2π)
  let k_real := θ * (n : ℝ) / (2 * π)
  let k_rounded := ⌊k_real + 0.5⌋  -- Round to nearest integer
  use (k_rounded : ZMod n)
  -- Now show ‖exp(I*θ) - character n k 1‖ < ε
  -- Key: The angle difference is |θ - 2πk/n| ≤ π/n (nearest root)
  -- And ‖exp(I*α) - exp(I*β)‖ ≤ 2|sin((α-β)/2)| ≤ |α - β| for small differences
  -- First establish that n is large enough: π/n < ε
  have hn_large : (π : ℝ) / n < ε := by
    have h1 : (n : ℝ) > π / ε := by
      calc (n : ℝ) ≥ ⌈π / ε⌉₊ + 1 := by exact_mod_cast hn
           _ > π / ε := by
             have : ⌈π / ε⌉₊ ≥ π / ε := Nat.le_ceil (π / ε)
             linarith
    have hn_pos : 0 < (n : ℝ) := by
      have : 0 < n := NeZero.pos n
      exact_mod_cast this
    have : π < ε * (n : ℝ) := by
      calc π = (π / ε) * ε := by field_simp
           _ < (n : ℝ) * ε := by apply mul_lt_mul_of_pos_right h1 hε
           _ = ε * (n : ℝ) := mul_comm _ _
    calc π / (n : ℝ) < (ε * (n : ℝ)) / (n : ℝ) := by
           apply div_lt_div_of_pos_right this hn_pos
         _ = ε := by field_simp
  -- Step 1: Establish the rounding property |k_real - k_rounded| ≤ 1/2
  have h_round_bound : |k_real - k_rounded| ≤ 1 / 2 := by
    -- k_rounded = ⌊k_real + 0.5⌋, so k_rounded ≤ k_real + 0.5 < k_rounded + 1
    have h1 : (k_rounded : ℝ) ≤ k_real + 0.5 := Int.floor_le (k_real + 0.5)
    have h2 : k_real + 0.5 < (k_rounded : ℝ) + 1 := Int.lt_floor_add_one (k_real + 0.5)
    -- This gives k_rounded - 0.5 ≤ k_real < k_rounded + 0.5
    have : (k_rounded : ℝ) - 0.5 ≤ k_real ∧ k_real < (k_rounded : ℝ) + 0.5 := by
      constructor
      · linarith
      · linarith
    -- Therefore |k_real - k_rounded| ≤ 0.5
    rw [abs_sub_le_iff]
    constructor <;> linarith
  -- Step 2: Angle difference bound
  -- θ = 2π * k_real / n by definition of k_real
  -- So θ - 2π*k_rounded/n = 2π * (k_real - k_rounded) / n
  have h_angle_diff : |θ - 2 * π * ((k_rounded : ℝ) / (n : ℝ))| ≤ π / n := by
    have : θ - 2 * π * ((k_rounded : ℝ) / (n : ℝ)) =
           2 * π * (k_real - k_rounded) / (n : ℝ) := by
      unfold k_real
      have hn_ne : (n : ℝ) ≠ 0 := by
        have : 0 < n := NeZero.pos n
        exact_mod_cast (ne_of_gt this)
      field_simp [hn_ne]
    rw [this, abs_div, abs_mul, abs_mul]
    have : (2 : ℝ) = 2 := rfl
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [abs_of_pos Real.pi_pos]
    have hn_pos : 0 < (n : ℝ) := by
      have : 0 < n := NeZero.pos n
      exact_mod_cast this
    rw [abs_of_pos hn_pos]
    calc 2 * π * |k_real - k_rounded| / (n : ℝ)
        ≤ 2 * π * (1 / 2) / (n : ℝ) := by
          apply div_le_div_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left h_round_bound
            apply mul_nonneg
            · norm_num
            · exact Real.pi_pos.le
          · exact hn_pos.le
      _ = π / (n : ℝ) := by ring
  -- Step 3: Use character definition and exponential bound
  unfold character
  have hn_ge_2 : 2 ≤ n := by
    have h1 : 1 ≤ ⌈π / ε⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      have : 0 < π / ε := div_pos Real.pi_pos hε
      have : 0 < ⌈π / ε⌉₊ := Nat.ceil_pos.mpr this
      omega)
    have h2 : ⌈π / ε⌉₊ + 1 ≤ n := by exact_mod_cast hn
    omega
  haveI : Fact (1 < n) := ⟨by omega⟩
  rw [ZMod.val_one]
  push_cast
  simp only [mul_one]
  -- Key: exp(I*x) is 2π-periodic, so exp(2πI·k.val/n) = exp(2πI·k_rounded/n)
  -- because k.val ≡ k_rounded (mod n), so 2π·k.val/n and 2π·k_rounded/n differ by 2π·(integer)
  have h_char : Complex.exp (2 * ↑π * Complex.I * (↑((k_rounded : ZMod n).val) / ↑n)) =
                Complex.exp (2 * ↑π * Complex.I * ((k_rounded : ℝ) / ↑n)) := by
    -- Use periodicity: exp(2πi·z) has period 1
    -- Key: (k_rounded : ZMod n).val ≡ k_rounded (mod n), so they differ by an integer multiple of n
    -- Therefore exp(2πi·val/n) = exp(2πi·k_rounded/n) since exp(2πi·m) = 1 for integer m
    -- The key is: k_rounded = q*n + val for some integer q
    -- Write k_rounded = q*n + val, then k_rounded/n = q + val/n
    -- So exp(2πi·k_rounded/n) = exp(2πi·q + 2πi·val/n) = exp(2πi·q)·exp(2πi·val/n) = exp(2πi·val/n)
    -- By division: k_rounded = (k_rounded / n) * n + k_rounded % n
    have hdiv : k_rounded = (k_rounded / (n : ℤ)) * (n : ℤ) + k_rounded % (n : ℤ) := by
      have := (Int.mul_ediv_add_emod k_rounded n).symm
      rwa [mul_comm] at this
    -- The remainder k_rounded % n equals (k_rounded : ZMod n).val when viewed as integers
    have hmod_eq : k_rounded % (n : ℤ) = ((k_rounded : ZMod n).val : ℤ) := by
      -- ZMod.val_intCast says: ↑(↑k_rounded).val = k_rounded % n (both sides as integers)
      have := ZMod.val_intCast (n := n) k_rounded
      exact this.symm
    -- Now use this to rewrite k_rounded in terms of quotient and val
    rw [hmod_eq] at hdiv
    -- hdiv : k_rounded = (k_rounded / n) * n + (k_rounded : ZMod n).val
    -- Work directly with complex numbers to avoid nested coercion issues
    -- Use hdiv: k_rounded = (k_rounded / n) * n + val
    let q := k_rounded / (n : ℤ)  -- The quotient (an integer)
    let r := (k_rounded : ZMod n).val  -- The remainder (a natural number)
    -- The key equality in integers: k_rounded = q * n + r
    have hint : k_rounded = q * (n : ℤ) + (r : ℤ) := by
      change k_rounded = (k_rounded / (n : ℤ)) * (n : ℤ) + ((k_rounded : ZMod n).val : ℤ)
      exact hdiv
    -- Cast to reals and then complex
    have hcomplex : ((k_rounded : ℝ) : ℂ) = ((q : ℝ) : ℂ) * ((n : ℝ) : ℂ) + ((r : ℝ) : ℂ) := by
      have : (k_rounded : ℝ) = (q : ℝ) * (n : ℝ) + (r : ℝ) := by
        have := congr_arg (fun x : ℤ => (x : ℝ)) hint
        push_cast at this
        exact this
      push_cast
      exact_mod_cast this
    -- Now work with the exponential
    have hexp_eq : Complex.exp (2 * ↑π * Complex.I * (((k_rounded : ℝ) : ℂ) / ↑n)) =
                   Complex.exp (2 * ↑π * Complex.I * (((r : ℝ) : ℂ) / ↑n)) := by
      -- Rewrite using hcomplex: (k_rounded : ℂ) = (q : ℂ) * (n : ℂ) + (r : ℂ)
      have hn0 : (n : ℂ) ≠ 0 := by norm_cast; omega
      -- Simplify the division directly
      calc Complex.exp (2 * ↑π * Complex.I * (((k_rounded : ℝ) : ℂ) / ↑n))
          = Complex.exp (2 * ↑π * Complex.I *
           ((((q : ℝ) : ℂ) * ((n : ℝ) : ℂ) + ((r : ℝ) : ℂ)) / ↑n)) := by
              congr 1; congr 1
              rw [hcomplex]
        _ = Complex.exp (2 * ↑π * Complex.I * (((q : ℝ) : ℂ) + ((r : ℝ) : ℂ) / ↑n)) := by
              congr 1
              rw [add_div]
              simp [hn0]
        _ = Complex.exp (2 * ↑π * Complex.I *
         ((q : ℝ) : ℂ)) * Complex.exp (2 * ↑π * Complex.I * (((r : ℝ) : ℂ) / ↑n)) := by
              rw [mul_add, Complex.exp_add]
        _ = Complex.exp (2 * ↑π * Complex.I * (((r : ℝ) : ℂ) / ↑n)) := by
              -- Show exp(2πi·q) = 1 for integer q
              have hq_one : Complex.exp (2 * ↑π * Complex.I * ((q : ℝ) : ℂ)) = 1 := by
                push_cast
                convert Complex.exp_int_mul_two_pi_mul_I q using 2
                ring
              rw [hq_one, one_mul]
    -- Simplify the right hand side to match the goal
    convert hexp_eq.symm using 2 <;> push_cast
  -- Now use the bound ‖exp(I*θ) - exp(I*β)‖ ≤ |θ - β| via sin bound
  have h_norm_bound : ‖Complex.exp (Complex.I * θ) -
                        Complex.exp (2 * ↑π * Complex.I * (↑((k_rounded : ZMod n).val) / ↑n))‖
                      ≤ |θ - 2 * π * ((k_rounded : ℝ) / (n : ℝ))| := by
    -- First convert via h_char
    rw [h_char]
    -- Now apply the exponential bound
    have h_rewrite : Complex.exp (2 * ↑π * Complex.I * ((k_rounded : ℝ) / ↑n)) =
           Complex.exp (Complex.I * (2 * π * ((k_rounded : ℝ) / ↑n))) := by
      congr 1; ring
    rw [h_rewrite]
    convert norm_exp_I_sub_exp_I_le θ
     (2 * π * ((k_rounded : ℝ) / ↑n))
     using 2 <;> push_cast <;> ring
  -- Apply the bound chain
  calc ‖Complex.exp (Complex.I * θ)
   - Complex.exp (2 * ↑π * Complex.I * (↑((k_rounded : ZMod n).val) / ↑n))‖
      ≤ |θ - 2 * π * ((k_rounded : ℝ) / (n : ℝ))| := h_norm_bound
    _ ≤ π / n := h_angle_diff
    _ < ε := hn_large


/-- Conjugate pairs form an equivalence relation.

This is the ORBIT structure under complex conjugation! -/
def conjugate_pair_class (n : ℕ) [NeZero n] : ZMod n → ZMod n → Prop :=
  fun k k' => k' = k ∨ k' = -k

lemma conjugate_pair_equiv (n : ℕ) [NeZero n] :
    Equivalence (conjugate_pair_class n) := by
  constructor
  · -- reflexive
    intro k
    left; rfl
  · -- symmetric
    intro k k' h
    cases h with
    | inl h => rw [h]; left; rfl
    | inr h => rw [h]; right; simp
  · -- transitive
    intro k k' k'' hkk' hk'k''
    cases hkk' with
    | inl hkk' =>
      -- k' = k
      rw [← hkk']
      exact hk'k''
    | inr hkk' =>
      -- k' = -k
      cases hk'k'' with
      | inl hk'k'' =>
      -- k'' = k' = -k
        right
        rw [hk'k'', hkk']
      | inr hk'k'' =>
      -- k'' = -k' = -(-k) = k
        left
        rw [hk'k'', hkk']
        simp

/-- Map complex number to principal branch argument in (-π, π]. -/
noncomputable def principal_arg (z : ℂ) (_hz : z ≠ 0) : ℝ :=
  Complex.arg z  -- Lean's built-in gives principal branch

/-- Distance from π in principal branch.

This is the KEY pairing function! Conjugate pairs have the SAME distance. -/
noncomputable def dist_from_pi (z : ℂ) (hz : z ≠ 0) : ℝ :=
  |principal_arg z hz - π|


/-- Fundamental domain: representatives mod conjugation.

Each conjugate pair has ONE representative in [0, π].
This is the quotient U(1) / {±1}! -/
def fundamental_domain : Set ℂ :=
  {z | z ≠ 0 ∧ ‖z‖ = 1 ∧
   ∃ hz : z ≠ 0, 0 ≤ principal_arg z hz ∧ principal_arg z hz ≤ π}

/-- Every z on U(1) is conjugate to a unique element in the fundamental domain [0, π]. -/
theorem quotient_by_conjugation (z : ℂ) (hz_unit : ‖z‖ = 1) (hz_nonzero : z ≠ 0) :
    ∃ w : ℂ, w ∈ fundamental_domain ∧ (w = z ∨ w = conj z) ∧
    ∀ w' : ℂ, w' ∈ fundamental_domain → (w' = z ∨ w' = conj z) → w' = w := by
  -- If arg(z) ∈ [0, π], then w = z
  -- If arg(z) ∈ (-π, 0), then w = conj(z) has arg ∈ (0, π)
  -- Uniqueness: only one element per conjugate pair in [0, π]
  by_cases h : 0 ≤ Complex.arg z
  · -- z already in fundamental domain
    use z
    constructor
    · -- z ∈ fundamental_domain
      unfold fundamental_domain
      simp
      use hz_nonzero, hz_unit, hz_nonzero
      constructor
      · exact h
      · -- arg(z) ≤ π for any z (arg returns values in (-π, π])
        exact Complex.arg_le_pi z
    · constructor
      · left; rfl
      · intro w' hw'_fund hw'_conj
      -- w' is in fundamental domain and equals z or conj(z)
      -- Since z is in fundamental domain (arg ∈ [0, π]) and w' is too, w' must be z
        cases hw'_conj with
        | inl heq => exact heq  -- w' = z, done
        | inr heq =>
          rw [heq]
          -- If w' = conj(z) and both are in fundamental domain, then z = conj(z)
          -- This means arg(z) = 0 or arg(z) = π (i.e., z = ±1)
          -- Key: if both z and conj(z) are in [0,π], then z must be real (±1)
          -- For real z, conj(z) = z, so w' = conj(z) = z
          by_cases hpi : Complex.arg z = π
          · -- arg(z) = π means z = -1, and conj(-1) = -1
            have z_real : z.im = 0 := by
              -- arg = π and ‖z‖ = 1 means z = -1, which is real
              have : z = -1 := by
                -- arg = π characterizes negative real numbers
                have hre_neg : z.re < 0 := by
                  rw [Complex.arg_eq_pi_iff] at hpi
                  exact hpi.1
                have him_zero : z.im = 0 := by
                  rw [Complex.arg_eq_pi_iff] at hpi
                  exact hpi.2
                -- ‖z‖ = 1 means z.re^2 + z.im^2 = 1
                have hnorm_sq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
                  rw [Complex.sq_norm, Complex.normSq_apply]
                  ring
                rw [hz_unit, him_zero] at hnorm_sq
                simp at hnorm_sq
                -- So z.re^2 = 1, and since z.re < 0, we have z.re = -1
                have hre_sq : z.re ^ 2 = 1 := by linarith
                have hre_eq : z.re = -1 := by
                  have : z.re = 1 ∨ z.re = -1 := sq_eq_one_iff.mp hre_sq
                  cases this with
                  | inl h => linarith [hre_neg]
                  | inr h => exact h
                apply Complex.ext
                · simp [hre_eq]
                · simp [him_zero]
              rw [this]
              norm_num
            have conj_eq : conj z = z := by
              -- Real numbers equal their conjugate
              apply Complex.ext
              · simp [z_real]  -- re part
              · simp [z_real]  -- im part
            exact conj_eq
          · -- arg(z) ∈ [0,π) \ {π}, and arg(conj(z)) ∈ [0,π] implies arg(z) = 0
            have hconj_arg : Complex.arg (conj z) = -(Complex.arg z) := by
              have := Complex.arg_conj z
              simp [hpi] at this
              exact this
            have neg_arg_nonneg : -(Complex.arg z) ≥ 0 := by
              unfold fundamental_domain at hw'_fund
              simp at hw'_fund
              -- hw'_fund says: w' ≠ 0 ∧ ‖w'‖ = 1 ∧ ∃ hz,
              -- 0 ≤ principal_arg w' hz ∧ principal_arg w' hz ≤ π
              obtain ⟨hw'_nonzero, hw'_norm, hw'_hz, hw'_arg_pos, hw'_arg_le⟩ := hw'_fund
              -- principal_arg w' hw'_hz = arg w'
              have : principal_arg w' hw'_hz = Complex.arg w' := rfl
              rw [this] at hw'_arg_pos
              -- w' = conj z
              rw [heq, hconj_arg] at hw'_arg_pos
              exact hw'_arg_pos
            have harg_zero : Complex.arg z = 0 := by linarith [h]
            have z_real : z.im = 0 := by
              -- arg = 0 and ‖z‖ = 1 means z = 1, which is real
              have : z = 1 := by
                -- arg = 0 characterizes non-negative real numbers
                have hre_nonneg : 0 ≤ z.re := by
                  rw [Complex.arg_eq_zero_iff] at harg_zero
                  exact harg_zero.1
                have him_zero : z.im = 0 := by
                  rw [Complex.arg_eq_zero_iff] at harg_zero
                  exact harg_zero.2
                -- ‖z‖ = 1 means z.re^2 + z.im^2 = 1
                have hnorm_sq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
                  rw [Complex.sq_norm, Complex.normSq_apply]
                  ring
                rw [hz_unit, him_zero] at hnorm_sq
                simp at hnorm_sq
                -- So z.re^2 = 1, and since z.re ≥ 0, we have z.re = 1
                have hre_sq : z.re ^ 2 = 1 := by linarith
                have hre_eq : z.re = 1 := by
                  have : z.re = 1 ∨ z.re = -1 := sq_eq_one_iff.mp hre_sq
                  cases this with
                  | inl h => exact h
                  | inr h => linarith [hre_nonneg]
                apply Complex.ext
                · simp [hre_eq]
                · simp [him_zero]
              rw [this]
              norm_num
            have conj_eq : conj z = z := by
              -- Real numbers equal their conjugate
              apply Complex.ext
              · simp [z_real]  -- re part
              · simp [z_real]  -- im part
            exact conj_eq
  · -- conj(z) in fundamental domain
    use conj z
    constructor
    · unfold fundamental_domain
      -- Need: conj(z) ≠ 0, ‖conj(z)‖ = 1, and arg(conj(z)) ∈ [0, π]
      constructor
      · -- conj(z) ≠ 0
        exact star_ne_zero.mpr hz_nonzero
      constructor
      · -- ‖conj(z)‖ = 1
        rw [norm_conj]
        exact hz_unit
      · -- ∃ hz : conj z ≠ 0, 0 ≤ principal_arg (conj z) hz ∧ principal_arg (conj z) hz ≤ π
        use star_ne_zero.mpr hz_nonzero
        constructor
        · -- 0 ≤ arg(conj(z))
          -- principal_arg is defined as Complex.arg
          show 0 ≤ Complex.arg (conj z)
          -- For z ≠ 0, arg(conj(z)) = -arg(z) when arg(z) ≠ π
          -- Since h says ¬(0 ≤ arg(z)), we have arg(z) < 0
          -- So arg(z) ∈ (-π, 0), thus -arg(z) ∈ (0, π)
          have : Complex.arg (conj z) = -(Complex.arg z) := by
            have := Complex.arg_conj z
            -- Since arg(z) < 0, we have arg(z) ≠ π
            have hneq : Complex.arg z ≠ π := by
              have : Complex.arg z < 0 := by linarith [h]
              linarith [Real.pi_pos]
            simp [hneq] at this
            exact this
          rw [this]
          linarith [Complex.neg_pi_lt_arg z]
        · -- arg(conj(z)) ≤ π
          show Complex.arg (conj z) ≤ π
          exact Complex.arg_le_pi (conj z)
    · constructor
      · right; rfl
      · intro w' hw'_fund hw'_conj
      -- w' is in fundamental domain and equals z or conj(z)
      -- Since conj(z) is in fundamental domain and w' is too, w' must be conj(z)
        cases hw'_conj with
        | inl heq =>
          -- w' = z, but this contradicts arg(z) < 0 and w' in fundamental domain
          -- If w' = z and w' ∈ fundamental_domain, then 0 ≤ arg(z)
          exfalso
          unfold fundamental_domain at hw'_fund
          obtain ⟨_, _, hw_hz, hw_arg_pos, _⟩ := hw'_fund
          have : principal_arg w' hw_hz = Complex.arg w' := rfl
          rw [this, heq] at hw_arg_pos
          -- Now hw_arg_pos says 0 ≤ arg(z), but h says ¬(0 ≤ arg(z))
          exact h hw_arg_pos
        | inr heq => exact heq  -- w' = conj(z), done

/-! ### Profinite Calculus on the Circle -/

/-- Nearest character approximation at level p^n. -/
noncomputable def nearest_character_index (p n : ℕ) [NeZero (p ^ n)] (θ : ℝ) : ZMod (p ^ n) :=
  -- Scale by p^n/π to get k ∈ [0, 2p^n), working in doubled quotient Z/(2p^n)Z
  let k : ℤ := Int.floor (θ * (p ^ n : ℝ) / Real.pi)
  -- Evens (k = 2j): round down to j = k/2
  -- Odds (k = 2j+1): round up to j+1 = (k+1)/2
  let j : ℤ := if k % 2 = 0 then k / 2 else (k + 1) / 2
  (j : ZMod (p ^ n))

/-- The angle corresponding to the nearest character grid point at level p^n. -/
noncomputable def charAngle (p n : ℕ) [NeZero (p ^ n)] (θ : ℝ) : ℝ :=
  2 * Real.pi * ((nearest_character_index p n θ).val : ℝ) / (p ^ n : ℝ)

/-- The nearest grid point is within π/p^n of θ. -/
lemma charAngle_approximation_bound (p n : ℕ) [NeZero (p ^ n)] (θ : ℝ) :
    ∃ k : ℤ, |charAngle p n θ - θ - 2 * Real.pi * k| ≤ Real.pi / p ^ n := by
  -- Define the key quantities
  let s := θ * (p ^ n : ℝ) / (2 * Real.pi)  -- scaled angle
  let k_raw := Int.floor (θ * (p ^ n : ℝ) / Real.pi)  -- = floor(2s)
  let j : ℤ := if k_raw % 2 = 0 then k_raw / 2 else (k_raw + 1) / 2  -- nearest integer to s
  let j_val := (nearest_character_index p n θ).val  -- in [0, p^n)

  -- Key fact: j_val is the ZMod representative of j
  have hj_def : (j : ZMod (p ^ n)) = nearest_character_index p n θ := by
    simp only [nearest_character_index, j, k_raw]

  -- Positivity facts
  have hpn_nat_pos : 0 < (p ^ n : ℕ) := Nat.pos_of_ne_zero (NeZero.ne (p ^ n))
  have hpn_pos : (0 : ℝ) < (p : ℝ) ^ n := by
    rw [← Nat.cast_pow]
    exact Nat.cast_pos.mpr hpn_nat_pos
  have hpn_ne : (p : ℝ) ^ n ≠ 0 := ne_of_gt hpn_pos
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have h2pi_ne : 2 * Real.pi ≠ 0 := h2pi_pos.ne'

  -- Key observation: k_raw = floor(2s)
  have hk_eq : k_raw = Int.floor (2 * s) := by
    simp only [k_raw, s]
    congr 1
    field_simp

  -- From floor properties: k_raw ≤ 2s < k_raw + 1
  have hk_le : (k_raw : ℝ) ≤ 2 * s := by rw [hk_eq]; exact Int.floor_le _
  have hk_lt : 2 * s < k_raw + 1 := by rw [hk_eq]; exact Int.lt_floor_add_one _

  -- The doubled quotient formula gives |j - s| ≤ 1/2
  have h_round : |j - s| ≤ 1/2 := by
    by_cases heven : k_raw % 2 = 0
    · -- k_raw even: k_raw = 2m, j = k_raw/2 = m
      simp only [j, heven, ite_true]
      have hdiv : (2 : ℤ) ∣ k_raw := Int.dvd_of_emod_eq_zero heven
      obtain ⟨m, hkm⟩ := hdiv
      have hj_eq : k_raw / 2 = m := by rw [hkm]; simp [Int.mul_ediv_cancel_left]
      rw [hj_eq]
      -- From hkm: k_raw = 2 * m, so (k_raw : ℝ) = 2 * m
      have hkm_real : (k_raw : ℝ) = 2 * (m : ℝ) := by
        have : (k_raw : ℤ) = 2 * m := hkm
        exact_mod_cast this
      -- Now: 2m ≤ 2s < 2m+1, so m ≤ s < m + 1/2
      have h1 : (m : ℝ) ≤ s := by
        have h2ms : 2 * (m : ℝ) ≤ 2 * s := by rw [← hkm_real]; exact hk_le
        linarith
      have h2 : s < (m : ℝ) + 1/2 := by
        have h2ms : 2 * s < 2 * (m : ℝ) + 1 := by rw [← hkm_real]; exact hk_lt
        linarith
      rw [abs_le]
      constructor <;> linarith
    · -- k_raw odd: k_raw = 2m-1, j = (k_raw+1)/2 = m
      simp only [j, heven, ite_false]
      have hdiv : (2 : ℤ) ∣ (k_raw + 1) := by
        rw [Int.dvd_iff_emod_eq_zero]
        have := Int.emod_two_eq_zero_or_one k_raw
        omega
      obtain ⟨m, hkm⟩ := hdiv
      have hj_eq : (k_raw + 1) / 2 = m := by rw [hkm]; simp [Int.mul_ediv_cancel_left]
      rw [hj_eq]
      -- From hkm: k_raw + 1 = 2 * m, so k_raw = 2*m - 1
      have hkm_real : (k_raw : ℝ) = 2 * (m : ℝ) - 1 := by
        have : (k_raw : ℤ) + 1 = 2 * m := hkm
        have : (k_raw : ℤ) = 2 * m - 1 := by linarith
        exact_mod_cast this
      -- Now: 2m-1 ≤ 2s < 2m, so m - 1/2 ≤ s < m
      have h1 : (m : ℝ) - 1/2 ≤ s := by
        have h2ms : 2 * (m : ℝ) - 1 ≤ 2 * s := by rw [← hkm_real]; exact hk_le
        linarith
      have h2 : s < (m : ℝ) := by
        have h2ms : 2 * s < 2 * (m : ℝ) := by
          have : 2 * s < (k_raw : ℝ) + 1 := hk_lt
          linarith [hkm_real]
        linarith
      rw [abs_le]
      constructor <;> linarith

  -- Connect j_val back to j via ZMod
  have hj_val_mod : (j_val : ℤ) = j % (p ^ n : ℕ) := by
    have h1 : (j_val : ℤ) = ((j : ZMod (p ^ n)).val : ℤ) := by
      simp only [j_val, hj_def]
    rw [h1, ZMod.val_intCast]

  -- Therefore j = j_val + m * p^n
  let m : ℤ := j / (p ^ n : ℕ)
  use -m

  -- Key identity: j = (j % p^n) + p^n * (j / p^n) = j_val + p^n * m
  have hj_eq_val : (j : ℝ) = (j_val : ℝ) + (m : ℝ) * ((p : ℝ) ^ n) := by
    have h_jval : j % (p ^ n : ℕ) = (j_val : ℤ) := hj_val_mod.symm
    -- j = j_val + p^n * m directly from Int.emod_add_ediv
    have h_int_eq : j = (j_val : ℤ) + (p ^ n : ℕ) * m := by
      have := Int.emod_add_mul_ediv j (p ^ n : ℕ)
      simp only [h_jval] at this
      linarith
    calc (j : ℝ) = ((j_val : ℤ) + (p ^ n : ℕ) * m : ℤ) := by exact_mod_cast h_int_eq
      _ = (j_val : ℝ) + (m : ℝ) * ((p : ℝ) ^ n) := by push_cast; ring

  -- charAngle = 2π * j_val / p^n by definition
  have h_charAngle : charAngle p n θ = 2 * Real.pi * j_val / (p : ℝ) ^ n := rfl

  -- θ = 2π * s / p^n by definition of s
  have h_theta : θ = 2 * Real.pi * s / (p : ℝ) ^ n := by
    simp only [s]
    field_simp

  -- The key algebraic identity for the calculation
  have h_alg : (j_val : ℝ) - s + m * (p : ℝ) ^ n = (j : ℝ) - s := by
    linarith [hj_eq_val]

  -- Now compute the bound
  have h_expr : |charAngle p n θ - θ - 2 * Real.pi * ((-m : ℤ) : ℝ)| =
      2 * Real.pi / (p : ℝ) ^ n * |j - s| := by
    simp only [Int.cast_neg]
    rw [h_charAngle, h_theta]
    have h1 : 2 * Real.pi * ↑j_val / (p : ℝ) ^ n - 2 * Real.pi * s / (p : ℝ) ^ n - 2 * Real.pi * -↑m =
        2 * Real.pi / (p : ℝ) ^ n * ((j_val : ℝ) - s + m * (p : ℝ) ^ n) := by field_simp; ring
    rw [h1, h_alg, abs_mul, abs_of_pos (div_pos h2pi_pos hpn_pos)]
  calc |charAngle p n θ - θ - 2 * Real.pi * ((-m : ℤ) : ℝ)|
      = 2 * Real.pi / (p : ℝ) ^ n * |j - s| := h_expr
      _ ≤ 2 * Real.pi / (p : ℝ) ^ n * (1/2) := by
          apply mul_le_mul_of_nonneg_left h_round
          exact le_of_lt (div_pos h2pi_pos hpn_pos)
      _ = Real.pi / (p : ℝ) ^ n := by ring

/-- Helper: n ≤ 2^n for all natural numbers. -/
lemma nat_le_two_pow (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [Nat.cast_succ, pow_succ]
    have h2m : (1 : ℝ) ≤ 2^m := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    calc (m : ℝ) + 1 ≤ 2^m + 1 := by linarith
      _ ≤ 2^m + 2^m := by linarith
      _ = 2^m * 2 := by ring

/-- Helper: n < 2^n for n ≥ 1. -/
private lemma nat_lt_two_pow (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) < 2 ^ n := by
  induction n with
  | zero => simp at hn
  | succ m ih =>
    simp only [Nat.cast_succ, pow_succ]
    by_cases hm : m = 0
    · simp [hm]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have h2m : (1 : ℝ) ≤ 2^m := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      calc (m : ℝ) + 1 < 2^m + 1 := by linarith [ih hm1]
        _ ≤ 2^m + 2^m := by linarith
        _ = 2^m * 2 := by ring

/-- Corollary: For large n, charAngle is within any ε of θ (on the circle). -/
lemma charAngle_eventually_close (p : ℕ) [Fact (Nat.Prime p)] (θ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, [NeZero (p^n)] → ∃ k : ℤ, |charAngle p n θ - θ - 2 * Real.pi * k| < ε := by
  -- Choose N such that π/p^N < ε
  -- Since p ≥ 2, p^n → ∞, so such N exists
  have hp : 1 < p := Nat.Prime.one_lt (Fact.elim inferInstance)
  have hp_pos : 0 < p := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_of_lt hp)
  -- Use Archimedean property: exists N with p^N > π/ε
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.pi / ε)
  use N
  intro n hn _
  obtain ⟨k, hk⟩ := charAngle_approximation_bound p n θ
  use k
  -- Key: p^n ≥ p^N > N > π/ε, so π/p^n < ε
  have hN_pos : (0 : ℝ) < N := by
    have : Real.pi / ε < N := hN
    have hpi : 0 < Real.pi := Real.pi_pos
    have hεi : 0 < ε := hε
    have : 0 < Real.pi / ε := div_pos hpi hεi
    linarith
  have hN_ge1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    have : N = 0 := Nat.lt_one_iff.mp h
    simp [this] at hN_pos
  have hpN_gt : (N : ℝ) < p ^ N := by
    have h2p : (2 : ℝ) ≤ p := by
      have : 2 ≤ p := hp
      exact Nat.cast_le.mpr this
    calc (N : ℝ) < 2 ^ N := nat_lt_two_pow N hN_ge1
      _ ≤ p ^ N := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2p N
  have hpn_pos : (0 : ℝ) < p ^ n := by positivity
  have hpN_pos : (0 : ℝ) < p ^ N := by positivity
  have hp_ge1 : (1 : ℝ) ≤ (p : ℝ) := by
    have h1p : 1 ≤ p := Nat.one_le_of_lt hp
    exact_mod_cast h1p
  have hpn_ge_pN : (p : ℝ) ^ N ≤ (p : ℝ) ^ n := by
    apply pow_le_pow_right₀ hp_ge1 hn
  calc |charAngle p n θ - θ - 2 * Real.pi * k|
      ≤ Real.pi / (p : ℝ) ^ n := hk
    _ ≤ Real.pi / (p : ℝ) ^ N := by
        apply div_le_div_of_nonneg_left Real.pi_nonneg hpN_pos hpn_ge_pN
    _ < Real.pi / (N : ℝ) := by
        exact div_lt_div_of_pos_left Real.pi_pos hN_pos hpN_gt
    _ < ε := by
        have hπε : Real.pi / ε < N := hN
        have hε_pos : 0 < ε := hε
        have hπ : 0 < Real.pi := Real.pi_pos
      -- From π/ε < N and ε > 0, we get π < N * ε, so π/N < ε
        have h1 : Real.pi < N * ε := by
          calc Real.pi = (Real.pi / ε) * ε := by field_simp
            _ < N * ε := by nlinarith
        calc Real.pi / N < (N * ε) / N := by
              apply div_lt_div_of_pos_right h1 hN_pos
          _ = ε := by field_simp

/-- PROFINITE CONTINUITY via character approximation. -/
def IsProfiniteContinuousAt (f : ℝ → ℂ) (a : ℝ) (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ θ : ℝ,
    |θ - a| < δ →
    let char_val := charAngle p n θ
    (‖f θ - f char_val‖ < ε / 2) ∧ (‖f char_val - f a‖ < ε / 2)


/-- Isomorphism Lemma: Doubled quotient rounding ≅ Standard rounding. -/
lemma doubled_quotient_eq_standard_rounding (p n : ℕ) [NeZero (p ^ n)] (θ : ℝ) :
    let s := θ * (p ^ n : ℝ) / (2 * Real.pi)
    let k := Int.floor (θ * (p ^ n : ℝ) / Real.pi)
    let j_doubled := if k % 2 = 0 then k / 2 else (k + 1) / 2
    let j_standard := Int.floor (s + 1/2)
    j_doubled = j_standard := by
  intro s k j_doubled j_standard
  -- Key observation: k = floor(2s)
  have hk_eq : k = Int.floor (2 * s) := by
    simp only [s, k]
    congr 1; ring
  -- Use floor properties to relate k and s
  have hk_le : (k : ℝ) ≤ 2 * s := by rw [hk_eq]; exact Int.floor_le _
  have hk_lt : 2 * s < (k : ℝ) + 1 := by rw [hk_eq]; exact Int.lt_floor_add_one _
  by_cases hk : k % 2 = 0
  · -- k even: k = 2m, so 2m ≤ 2s < 2m+1, hence m ≤ s < m+1/2, so floor(s+1/2) = m
    simp only [j_doubled, hk, ite_true]
    -- Use divisibility to get k = 2*m for some m
    have hk2 : (2 : ℤ) ∣ k := Int.dvd_of_emod_eq_zero hk
    obtain ⟨m, hkm⟩ := hk2
    -- Show k/2 = m
    have hk_div : k / 2 = m := by
      rw [hkm]
      simp [Int.mul_ediv_cancel_left]
    -- Rewrite goal and hypotheses using k = 2*m
    rw [hk_div]
    symm
    rw [Int.floor_eq_iff]
    constructor
    · -- Show m ≤ s + 1/2
      -- From k = 2*m and k ≤ 2*s, we get 2*m ≤ 2*s, so m ≤ s
      have : (m : ℝ) ≤ s := by
        have h2m : (2 * m : ℝ) ≤ 2 * s := by
          calc (2 * m : ℝ) = (k : ℝ) := by norm_cast; exact hkm.symm
            _ ≤ 2 * s := hk_le
        linarith
      linarith
    · -- Show s + 1/2 < m + 1
      -- From k = 2*m and 2*s < k+1, we get 2*s < 2*m+1, so s < m + 1/2
      have : s < (m : ℝ) + 1/2 := by
        have h2m : 2 * s < (2 * m : ℝ) + 1 := by
          calc 2 * s < (k : ℝ) + 1 := hk_lt
            _ = (2 * m : ℝ) + 1 := by norm_cast; rw [hkm]
        linarith
      linarith
  · -- k odd: k = 2m+1, so 2m+1 ≤ 2s < 2m+2, hence m+1/2 ≤ s < m+1, so floor(s+1/2) = m+1
    simp only [j_doubled, hk, ite_false]
    -- k is odd, so k % 2 = 1
    have hk_odd : k % 2 = 1 := by
      have := Int.emod_two_eq_zero_or_one k
      omega
    -- Therefore k+1 is even
    have hk2 : (2 : ℤ) ∣ (k + 1) := by
      rw [Int.dvd_iff_emod_eq_zero]
      omega
    obtain ⟨m, hkm⟩ := hk2
    -- Show (k+1)/2 = m
    have hk_div : (k + 1) / 2 = m := by
      rw [hkm]
      simp [Int.mul_ediv_cancel_left]
    -- Rewrite goal and hypotheses using k+1 = 2*m
    rw [hk_div]
    symm
    rw [Int.floor_eq_iff]
    constructor
    · -- Show m ≤ s + 1/2
      -- From k+1 = 2*m and k ≤ 2*s, we get 2*m ≤ 2*s+1, so m ≤ s + 1/2
      have : (m : ℝ) ≤ s + 1/2 := by
        have h2m : (2 * m : ℝ) = (k : ℝ) + 1 := by norm_cast; rw [hkm]
        linarith [hk_le]
      exact this
    · -- Show s + 1/2 < m + 1
      -- From k+1 = 2*m and 2*s < k+1, we get 2*s < 2*m, so s < m
      have : s + 1/2 < (m : ℝ) + 1 := by
        have h2m : (2 * m : ℝ) = (k : ℝ) + 1 := by norm_cast; rw [hkm]
        linarith [hk_lt]
      exact this

/-- Equivalence Theorem: Profinite continuity → Classical continuity -/
theorem continuous_if_profinitecontinuous_at (f : ℝ → ℂ) (a : ℝ) (p : ℕ) [Fact (Nat.Prime p)] :
    IsProfiniteContinuousAt f a p →  ContinuousAt f a := by
  -- IsProfiniteContinuousAt → ContinuousAt
  -- With the two-inequality definition, this is pure triangle inequality
  intro h_prof
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, N, h_prof_δ⟩ := h_prof ε hε
  use δ, hδ
  intro θ hθ_close
  -- Convert |θ - a| to dist for consistency
  have hθ_dist : dist θ a < δ := by simpa [Real.dist_eq] using hθ_close
  -- Get both inequalities from profinite continuity
  obtain ⟨h1, h2⟩ := h_prof_δ N (le_refl N) θ hθ_close
  -- Triangle inequality: dist(f θ, f a) ≤ dist(f θ, f char_θ) + dist(f char_θ, f a)
  calc dist (f θ) (f a)
      ≤ dist (f θ) (f (charAngle p N θ)) + dist (f (charAngle p N θ)) (f a) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · -- dist (f θ) (f char_θ) = ‖f θ - f char_θ‖
          rw [dist_eq_norm]
          exact h1
        · -- dist (f char_θ) (f a) = ‖f char_θ - f a‖
          rw [dist_eq_norm]
          exact h2
    _ = ε := by ring

/-! ### Positive-Definiteness via the Profinite Tower -/

/-- PROFINITE POSITIVE-DEFINITENESS -/
def IsPositiveDefiniteProfinite (f : ℤ → ℂ) (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ n : ℕ, ∀ [NeZero (p ^ n)],
    -- Restrict f to ℤ/(p^n)ℤ
    let f_n : ZMod (p ^ n) → ℂ := fun k => f k.val
    IsPositiveDefiniteFinite (p ^ n) f_n


/-! ### Conjugate Invariance and Riesz Representation -/

/-- CONJUGATE INVARIANCE OF POSITIVE-DEFINITE FUNCTIONS

If f is positive-definite, it satisfies f(x) = conj(f(-x)).
This is the key symmetry that forces the Riesz measure to live on the quotient! -/
lemma pos_def_conjugate_invariant {f : ℝ → ℂ} (hf : IsPositiveDefinite f) (x : ℝ) :
    f x = conj (f (-x)) := by
  have h := hf.1 (-x)
  rw [neg_neg] at h
  exact h


/-- CHARACTER ADDITIVITY - The core algebraic property.

The exponents differ by an integer (due to ZMod overflow), but exp kills it via periodicity! -/
lemma character_add (N : ℕ) [NeZero N] (k m a : ZMod N) :
    character N k (m + a) = character N k m * character N k a := by
  unfold character
  simp only [ZMod.val_add]
  by_cases h : m.val + a.val < N
  · -- No overflow: just exp(x+y) = exp(x)*exp(y)
    rw [Nat.mod_eq_of_lt h, ← Complex.exp_add]
    congr 1; push_cast; ring
  · -- Overflow: exponents differ by -2πi·k.val, but exp(-2πi·k.val) = 1
    have hge : m.val + a.val ≥ N := by omega
    have hm : m.val < N := ZMod.val_lt m
    have ha : a.val < N := ZMod.val_lt a
    have hlt : m.val + a.val - N < N := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt, Nat.cast_sub hge, ← Complex.exp_add]
    push_cast
    -- Goal: exp(2πi·k·(m+a-N)/N) = exp(2πi·k·m/N + 2πi·k·a/N)
    -- LHS = exp(2πi·k·(m+a)/N - 2πi·k) = exp(2πi·k·(m+a)/N) * exp(-2πi·k) = RHS * 1
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    rw [show (2 : ℂ) * ↑π * I * ((↑k.val * (↑m.val + ↑a.val - ↑N) / ↑N : ℂ)) =
             (2 : ℂ) * ↑π * I * ((↑k.val * ↑m.val / ↑N : ℂ)) +
             (2 : ℂ) * ↑π * I * ((↑k.val * ↑a.val / ↑N : ℂ)) +
             (-(k.val : ℤ)) * ((2 : ℂ) * ↑π * I) by
      field_simp [hN]
      ring_nf
      simp [mul_comm]]
    rw [Complex.exp_add, Complex.exp_add]
    -- After exp_add: goal is exp(...) * exp(...) * exp(period) = exp(...) * exp(...)
    -- The third term is exp(-↑↑k.val * 2πi) = exp(-(k.val : ℤ) * 2πi) = 1
    conv_rhs => rw [← mul_one (cexp _ * cexp _)]
    congr 1
    -- Goal: cexp(-↑↑k.val * (2 * ↑π * I)) = 1
    convert Complex.exp_int_mul_two_pi_mul_I (-(k.val : ℤ)) using 1
    push_cast
    ring

/-- Character Subtraction Formula: char_k(i-j) = char_k(i) * conj(char_k(j))

This is the KEY identity for bochner_finite Sorry 4!
Shows how characters transform differences into products. -/
lemma character_sub_eq_mul (n : ℕ) [NeZero n] (k i j : ZMod n) :
    character n k (i - j) = character n k i * conj (character n k j) := by
  calc
    character n k (i - j)
        = character n k (i + (-j)) := by simp [sub_eq_add_neg]
    _   = character n k i * character n k (-j) := by
          simpa using (character_add (N := n) k i (-j))
    _   = character n k i * conj (character n k j) := by
          simp [character_arg_conjugate]

/-- CONNECTION TO MATHLIB's AddChar

Our `character N k` is an additive character (ZMod N → ℂ).
This wrapper lets us use ALL of mathlib's character theory! -/
noncomputable def character_asAddChar (N : ℕ) [NeZero N] (k : ZMod N) : AddChar (ZMod N) ℂ where
  toFun := character N k
  map_zero_eq_one' := by simp [character, ZMod.val_zero]
  map_add_eq_mul' := character_add N k

/-- NONTRIVIAL CHARACTER - χ_k(1) ≠ 1 when k ≠ 0

A character is nontrivial (≠ 1 everywhere) iff k ≠ 0.
This uses: exp(z) = 1 ⟺ z = 2πi·n for some integer n -/
lemma character_one_ne_one_of_ne_zero (N : ℕ) [NeZero N] (k : ZMod N) (hk : k ≠ 0) :
    character N k 1 ≠ 1 := by
  intro h
  unfold character at h
  -- Use Complex.exp_eq_one_iff: exp(z) = 1 ⟺ ∃ t : ℤ, z = 2πi·t
  rw [Complex.exp_eq_one_iff] at h
  rcases h with ⟨t, ht⟩
  -- We have: 2πi·(k.val·1)/N = 2πi·t
  -- Cancel 2πi and simplify to get: k.val/N = t
  have h_simp : (k.val : ℝ) / (N : ℝ) = t := by
    -- From ht: 2πi·(k.val·(1:ZMod N).val/N) = 2πi·t
    -- We have (1:ZMod N).val ∈ [0,N), and equals 1 mod N
    -- Since k ≠ 0, we know N > 1 (otherwise ZMod 1 = {0})
    have hN_gt_one : 1 < N := by
      by_contra h_not
      push_neg at h_not
      interval_cases N
      · exact NeZero.ne 0 rfl
      · -- N = 1 case: ZMod 1 has only element 0, contradicting k ≠ 0
        have : k = 0 := Subsingleton.elim k 0
        exact hk this
    -- Now (1:ZMod N).val = 1 (provide Fact instance)
    haveI : Fact (1 < N) := ⟨hN_gt_one⟩
    have h1 : (1 : ZMod N).val = 1 := ZMod.val_one (n := N)
    -- From ht: 2πi·(k.val·1/N) = 2πi·t
    simp only [h1, Nat.cast_one, mul_one] at ht
    -- Cancel 2πi
    have h2πi : (2 : ℂ) * ↑π * I ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have h_complex : (↑k.val / ↑N : ℂ) = ↑t := by field_simp [h2πi] at ht; exact ht
    -- Extract real parts from both sides
    have h_re : (↑k.val / ↑N : ℂ).re = (↑t : ℂ).re := congrArg Complex.re h_complex
    -- Simplify right side: (↑t : ℂ).re = t
    rw [Complex.intCast_re] at h_re
    -- Simplify left side: (↑k.val / ↑N : ℂ).re = (k.val : ℝ) / (N : ℝ)
    have h_lhs : (↑k.val / ↑N : ℂ).re = (k.val : ℝ) / (N : ℝ) := by
      rw [Complex.div_natCast_re, Complex.natCast_re]
    rw [h_lhs] at h_re
    exact h_re
  -- But 0 < k.val < N and k ≠ 0, so k.val/N ∈ (0,1), which can't equal integer t
  have hkval : 0 < k.val ∧ k.val < N := by
    constructor
    · have : k.val ≠ 0 := by
        intro h0
        apply hk
        simpa [ZMod.val_eq_zero] using h0
      omega
    · exact ZMod.val_lt k
  -- Contradiction: t ∈ ℤ but k.val/N ∈ (0,1)
  have h_bounds : 0 < (k.val : ℝ) / (N : ℝ) ∧ (k.val : ℝ) / (N : ℝ) < 1 := by
    have hk_pos : (0 : ℝ) < (k.val : ℝ) := Nat.cast_pos.mpr hkval.1
    have hN_pos : (0 : ℝ) < (N : ℝ) := by
      have : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      exact Nat.cast_pos.mpr this
    have hk_lt_N : (k.val : ℝ) < (N : ℝ) := Nat.cast_lt.mpr hkval.2
    constructor
    · exact div_pos hk_pos hN_pos
    · rw [div_lt_one hN_pos]
      exact hk_lt_N
  rw [h_simp] at h_bounds
  -- t is an integer with 0 < t < 1, which is impossible
  -- Convert real inequalities to integer inequalities
  have ht_pos : 0 < t := Int.cast_pos.mp h_bounds.1
  have ht_lt_one : t < 1 := by
    have : (t : ℝ) < ((1 : ℤ) : ℝ) := by norm_num; exact h_bounds.2
    exact Int.cast_lt.mp this
  omega

/-- Sum of nontrivial character is zero. -/
lemma sum_character_eq_zero_of_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero (p ^ n)]
    (k : ZMod (p ^ n)) (hk : k ≠ 0) :
    ∑ m : ZMod (p ^ n), character (p ^ n) k m = 0 := by
  -- Show that character_asAddChar (p^n) k is nontrivial (≠ 0 as AddChar)
  have h_ne_zero : character_asAddChar (p ^ n) k ≠ 0 := by
    intro h_eq
    -- The zero AddChar is the trivial character: ψ m = 1 for all m
    -- So if character_asAddChar = 0, then character (p^n) k 1 = 1
    have h_one : character (p ^ n) k 1 = 1 := by
      have := DFunLike.congr_fun h_eq 1
      simp [character_asAddChar] at this
      exact this
    -- But we proved character (p^n) k 1 ≠ 1 when k ≠ 0
    exact character_one_ne_one_of_ne_zero (p ^ n) k hk h_one
  -- Use mathlib: ∑ x, ψ x = 0 ↔ ψ ≠ 0
  -- Since character_asAddChar.toFun = character, the sums are equal
  change ∑ m, (character_asAddChar (p ^ n) k) m = 0
  exact AddChar.sum_eq_zero_iff_ne_zero.mpr h_ne_zero

/-- Generalized sum of nontrivial character is zero - works for any N, not just prime powers -/
lemma sum_character_eq_zero_of_ne_zero_general (N : ℕ) [NeZero N]
    (k : ZMod N) (hk : k ≠ 0) :
    ∑ m : ZMod N, character N k m = 0 := by
  -- Show that character_asAddChar N k is nontrivial (≠ 0 as AddChar)
  have h_ne_zero : character_asAddChar N k ≠ 0 := by
    intro h_eq
    have h_one : character N k 1 = 1 := by
      have := DFunLike.congr_fun h_eq 1
      simp [character_asAddChar] at this
      exact this
    exact character_one_ne_one_of_ne_zero N k hk h_one
  change ∑ m, (character_asAddChar N k) m = 0
  exact AddChar.sum_eq_zero_iff_ne_zero.mpr h_ne_zero

/-- Generalized character orthogonality - works for any N -/
lemma character_orthogonality_general (N : ℕ) [NeZero N]
    (k k' : ZMod N) :
    ∑ m : ZMod N, character N k m * conj (character N k' m) =
    if k = k' then (N : ℂ) else 0 := by
  have h_card : Fintype.card (ZMod N) = N := ZMod.card N
  by_cases h_eq : k = k'
  · -- Case k = k': characters are equal, sum = N
    subst h_eq
    simp only [ite_true]
    have h_one : ∀ m : ZMod N, character N k m * conj (character N k m) = 1 :=
      character_mul_conj N k
    simp only [h_one, Finset.sum_const, Finset.card_univ, h_card]
    simp only [nsmul_eq_mul, mul_one]
  · -- Case k ≠ k': use translation argument
    simp only [h_eq, ite_false]
    -- Simplify: char_k(m) · conj(char_k'(m)) = char_{k-k'}(m)
    have h_mul : ∀ m : ZMod N,
        character N k m * conj (character N k' m) = character N (k - k') m := by
      intro m
      -- Use character algebraic properties instead of fighting with casts
      -- 1) conj(char k') = char (-k')
      rw [character_conjugate_pair (n := N) (k := k') (m := m)]
      -- 2) Symmetry: character n a b = character n b a (commutativity in exponent)
      have hswap : ∀ a b : ZMod N, character N a b = character N b a := by
        intro a b
        unfold character
        congr 1
        push_cast
        ring
      -- 3) Use character_add in the *second* slot after swapping arguments
      calc
        character N k m * character N (-k') m
            = character N m k * character N m (-k') := by simp [hswap]
        _ = character N m (k + -k') := by
              simpa using (character_add (N := N) (k := m) (m := k) (a := -k')).symm
        _ = character N (k + -k') m := by simp [hswap]
        _ = character N (k - k') m := by simp [sub_eq_add_neg]
    calc ∑ m, character N k m * conj (character N k' m)
        = ∑ m, character N (k - k') m := by
          congr 1; ext m; rw [h_mul m]
      _ = 0 := by
          have h_diff_ne_zero : k - k' ≠ 0 := sub_ne_zero.mpr h_eq
          exact sum_character_eq_zero_of_ne_zero_general N (k - k') h_diff_ne_zero

/-- Generalized dual orthogonality - summing over characters (k) instead of group elements (m) -/
lemma character_orthogonality_dual_general (N : ℕ) [NeZero N]
    (m m' : ZMod N) :
    ∑ k : ZMod N, character N k m * conj (character N k m') =
    if m = m' then (N : ℂ) else 0 := by
  -- Use the fact that character N k m = character N m k (symmetry in exponent k·m)
  have hswap : ∀ a b : ZMod N, character N a b = character N b a := by
    intro a b
    unfold character
    congr 1
    push_cast
    ring
  have h_swap : ∀ k : ZMod N, character N k m * conj (character N k m') =
      character N m k * conj (character N m' k) := by
    intro k
    simp only [hswap]
  simp_rw [h_swap]
  exact character_orthogonality_general N m m'

/-- CHARACTER ORTHOGONALITY - The foundation of discrete Fourier transform -/
lemma character_orthogonality (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero (p ^ n)]
    (k k' : ZMod (p ^ n)) :
    ∑ m : ZMod (p ^ n), character (p ^ n) k m * conj (character (p ^ n) k' m) =
    if k = k' then (p ^ n : ℂ) else 0 := by
  -- Direct proof by cases using the conjugation identities
  have h_card : Fintype.card (ZMod (p ^ n)) = p ^ n := ZMod.card (p ^ n)
  by_cases h_eq : k = k'
  · -- Case k = k': characters are equal, sum = p^n
    subst h_eq
    simp only [ite_true]
    -- When k = k', each term is character * conj(character) = |character|² = 1
    have : ∀ m : ZMod (p ^ n),
        character (p ^ n) k m * conj (character (p ^ n) k m) = 1 := by
      intro m
      unfold character
      -- exp(z) * conj(exp(z)) = exp(z + conj(z))
      -- For purely imaginary z, conj(z) = -z, so z + conj(z) = 0
      rw [← Complex.exp_conj, ← Complex.exp_add]
      -- Simplify conjugations: conj(I) = -I, conj(real) = real
      simp [map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I,
       Complex.ofReal_natCast]
      -- Handle remaining starRingEnd applications (starRingEnd ℂ = conj)
      have : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
        show conj (2 : ℂ) = 2
        exact Complex.conj_natCast 2
      simp only [this]
      -- Now: 2πI*x - 2πI*x = 0
      ring_nf
      simp only [Complex.exp_zero]
    -- Sum of p^n copies of 1
    calc ∑ m, character (p ^ n) k m * conj (character (p ^ n) k m)
        = ∑ m, (1 : ℂ) := by congr 1; ext m; rw [this m]
      _ = Fintype.card (ZMod (p ^ n)) := by simp
      _ = (p ^ n : ℂ) := by rw [h_card]; norm_cast
  · -- Case k ≠ k': use geometric series
    simp only [h_eq, ite_false]
    -- Simplify: char_k(m) · conj(char_k'(m)) = char_{k-k'}(m)
    have h_simplify : ∀ m : ZMod (p ^ n),
        character (p ^ n) k m * conj (character (p ^ n) k' m) =
        character (p ^ n) (k - k') m := by
      intro m
      -- Use character algebraic properties instead of fighting with casts
      -- 1) conj(char k') = char (-k')
      rw [character_conjugate_pair (n := p ^ n) (k := k') (m := m)]
      -- 2) Symmetry: character n a b =
      -- character n b a (commutativity of multiplication in the exponent)
      have hswap : ∀ a b : ZMod (p ^ n),
          character (p ^ n) a b = character (p ^ n) b a := by
        intro a b
        unfold character
        congr 1
      -- target is equality of the real fractions inside the complex cast
        push_cast
        ring
      -- 3) Use character_add in the *second* slot after swapping arguments
      calc
        character (p ^ n) k m * character (p ^ n) (-k') m
            = character (p ^ n) m k * character (p ^ n) m (-k') := by simp [hswap]
        _ = character (p ^ n) m (k + -k') := by
              simpa using (character_add (N := p ^ n) (k := m) (m := k) (a := -k')).symm
        _ = character (p ^ n) (k + -k') m := by simp [hswap]
        _ = character (p ^ n) (k - k') m := by simp [sub_eq_add_neg]
    calc ∑ m, character (p ^ n) k m * conj (character (p ^ n) k' m)
        = ∑ m, character (p ^ n) (k - k') m := by
          congr 1; ext m; rw [h_simplify m]
      _ = 0 := by
          have h_diff_ne_zero : k - k' ≠ 0 := by
            intro h_zero
            apply h_eq
            exact sub_eq_zero.mp h_zero
          exact sum_character_eq_zero_of_ne_zero p n (k - k') h_diff_ne_zero


/-- Symmetry of the character: in our definition the kernel is symmetric in k and m. -/
lemma character_swap (N : ℕ) [NeZero N] (k m : ZMod N) :
    character N k m = character N m k := by
  unfold character
  congr 1
  push_cast
  ring

/-- Dual orthogonality: summing over characters (k) gives Kronecker delta in m. -/
lemma character_orthogonality_dual
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero (p ^ n)]
    (m m' : ZMod (p ^ n)) :
    ∑ k : ZMod (p ^ n), character (p ^ n) k m * conj (character (p ^ n) k m') =
      if m = m' then (p ^ n : ℂ) else 0 := by
  -- start from your existing lemma which sums over the second argument,
  -- then swap arguments inside the sum
  simpa [character_swap, mul_assoc, mul_left_comm, mul_comm] using
    (character_orthogonality (p := p) (n := n) (k := m) (k' := m'))

/-- Inner orthogonality: <χ_k, χ_{k'}> = δ_{kk'} * N -/
lemma character_orthogonality_inner
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero (p ^ n)]
    (m m' : ZMod (p ^ n)) :
    ∑ k : ZMod (p ^ n), character (p ^ n) k m * conj (character (p ^ n) k m') =
      if m = m' then (p ^ n : ℂ) else 0 :=
  character_orthogonality_dual p n m m'

/-- Finite Fourier inversion on ZMod (p^n): every function is a linear combination
of characters. -/
theorem character_basis_representation
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero (p ^ n)]
    (f : ZMod (p ^ n) → ℂ) :
    ∃ a : ZMod (p ^ n) → ℂ,
      ∀ m : ZMod (p ^ n),
        f m = ∑ k : ZMod (p ^ n), a k * character (p ^ n) k m := by
  classical
  let N : ℕ := p ^ n
  let U : Finset (ZMod N) := Finset.univ
  -- Fourier coefficients
  refine ⟨fun k => ((N : ℂ)⁻¹) * ∑ m' : ZMod N, f m' * conj (character N k m'), ?_⟩
  intro m
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  -- We prove the RHS equals f m, then flip.
  have hRHS :
      (∑ k : ZMod N,
        (((N : ℂ)⁻¹) * ∑ m' : ZMod N, f m' * conj (character N k m')) *
          character N k m)
        = f m := by
    -- rewrite all Fintype sums explicitly as univ sums to use Finset lemmas
    -- (this avoids any big simp/whnf expansions)
    change
      U.sum (fun k =>
        (((N : ℂ)⁻¹) * (U.sum (fun m' => f m' * conj (character N k m')))) *
          character N k m)
      = f m
    -- Step 1: pull (N⁻¹) out of the k-sum and expand product over the inner m'-sum.
    have h1 :
        U.sum (fun k =>
          (((N : ℂ)⁻¹) * (U.sum (fun m' => f m' * conj (character N k m')))) *
            character N k m)
        =
        ((N : ℂ)⁻¹) *
          U.sum (fun k =>
            (U.sum (fun m' => f m' * conj (character N k m'))) *
              character N k m) := by
      -- reassociate each summand into (N⁻¹) * (...)
      calc
        U.sum (fun k =>
          (((N : ℂ)⁻¹) * (U.sum (fun m' => f m' * conj (character N k m')))) *
            character N k m)
            =
          U.sum (fun k =>
            ((N : ℂ)⁻¹) *
              ((U.sum (fun m' => f m' * conj (character N k m'))) *
                character N k m)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring  -- just reassociation in ℂ
        _ =
          ((N : ℂ)⁻¹) *
            U.sum (fun k =>
              (U.sum (fun m' => f m' * conj (character N k m'))) *
                character N k m) := by
          -- pull scalar out of sum
          rw [← Finset.mul_sum]
    -- Step 2: swap the k-sum and m'-sum (finite sums), and rearrange factors.
    have h2 :
        U.sum (fun k =>
          (U.sum (fun m' => f m' * conj (character N k m'))) *
            character N k m)
        =
        U.sum (fun m' =>
          f m' *
            U.sum (fun k =>
              character N k m * conj (character N k m'))) := by
      -- Expand the inner product as a sum over m', then commute sums.
      -- (This is the only place we use sum_comm, and it’s finite/univ×univ.)
      calc
        U.sum (fun k =>
          (U.sum (fun m' => f m' * conj (character N k m'))) *
            character N k m)
            =
        U.sum (fun k =>
          U.sum (fun m' =>
            (f m' * conj (character N k m')) * character N k m)) := by
          -- distribute multiplication over the m'-sum
          refine Finset.sum_congr rfl ?_
          intro k hk
          -- (∑ m', g m') * c = ∑ m', g m' * c
          simpa [Finset.sum_mul, mul_assoc] using
            (Finset.sum_mul (s := U)
             (f := fun m' => f m' * conj (character N k m')) (a := character N k m))
        _ =
        U.sum (fun m' =>
          U.sum (fun k =>
            (f m' * conj (character N k m')) * character N k m)) := by
          -- commute the two finite sums
          exact Finset.sum_comm
        _ =
        U.sum (fun m' =>
          f m' *
            U.sum (fun k =>
              character N k m * conj (character N k m'))) := by
          -- factor out f m' and commute inside each summand
          refine Finset.sum_congr rfl ?_
          intro m' hm'
          -- inside: ∑ k, (f m' * conj(char k m')) * char k m
          --       = f m' * ∑ k, char k m * conj(char k m')
          -- by commutativity/associativity in ℂ
          calc
            U.sum (fun k =>
              (f m' * conj (character N k m')) * character N k m)
                =
            U.sum (fun k =>
              f m' * (character N k m * conj (character N k m'))) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              ring
            _ =
            f m' * U.sum (fun k =>
              character N k m * conj (character N k m')) := by
              -- pull scalar f m' out of the k-sum
              rw [← Finset.mul_sum]
    -- Step 3: apply orthogonality (inner k-sum becomes Kronecker delta)
    have h3 :
        U.sum (fun m' =>
          f m' *
            U.sum (fun k =>
              character N k m * conj (character N k m')))
        =
        U.sum (fun m' =>
          f m' * (if m = m' then (N : ℂ) else 0)) := by
      refine Finset.sum_congr rfl ?_
      intro m' hm'
      -- rewrite the inner sum using orthogonality_dual
      have := character_orthogonality_dual (p := p) (n := n) (m := m) (m' := m')
      -- The statement `this` says: ∑ k : ZMod (p^n), char k m * conj(char k m') = ...
      -- We need it for N where N := p^n
      congr 1
      -- Now show: U.sum (...) = if m = m' then N else 0
      calc U.sum (fun k => character N k m * conj (character N k m'))
          = ∑ k : ZMod (p ^ n), character (p ^ n) k m * conj (character (p ^ n) k m') := by
            simp [N, U]
        _ = if m = m' then (p ^ n : ℂ) else 0 := this
        _ = if m = m' then (N : ℂ) else 0 := by simp [N]
    -- Step 4: collapse the Kronecker-delta sum over m'
    have h4 :
        ((N : ℂ)⁻¹) * U.sum (fun m' => f m' * (if m = m' then (N : ℂ) else 0))
        = f m := by
      have hmU : m ∈ U := by simp [U]
      -- rewrite into a sum_ite form and collapse
      have hsum :
          U.sum (fun m' => f m' * (if m = m' then (N : ℂ) else 0))
            = f m * (N : ℂ) := by
      -- turn `if m = m'` into `if m' = m` so sum_ite_eq' applies cleanly
        calc
          U.sum (fun m' => f m' * (if m = m' then (N : ℂ) else 0))
              =
            U.sum (fun m' => if m' = m then f m' * (N : ℂ) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro m' hm'
              by_cases h : m' = m
              · subst h; simp
              · have : m ≠ m' := by simpa [eq_comm] using h
                simp [h, this]
          _ = f m * (N : ℂ) := by
              -- collapse at m
              simpa [U, hmU] using
                (Finset.sum_ite_eq' (s := U) (a := m)
                  (f := fun x => f x * (N : ℂ)))
      -- now cancel by multiplying with (N⁻¹)
      calc
        ((N : ℂ)⁻¹) * U.sum (fun m' => f m' * (if m = m' then (N : ℂ) else 0))
            =
        ((N : ℂ)⁻¹) * (f m * (N : ℂ)) := by rw [hsum]
        _ = f m := by field_simp [hN0]
    -- assemble the chain
    calc
      U.sum (fun k =>
        (((N : ℂ)⁻¹) * (U.sum (fun m' => f m' * conj (character N k m')))) *
          character N k m)
          =
      ((N : ℂ)⁻¹) *
        U.sum (fun k =>
          (U.sum (fun m' => f m' * conj (character N k m'))) * character N k m) := h1
      _ =
      ((N : ℂ)⁻¹) *
        U.sum (fun m' =>
          f m' *
            U.sum (fun k =>
              character N k m * conj (character N k m'))) := by
          rw [h2]
      _ =
      ((N : ℂ)⁻¹) *
        U.sum (fun m' =>
          f m' * (if m = m' then (N : ℂ) else 0)) := by
          rw [h3]
      _ = f m := h4
  -- Turn the RHS equality into the goal orientation.
  -- Goal currently: f m = ∑ k, a k * character N k m.
  -- Our hRHS is exactly that sum (expanded a), equals f m.
  -- So finish by rewriting and simpa.
  -- (We use `N := p^n` to keep Lean’s unfolding minimal.)
  -- First, unfold the "a" that we constructed:
  -- `simp` here is safe because it does not unfold `character`, only the lambda.
  have : f m =
      ∑ k : ZMod N,
        (((N : ℂ)⁻¹) * ∑ m' : ZMod N, f m' * conj (character N k m')) *
          character N k m := by
    simpa using hRHS.symm
  -- now rewrite N back to p^n and adjust the presentation to `a k * character ...`
  simpa [N] using this

/-- Parseval over `ZMod (p^n)` for the additive characters `character`. -/
theorem parseval_identity
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero (p ^ n)]
    (c : ZMod (p ^ n) → ℂ) :
    ∑ k : ZMod (p ^ n), ‖∑ x : ZMod (p ^ n), c x * character (p ^ n) k x‖ ^ 2 =
      (p ^ n : ℝ) * ∑ x : ZMod (p ^ n), ‖c x‖ ^ 2 := by
  classical
  let N : ℕ := p ^ n
  -- Define the k-th projection using Fintype sums (matches your goal form)
  let S : ZMod N → ℂ := fun k =>
    ∑ x : ZMod N, c x * character N k x
  -- Convert ‖·‖^2 to Complex.normSq (ℝ-valued)
  have step1 :
      ∑ k : ZMod N, ‖S k‖ ^ 2 =
        ∑ k : ZMod N, Complex.normSq (S k) := by
    congr 1; funext k
    simpa [Complex.normSq_eq_norm_sq]
  -- Main identity in ℝ (we’ll prove it via a ℂ identity + real part)
  have hC :
      ((∑ k : ZMod N, Complex.normSq (S k)) : ℂ)
        =
      (N : ℂ) * (∑ x : ZMod N, Complex.normSq (c x) : ℂ) := by
    classical
    -- unfold N to p^n inside this proof to match your orthogonality lemma exactly

    subst N  -- turns N into (p ^ n) everywhere
    -- Now we are on ZMod (p^n) everywhere, matching character_orthogonality_dual.
    -- rewrite normSq as z * conj z
    calc
      ∑ k : ZMod (p ^ n), (↑(Complex.normSq (S k)) : ℂ)
          = ∑ k, S k * conj (S k) := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              simpa using (Complex.mul_conj (S k)).symm
      _ = ∑ k, ( (∑ x, c x * character (p ^ n) k x)
               * conj (∑ y, c y * character (p ^ n) k y) ) := by
              simp [S]   -- since N is now p^n, S uses character (p^n)
      _ = ∑ k, (∑ x, ∑ y,
            (c x * character (p ^ n) k x)
              * conj (c y * character (p ^ n) k y)) := by
              -- use sum_mul_sum to expand product of sums
              simp [Finset.sum_mul_sum]
      _ = ∑ k, (∑ x, ∑ y,
            (c x * conj (c y)) *
              (character (p ^ n) k x * conj (character (p ^ n) k y))) := by
              -- push conj into the product, and reassociate
              -- this simp is small; avoid commutativity explosions
              simp [mul_assoc, mul_left_comm, mul_comm]
      _ = ∑ x, ∑ y,
            (c x * conj (c y)) *
              (∑ k, character (p ^ n) k x * conj (character (p ^ n) k y)) := by
        classical
      -- First, swap the outer `k` sum with the `x` sum:
      -- ∑ k, ∑ x, ... = ∑ x, ∑ k, ...
        rw [Finset.sum_comm]
      -- Now we have: ∑ x, ∑ k, ∑ y, ...
        refine Finset.sum_congr rfl ?_
        intro x hx
      -- Swap inner `k` and `y`:
      -- ∑ k, ∑ y, ... = ∑ y, ∑ k, ...
        rw [Finset.sum_comm]
      -- Now we have: ∑ x, ∑ y, ∑ k, ...
        refine Finset.sum_congr rfl ?_
        intro y hy
      -- Factor out (c x * conj (c y)) from the k-sum by rewriting the RHS:
      -- (c x * conj (c y)) * ∑ k, ... = ∑ k, (c x * conj (c y)) * ...
      -- and then finish by rfl
        symm
      -- `∑ k, ...` is definitionaly `∑ k in Finset.univ, ...` for a Fintype
        simpa [mul_assoc] using
          (Finset.mul_sum
            (s := (Finset.univ : Finset (ZMod (p ^ n))))
            (a := c x * (starRingEnd ℂ) (c y))
            (f := fun k : ZMod (p ^ n) =>
              character (p ^ n) k x * (starRingEnd ℂ) (character (p ^ n) k y)))
      _ = ∑ x, ∑ y,
            (c x * (starRingEnd ℂ) (c y)) *
              (if x = y then ((p : ℂ) ^ n) else 0) := by
              -- orthogonality injection (this is YOUR lemma)
              refine Finset.sum_congr rfl ?_
              intro x hx
              refine Finset.sum_congr rfl ?_
              intro y hy
              have horth := character_orthogonality_dual (p := p) (n := n) (m := x) (m' := y)
              simpa using congrArg (fun t => (c x * (starRingEnd ℂ) (c y)) * t) horth
      _ = ∑ x : ZMod (p ^ n), (c x * (starRingEnd ℂ) (c x)) * ((p : ℂ) ^ n) := by
            simp [Finset.sum_ite_eq, mul_assoc, mul_left_comm, mul_comm]
      _ = ((p : ℂ) ^ n) * ∑ x, (↑(Complex.normSq (c x)) : ℂ) := by
            -- factor and rewrite normSq
            calc
              ∑ x, (c x * (starRingEnd ℂ) (c x)) * ((p : ℂ) ^ n)
                  = ((p : ℂ) ^ n) * ∑ x, (c x * (starRingEnd ℂ) (c x)) := by
                      simp [mul_sum, sum_mul, mul_assoc, mul_left_comm, mul_comm]
              _ = ((p : ℂ) ^ n) * ∑ x, (↑(Complex.normSq (c x)) : ℂ) := by
                      refine congrArg (fun t => ((p : ℂ) ^ n) * t) ?_
                      refine Finset.sum_congr rfl ?_
                      intro x hx
                      simpa using (Complex.mul_conj (c x))
    -- turns (↑p : ℂ)^n into ↑(p^n : ℂ)
    simpa [Nat.cast_pow]
  -- Take real parts to get the ℝ identity
  have hR :
      (∑ k : ZMod N, Complex.normSq (S k))
        =
      (N : ℝ) * ∑ x : ZMod N, Complex.normSq (c x) := by
    have := congrArg Complex.re hC
    -- re(ofReal _) simplification
    simpa [Complex.ofReal_mul, Complex.ofReal_sum, mul_assoc] using this
  -- Finish: chain the rewrites and clean up definitional equalities.
  calc
    ∑ k : ZMod (p ^ n), ‖∑ x : ZMod (p ^ n), c x * character (p ^ n) k x‖ ^ 2
        = ∑ k : ZMod N, ‖S k‖ ^ 2 := by
            -- rewrite p^n as N everywhere
            simp [N, S]
    _ = ∑ k : ZMod N, Complex.normSq (S k) := by
            simpa using step1
    _ = (N : ℝ) * ∑ x : ZMod N, Complex.normSq (c x) := by
            simpa using hR
    _ = (N : ℝ) * ∑ x : ZMod N, ‖c x‖ ^ 2 := by
            -- no funext; just simp inside the sum
            simp [Complex.normSq_eq_norm_sq]
    _ = (p ^ n : ℝ) * ∑ x : ZMod N, ‖c x‖ ^ 2 := by
            -- THIS solves your remaining “↑N vs ↑p^n” goal
            simp [N]

/-- Power monotonicity in base. -/
lemma pow_le_pow_of_le_left' {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∀ n : ℕ, x ^ n ≤ y ^ n
  | 0 => by simp
  | (n+1) => by
    have ih := pow_le_pow_of_le_left' hx hxy n
    have hy : 0 ≤ y := le_trans hx hxy
    calc
      x ^ (n+1) = x ^ n * x := by ring
      _ ≤ y ^ n * x := mul_le_mul_of_nonneg_right ih hx
      _ ≤ y ^ n * y := mul_le_mul_of_nonneg_left hxy (pow_nonneg hy _)
      _ = y ^ (n+1) := by ring

/-- Helper for domination-based integrability. -/
lemma integrable_of_norm_le {f g : ℝ → ℝ}
    (hg : MeasureTheory.Integrable g)
    (hf_meas : AEStronglyMeasurable f (volume : Measure ℝ))
    (hfg : ∀ x, ‖f x‖ ≤ g x) :
    MeasureTheory.Integrable f := by
  -- g is nonnegative (since it dominates a norm)
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x => le_trans (norm_nonneg _) (hfg x)
  -- Convert to the form Integrable.mono expects: ‖f‖ ≤ ‖g‖
  have hfg' : ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ ≤ ‖g x‖ := ae_of_all _ fun x => by
    calc ‖f x‖ ≤ g x := hfg x
      _ = ‖g x‖ := (abs_of_nonneg (hg_nonneg x)).symm
  exact Integrable.mono hg hf_meas hfg'


end FourierBochner
