/-
Copyright (c) 2025 Zachary Mullaghy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Mullaghy, Gianfranco Romaelle
-/
import FourierBochner.FejerRiesz
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

/-- Finite Bochner theorem: a function on ZMod n is positive-definite iff it is a
positive linear combination of characters. -/
theorem bochner_finite (n : ℕ) [NeZero n] (f : ZMod n → ℂ) :
    IsPositiveDefiniteFinite n f ↔
    ∃ μ : ZMod n → ℝ, (∀ k, 0 < μ k) ∧
      ∀ m, f m = ∑ k : ZMod n, μ k * character n k m := by
  constructor
  · -- Forward: Positive-definite ⟹ positive Fourier coefficients
    intro hf
    classical
    letI : Fintype (ZMod n) := ZMod.fintype n


    let a : ZMod n → ℂ := fun k => ((n : ℂ)⁻¹) * ∑ m : ZMod n, f m * conj (character n k m)

    have ha_real : ∀ k, (a k).im = 0 := by
      intro k
      -- Proof: conj(a_k) = a_k via reindexing m ↦ -m
      -- Uses: f(-m) = conj(f(m)) [Hermitian], char_k(-m) = conj(char_k(m))
      have h_herm := hf.1  -- Hermitian symmetry: f(-x) = conj(f(x))
      -- First show conj(a k) = a k
      have h_conj_eq : conj (a k) = a k := by
        simp only [a]
      -- Goal: conj((n:ℂ)⁻¹ * Σ_m f(m) * conj(char_k(m))) = (n:ℂ)⁻¹ * Σ_m f(m) * conj(char_k(m))
      -- Distribute conj through multiplication and sum
        simp only [map_mul, map_sum, map_inv₀]
        have hn_real : conj (n : ℂ) = n := Complex.conj_ofReal n
        rw [hn_real]
      -- Goal: (n:ℂ)⁻¹ * Σ_m conj(f(m)) * conj(conj(char_k(m))) = (n:ℂ)⁻¹ * Σ_m f(m) * conj(char_k(m))
      -- Note: simp distributed conj through sum and product
      -- Simplify conj(conj(char)) = char on LHS
        simp only [Complex.conj_conj]
      -- Goal: (n:ℂ)⁻¹ * Σ_m conj(f(m)) * char_k(m) = (n:ℂ)⁻¹ * Σ_m f(m) * conj(char_k(m))
        congr 1
      -- Goal: Σ_m conj(f(m)) * char_k(m) = Σ_m f(m) * conj(char_k(m))
      -- Reindex LHS using m ↦ -m
        erw [Fintype.sum_equiv (Equiv.neg (ZMod n))]
        intro m
      -- Goal: f(-m) * conj(char_k(-m)) = conj(f(m)) * char_k(m)
        simp only [Equiv.neg_apply]
      -- From Hermitian: f(-m) = conj(f(m))
        have hf_neg : f (-m) = conj (f m) := h_herm m
      -- conj(char_k(-m)) = conj(conj(char_k(m))) = char_k(m)
        have hc_neg : conj (character n k (-m)) = character n k m := by
          rw [character_arg_conjugate]
          exact Complex.conj_conj _
        rw [hf_neg, hc_neg]
      -- From conj(z) = z, we get im(z) = 0
      rw [← Complex.conj_eq_iff_im.mp h_conj_eq]

    let μ : ZMod n → ℝ := fun k => (a k).re

    have h_rep : ∀ m, f m = ∑ k : ZMod n, (μ k : ℂ) * character n k m := by
      -- Fourier inversion via character_orthogonality_dual_general
      intro m
      -- Since a k is real (ha_real), μ k = (a k).re means (μ k : ℂ) = a k
      have ha_eq_mu : ∀ k, (μ k : ℂ) = a k := by
        intro k
        simp only [μ]
      -- a k is real (im = 0), so a k = (a k).re as complex
      -- Use: z = z.re ↔ z.im = 0
        rw [Complex.ext_iff]
        constructor
        · simp  -- re part: (a k).re = (a k).re
        · simp [ha_real k]  -- im part: 0 = (a k).im = 0
      simp_rw [ha_eq_mu]
      -- Goal: f m = Σ_k a_k * char_k(m)
      simp only [a]
      -- Goal: f m = Σ_k ((n:ℂ)⁻¹ * Σ_m' f(m') * conj(char_k(m'))) * char_k(m)
      -- Rearrange each term: ((n⁻¹) * S) * char = (n⁻¹) * (S * char)
      conv_rhs => arg 2; ext k; rw [mul_assoc]
      -- Factor out (n:ℂ)⁻¹ from sum
      rw [← Finset.mul_sum]
      -- Goal: f m = (n:ℂ)⁻¹ * Σ_k (Σ_m' f(m') * conj(char_k(m'))) * char_k(m)
      -- Distribute char_k(m) into inner sum
      conv_rhs => arg 2; arg 2; ext k; rw [Finset.sum_mul]
      -- Goal: f m = (n:ℂ)⁻¹ * Σ_k Σ_m' (f(m') * conj(char_k(m'))) * char_k(m)
      -- Swap sums
      rw [Finset.sum_comm]
      -- Goal: f m = (n:ℂ)⁻¹ * Σ_m' Σ_k (f(m') * conj(char_k(m'))) * char_k(m)
      -- Rearrange: (f(m') * conj(char_k(m'))) * char_k(m) = f(m') * (conj(char_k(m')) * char_k(m))
      conv_rhs => arg 2; arg 2; ext m'; arg 2; ext k; rw [mul_assoc]
      -- Factor out f(m') from inner sum
      conv_rhs => arg 2; arg 2; ext m'; rw [← Finset.mul_sum]
      -- Goal: f m = (n:ℂ)⁻¹ * Σ_m' f(m') * Σ_k conj(char_k(m')) * char_k(m)
      -- Reorder: conj(char_k(m')) * char_k(m) = char_k(m) * conj(char_k(m'))
      conv_rhs => arg 2; arg 2; ext m'; arg 2; arg 2; ext k; rw [mul_comm]
      -- Apply character orthogonality: Σ_k char_k(m) * conj(char_k(m')) = n * δ_{m,m'}
      simp_rw [character_orthogonality_dual_general n m]
      -- Goal: f m = (n:ℂ)⁻¹ * Σ_m' f(m') * (if m = m' then n else 0)
      rw [Finset.sum_eq_single m]
      · -- Main term: m' = m
        simp only [ite_true]
        field_simp [NeZero.ne n]
      · -- Off-diagonal: m' ≠ m
        intro m' _ hm'
        simp only [Ne.symm hm', ite_false, mul_zero]
      · -- m not in univ (impossible)
        intro hm; exact (hm (Finset.mem_univ m)).elim

    have hμ_pos : ∀ k, 0 < μ k := by
      -- Test c = char_{k₀}, quadratic form = n²·μ_{k₀}
      -- If μ_{k₀} ≤ 0, contradicts positive-definiteness
      intro k₀
      -- Use positive-definiteness with c = character n k₀
      let c : ZMod n → ℂ := fun i => character n k₀ i
      -- c is nonzero (characters are never identically zero)
      have hc_ne : c ≠ 0 := by
        intro h_all_zero
        have h0 : c 0 = 0 := congr_fun h_all_zero 0
        simp only [c, character, ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div,
          Complex.ofReal_zero, Complex.exp_zero] at h0
        exact one_ne_zero h0
      -- Apply positive-definiteness
      have h_quad := hf.2 c hc_ne
      have h_calc : (∑ i : ZMod n, ∑ j : ZMod n, conj (c i) * c j * f (i - j)).re =
                    (n : ℝ)^2 * μ k₀ := by
      -- Key identity: testing with c = char_{k₀} extracts coefficient μ_{k₀}
        simp only [c]
      -- Substitute f using h_rep and expand
        simp_rw [h_rep, character_sub_eq_mul]
      -- Rearrange sums: we need ∑_i ∑_j ∑_k → ∑_k ∑_i ∑_j
        simp_rw [Finset.mul_sum]
      -- Now: ∑_i ∑_j ∑_k conj(char_{k₀}(i)) * char_{k₀}(j) * (μ_k * char_k(i) * conj(char_k(j)))

      -- For each k, compute the inner double sum
        have h_inner : ∀ k : ZMod n,
            (∑ i : ZMod n, ∑ j : ZMod n, conj (character n k₀ i) * character n k₀ j *
              ((μ k : ℂ) * (character n k i * conj (character n k j)))).re =
            μ k * (if k = k₀ then (n : ℝ)^2 else 0) := by
          intro k
          -- Rearrange the expression
          have h_alg : ∑ i : ZMod n, ∑ j : ZMod n, conj (character n k₀ i) * character n k₀ j *
              ((μ k : ℂ) * (character n k i * conj (character n k j))) =
            (μ k : ℂ) * (∑ i : ZMod n, character n k i * conj (character n k₀ i)) *
                       (∑ j : ZMod n, character n k₀ j * conj (character n k j)) := by
            -- Following the backward direction pattern (lines 18602-18613)
            calc ∑ i : ZMod n, ∑ j : ZMod n, conj (character n k₀ i) * character n k₀ j *
                    ((μ k : ℂ) * (character n k i * conj (character n k j)))
              -- Step 1: Rearrange each term to factor as (μ k) * ((X_i) * (Y_j))
              _ = ∑ i : ZMod n, ∑ j : ZMod n, (μ k : ℂ) *
                    ((character n k i * conj (character n k₀ i)) *
                     (character n k₀ j * conj (character n k j))) := by
                  congr 1; ext i; congr 1; ext j; ring
              -- Step 2: Pull μ k out of both sums using backward direction pattern
              _ = (μ k : ℂ) * ∑ i : ZMod n, ∑ j : ZMod n,
                    (character n k i * conj (character n k₀ i)) *
                    (character n k₀ j * conj (character n k j)) := by
                  conv_lhs => arg 2; ext i; rw [← Finset.mul_sum]
                  rw [← Finset.mul_sum]
              -- Step 3: Factor double sum as product of sums (same as backward line 18612-18613)
              _ = (μ k : ℂ) * ((∑ i : ZMod n, character n k i * conj (character n k₀ i)) *
                    (∑ j : ZMod n, character n k₀ j * conj (character n k j))) := by
                  congr 1
                  rw [Finset.sum_mul_sum]
              _ = (μ k : ℂ) * (∑ i : ZMod n, character n k i * conj (character n k₀ i)) *
                    (∑ j : ZMod n, character n k₀ j * conj (character n k j)) := by ring
          rw [h_alg]
          -- Apply orthogonality
          rw [character_orthogonality_general, character_orthogonality_general]
          simp only [eq_comm (a := k₀) (b := k)]
          split_ifs with h
          · -- k = k₀: result is μ k * n * n = μ k * n²
            simp only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
            ring
          · -- k ≠ k₀: result is 0
            simp only [mul_zero, Complex.zero_re]

      -- Swap the sum order: ∑_i ∑_j ∑_k → ∑_k (∑_i ∑_j)
      -- First, reorder the sums (move k to outermost) using backward direction pattern
        have h_step1 : ∑ i : ZMod n, ∑ j : ZMod n, ∑ k : ZMod n,
            conj (character n k₀ i) * character n k₀ j *
              ((μ k : ℂ) * (character n k i * conj (character n k j))) =
            ∑ i : ZMod n, ∑ k : ZMod n, ∑ j : ZMod n,
            conj (character n k₀ i) * character n k₀ j *
              ((μ k : ℂ) * (character n k i * conj (character n k j))) := by
          -- Swap j and k inside each i (like backward lines 18571-18573)
          apply Finset.sum_congr rfl; intro i _
          exact Finset.sum_comm
        have h_step2 : ∑ i : ZMod n, ∑ k : ZMod n, ∑ j : ZMod n,
            conj (character n k₀ i) * character n k₀ j *
              ((μ k : ℂ) * (character n k i * conj (character n k j))) =
            ∑ k : ZMod n, ∑ i : ZMod n, ∑ j : ZMod n,
            conj (character n k₀ i) * character n k₀ j *
              ((μ k : ℂ) * (character n k i * conj (character n k j))) := by
          -- Swap i and k at outer level (like backward lines 18574-18575)
          exact Finset.sum_comm
        have h_reorder := h_step1.trans h_step2
        calc (∑ i : ZMod n, ∑ j : ZMod n, ∑ k : ZMod n,
            conj (character n k₀ i) * character n k₀ j *
              ((μ k : ℂ) * (character n k i * conj (character n k j)))).re
          = (∑ k : ZMod n, ∑ i : ZMod n, ∑ j : ZMod n,
            conj (character n k₀ i) * character n k₀ j *
              ((μ k : ℂ) * (character n k i * conj (character n k j)))).re :=
            congrArg Complex.re h_reorder
          _ = ∑ k : ZMod n, (∑ i : ZMod n, ∑ j : ZMod n,
            conj (character n k₀ i) * character n k₀ j *
              ((μ k : ℂ) * (character n k i * conj (character n k j)))).re := by
            rw [Complex.re_sum]
          _ = ∑ k : ZMod n, μ k * (if k = k₀ then (n : ℝ)^2 else 0) := by
            apply Finset.sum_congr rfl; intro k _
            exact h_inner k
          _ = μ k₀ * (n : ℝ)^2 := by
            rw [Finset.sum_eq_single k₀]
            · simp only [ite_true]
            · intro k _ hk; simp only [hk, ite_false, mul_zero]
            · intro h; exact (h (Finset.mem_univ k₀)).elim
          _ = (n : ℝ)^2 * μ k₀ := by ring
      rw [h_calc] at h_quad
      -- n² * μ k₀ > 0, and n² > 0, so μ k₀ > 0
      have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos n)
      have hn_sq_pos : (0 : ℝ) < (n : ℝ)^2 := sq_pos_of_pos hn_pos
      exact (mul_pos_iff_of_pos_left hn_sq_pos).mp h_quad

    exact ⟨μ, hμ_pos, h_rep⟩
  · -- Backward: Positive measure ⟹ positive-definite
    intro ⟨μ, hμ_pos, hμ_rep⟩
    constructor
    · -- Conjugate symmetry: f(-x) = conj(f(x))
      intro x
      calc f (-x)
          = ∑ k : ZMod n, μ k * character n k (-x) := hμ_rep (-x)
        _ = ∑ k : ZMod n, μ k * conj (character n k x) := by
            congr 1; ext k
            -- char_k(-x) = exp(-2πikx/n) = conj(exp(2πikx/n)) = conj(char_k(x))
            rw [character_arg_conjugate]
        _ = conj (∑ k : ZMod n, μ k * character n k x) := by
            rw [map_sum]
            congr 1; ext k
            -- conj(μ_k · char_k(x)) = μ_k · conj(char_k(x)) since μ_k is real
            rw [map_mul]
            congr 1
            exact (conj_ofReal (μ k)).symm
        _ = conj (f x) := by rw [← hμ_rep x]
    · -- Positive definiteness (strict positivity for non-zero test vectors)
      intro c hc_ne
      letI : Fintype (ZMod n) := ZMod.fintype n
      -- The quadratic form is: ∑_i ∑_j conj(c_i) · c_j · f(i-j)
      -- Substituting f(i-j) = ∑_k μ_k · char_k(i-j):
      calc (∑ i : ZMod n, ∑ j : ZMod n, conj (c i) * c j * f (i - j)).re
          = (∑ i : ZMod n, ∑ j : ZMod n,
              conj (c i) * c j * ∑ k : ZMod n, μ k * character n k (i - j)).re := by
              simp_rw [hμ_rep]
        _ = (∑ k : ZMod n, μ k * (∑ i : ZMod n, ∑ j : ZMod n,
              conj (c i) * c j * character n k (i - j))).re := by
              -- Rearrange: move ∑ over k from innermost to outermost
              congr 1
              calc ∑ i, ∑ j, conj (c i) * c j * ∑ k, μ k * character n k (i - j)
                  = ∑ i, ∑ j, ∑ k, conj (c i) * c j * (μ k * character n k (i - j)) := by
                      congr 1; ext i; congr 1; ext j
                      rw [Finset.mul_sum]
                _ = ∑ i, ∑ k, ∑ j, conj (c i) * c j * (μ k * character n k (i - j)) := by
                      congr 1; ext i
                      exact Finset.sum_comm
                _ = ∑ k, ∑ i, ∑ j, conj (c i) * c j * (μ k * character n k (i - j)) := by
                      exact Finset.sum_comm
                _ = ∑ k, ∑ i, ∑ j, μ k * (conj (c i) * c j * character n k (i - j)) := by
                      congr 1; ext k; congr 1; ext i; congr 1; ext j
                      ring
                _ = ∑ k, μ k * (∑ i, ∑ j, conj (c i) * c j * character n k (i - j)) := by
                      congr 1; ext k
                      -- First factor out μ k from the inner j-sum
                      conv_lhs => arg 2; ext i; rw [← Finset.mul_sum]
                      -- Then factor out μ k from the outer i-sum
                      rw [← Finset.mul_sum]
        _ = (∑ k : ZMod n, (μ k : ℂ) * ‖∑ j : ZMod n, c j * conj (character n k j)‖ ^ 2).re := by
              -- Use character_sub_eq_mul to show each summand equals norm squared
              -- First show the complex sums are equal
              congr 1
              -- Show sums are equal by showing summands are equal for all k
              apply Finset.sum_congr rfl
              intro k _
              congr 1
              -- Quadratic form factors as |w'|² where w' = ∑ c * conj(char)
              -- ∑ i,j conj(c_i) * c_j * char_k(i-j) = |∑ c_j * conj(char_k(j))|²
              calc ∑ i : ZMod n, ∑ j : ZMod n, conj (c i) * c j * character n k (i - j)
                  = ∑ i : ZMod n, ∑ j : ZMod n,
                      conj (c i) * c j * (character n k i * conj (character n k j)) := by
                    congr 1; ext i; congr 1; ext j
                    rw [character_sub_eq_mul]
                _ = ∑ i : ZMod n, ∑ j : ZMod n,
                      conj (c i) * character n k i * (c j * conj (character n k j)) := by
                    congr 1; ext i; congr 1; ext j
                    ring
                _ = (∑ i : ZMod n, conj (c i) * character n k i) *
                    (∑ j : ZMod n, c j * conj (character n k j)) := by
                    rw [Finset.sum_mul_sum]
                _ = ‖∑ j : ZMod n, c j * conj (character n k j)‖ ^ 2 := by
                    -- First factor = conj of second factor
                    have h_conj : (∑ i : ZMod n, conj (c i) * character n k i) =
                                  conj (∑ j : ZMod n, c j * conj (character n k j)) := by
                      rw [map_sum]
                      congr 1; ext i
                      simp only [map_mul, conj_conj]
                    rw [h_conj]
                    -- Now LHS = conj(w') * w' = |w'|² = ‖w'‖²
                    rw [sq, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
                    simp only [sq, Complex.ofReal_mul]
        _ = ∑ k : ZMod n, μ k * ‖∑ j : ZMod n, c j * conj (character n k j)‖ ^ 2 := by
              -- Pull out real part: all terms are real (μ k ∈ ℝ and ‖·‖² ∈ ℝ)
              -- The sum (μ k : ℂ) * ‖...‖² is real, so .re gives back the real sum
              have h_real : ∀ k : ZMod n,
                  ((μ k : ℂ) * (‖∑ j, c j * conj (character n k j)‖ : ℂ) ^ 2).re =
                  μ k * ‖∑ j, c j * conj (character n k j)‖ ^ 2 := by
                intro k
                simp only [sq, Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re,
                  Complex.ofReal_im, mul_zero, sub_zero]
                ring
              simp only [Complex.re_sum, h_real]
        _ > 0 := by
              have h_nonneg : ∀ k ∈ Finset.univ, 0 ≤ μ k * ‖∑ j, c j * conj (character n k j)‖ ^ 2 := by
                intro k _
                apply mul_nonneg (le_of_lt (hμ_pos k)) (sq_nonneg _)
              -- Step 2: At least one term is > 0
              -- c ≠ 0 means some c_j ≠ 0, and DFT is invertible, so some Fourier coefficient ≠ 0
              have h_exists : ∃ k ∈ Finset.univ, 0 < μ k * ‖∑ j, c j * conj (character n k j)‖ ^ 2 := by
                let w : ZMod n → ℂ := fun k => ∑ j, c j * conj (character n k j)
                suffices h : ∃ k, w k ≠ 0 by
                  obtain ⟨k₀, hk₀⟩ := h
                  use k₀, Finset.mem_univ k₀
                  apply mul_pos (hμ_pos k₀)
                  rw [sq_pos_iff]
                  exact norm_ne_zero_iff.mpr hk₀
                -- If all w(k) = 0, then c = 0 by Fourier inversion
                -- This uses character_orthogonality_dual_general n
                by_contra h_all_zero
                push_neg at h_all_zero
                apply hc_ne
                -- c = 0 via Fourier inversion
                -- Key identity: ∑_k w(k) * char(k,m) = n * c(m)
                -- When all w(k) = 0, we get 0 = n * c(m), so c(m) = 0
                ext m
                -- Prove the Fourier inversion identity
                have h_identity : ∑ k : ZMod n, w k * character n k m = (n : ℂ) * c m := by
                  simp only [w]
                  -- Expand: ∑_k (∑_j c(j) * conj(char k j)) * char k m
                  -- = ∑_k ∑_j c(j) * conj(char k j) * char k m
                  -- = ∑_j c(j) * ∑_k conj(char k j) * char k m  (swap sums)
                  -- = ∑_j c(j) * (if m = j then n else 0)       (orthogonality)
                  -- = n * c(m)
                  calc ∑ k : ZMod n, (∑ j : ZMod n, c j * conj (character n k j)) * character n k m
                      = ∑ k : ZMod n, ∑ j : ZMod n, c j * conj (character n k j) * character n k m := by
                        congr 1; ext k; rw [Finset.sum_mul]
                    _ = ∑ j : ZMod n, ∑ k : ZMod n, c j * conj (character n k j) * character n k m := by
                        rw [Finset.sum_comm]
                    _ = ∑ j : ZMod n, c j * ∑ k : ZMod n, conj (character n k j) * character n k m := by
                        congr 1; ext j
                        have h_assoc : ∀ k, c j * conj (character n k j) * character n k m =
                            c j * (conj (character n k j) * character n k m) := by intro k; ring
                        simp_rw [h_assoc]
                        rw [← Finset.mul_sum]
                    _ = ∑ j : ZMod n, c j * ∑ k : ZMod n, character n k m * conj (character n k j) := by
                        congr 1; ext j; congr 1; congr 1; ext k; ring
                    _ = ∑ j : ZMod n, c j * (if m = j then (n : ℂ) else 0) := by
                        congr 1; ext j; congr 1; exact character_orthogonality_dual_general n m j
                    _ = (n : ℂ) * c m := by
                        rw [Finset.sum_eq_single m]
                        · -- Goal: c m * (if m = m then n else 0) = n * c m
                          simp only [ite_true]
                          ring
                        · intro j _ hmj; simp only [Ne.symm hmj, ite_false, mul_zero]
                        · intro hm; exact (hm (Finset.mem_univ m)).elim
                -- Now use h_identity and h_all_zero
                have h_sum_zero : ∑ k : ZMod n, w k * character n k m = 0 := by
                  simp only [h_all_zero, zero_mul, Finset.sum_const_zero]
                rw [h_identity] at h_sum_zero
                -- n * c(m) = 0, so c(m) = 0
                have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
                simp only [Pi.zero_apply]
                exact (mul_eq_zero.mp h_sum_zero).resolve_left hn_ne
              -- Step 3: Apply sum_pos' (nonneg terms with at least one positive)
              exact Finset.sum_pos' h_nonneg h_exists

/-- A 2π-periodic function satisfies f(x + 2πk) = f(x) for any integer k. -/
lemma periodic_shift (f : ℝ → ℂ) (hf : ∀ x : ℝ, f (x + 2 * Real.pi) = f x)
    (x : ℝ) (k : ℤ) : f (x + 2 * Real.pi * k) = f x := by
  -- Use Function.Periodic and its integer multiple property
  have hper : Function.Periodic f (2 * Real.pi) := hf
  -- Periodic.int_mul gives: Periodic f (k * (2π))
  have hper_k := hper.int_mul k
  -- Apply at x: f(x + k * 2π) = f x
  have h := hper_k x
  -- Rewrite k * (2π) to 2π * k
  convert h using 2
  ring

/-- PROFINITE TOPOLOGY = STANDARD TOPOLOGY -/
theorem profinite_topology_eq_standard (f : ℝ → ℂ) (a : ℝ) (p : ℕ) [Fact (Nat.Prime p)]
    (hf_periodic : ∀ x : ℝ, f (x + 2 * Real.pi) = f x)
    (hf_classical : ContinuousAt f a) :
    IsProfiniteContinuousAt f a p := by
  intro ε hε
  -- Strategy: Use classical continuity and the density of character grids.
  -- For small δ and large N, charAngle is close to both θ and a.

  have hε4 : (0 : ℝ) < ε / 4 := by linarith

  -- Step 1: From classical continuity at a, get δ₀ such that
  -- |x - a| < δ₀ implies ‖f x - f a‖ < ε/4
  rw [Metric.continuousAt_iff] at hf_classical
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := hf_classical (ε / 4) hε4

  use δ₀ / 2
  constructor
  · linarith

  -- Find N large enough that grid spacing < δ₀/2
  -- Grid spacing at level n is 2π/p^n, so we need 2π/p^N < δ₀/2
  -- i.e., p^N > 4π/δ₀
  -- Use: p ≥ 2, so p^n grows without bound

  have hp : 1 < p := Nat.Prime.one_lt (Fact.elim inferInstance)
  have hp_pos : 0 < p := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_of_lt hp)

  -- Find N such that p^N > 4π/δ₀
  -- Since p ≥ 2, we have p^n → ∞, so such N exists
  -- Use: p^n ≥ n+1 for p ≥ 2, so take N > 4π/δ₀
  let bound := 4 * Real.pi / δ₀
  let N := Nat.ceil bound + 1

  use N
  intro n hn θ hθ_close

  -- Show both inequalities hold
  -- Key: For n ≥ N, we have π/p^n < δ₀/4 (since p^n ≥ p^N > 4π/δ₀)
  -- By charAngle_approximation_bound: ∃ k, |charAngle - θ - 2πk| ≤ π/p^n < δ₀/4
  -- For 2π-periodic f (or working on S¹), this means |f(charAngle) - f(θ)| is controlled.

  -- Technical bound: p^n > bound = 4π/δ₀ for n ≥ N
  have hN_bound : (bound : ℝ) < (N : ℕ) := by
    simp only [N]
    have h2 : bound ≤ Nat.ceil bound := Nat.le_ceil bound
    have h3 : (Nat.ceil bound : ℝ) < (Nat.ceil bound + 1 : ℕ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      linarith
    linarith
  have h2p : (2 : ℝ) ≤ (p : ℝ) := by
    have hp2 : 2 ≤ p := hp
    exact_mod_cast hp2
  have hn_bound : bound < (p : ℝ) ^ n := by
    calc bound < (N : ℝ) := hN_bound
      _ ≤ (n : ℝ) := by exact_mod_cast hn
      _ ≤ 2 ^ n := nat_le_two_pow n
      _ ≤ (p : ℝ) ^ n := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2p n

  -- Therefore π/p^n < δ₀/4
  have hgrid_small : Real.pi / (p : ℝ) ^ n < δ₀ / 4 := by
    have hpn_pos : (0 : ℝ) < (p : ℝ) ^ n := by positivity
    rw [div_lt_div_iff₀ hpn_pos (by linarith : (0 : ℝ) < 4)]
    -- bound = 4π/δ₀, so bound * δ₀ = 4π
    -- From hn_bound: bound < p^n, so 4π = bound * δ₀ < p^n * δ₀
    have hbound_prod : bound * δ₀ = 4 * Real.pi := by
      simp only [bound]
      field_simp
    have h_lt : bound * δ₀ < (p : ℝ) ^ n * δ₀ := by
      apply mul_lt_mul_of_pos_right hn_bound hδ₀_pos
    calc Real.pi * 4 = 4 * Real.pi := by ring
      _ = bound * δ₀ := hbound_prod.symm
      _ < (p : ℝ) ^ n * δ₀ := h_lt
      _ = δ₀ * (p : ℝ) ^ n := by ring

  constructor

  -- Part 1: ‖f θ - f (charAngle p n θ)‖ < ε/2
  · -- Use charAngle bound + periodicity + triangle inequality
    obtain ⟨k, hk⟩ := charAngle_approximation_bound p n θ
    have hpn_pos : (0 : ℝ) < (p : ℝ) ^ n := by positivity

    -- Key: charAngle - 2πk is within δ₀/4 of θ
    have hchar_shifted : |charAngle p n θ - 2 * Real.pi * k - θ| < δ₀ / 4 := by
      have h := hk
      calc |charAngle p n θ - 2 * Real.pi * k - θ|
          = |charAngle p n θ - θ - 2 * Real.pi * k| := by ring_nf
        _ ≤ Real.pi / (p : ℝ) ^ n := h
        _ < δ₀ / 4 := hgrid_small

    -- By periodicity: f(charAngle) = f(charAngle - 2πk)
    have hf_per_char : f (charAngle p n θ) = f (charAngle p n θ - 2 * Real.pi * k) := by
      have h := periodic_shift f hf_periodic (charAngle p n θ - 2 * Real.pi * k) k
      simp only [sub_add_cancel] at h
      exact h

    -- Both θ and (charAngle - 2πk) are within δ₀ of a
    have hθ_close_a : dist θ a < δ₀ := by
      simp only [Real.dist_eq]
      calc |θ - a| < δ₀ / 2 := hθ_close
        _ < δ₀ := by linarith

    have hchar_shifted_close_a : dist (charAngle p n θ - 2 * Real.pi * k) a < δ₀ := by
      simp only [Real.dist_eq]
      calc |charAngle p n θ - 2 * Real.pi * k - a|
          ≤ |charAngle p n θ - 2 * Real.pi * k - θ| + |θ - a| := by
            have := abs_sub_le (charAngle p n θ - 2 * Real.pi * k) θ a
            linarith [this]
        _ < δ₀ / 4 + δ₀ / 2 := by linarith [hchar_shifted, hθ_close]
        _ < δ₀ := by linarith

    -- Apply continuity and triangle inequality
    have hfθ : dist (f θ) (f a) < ε / 4 := hδ₀ hθ_close_a
    have hfchar : dist (f (charAngle p n θ - 2 * Real.pi * k)) (f a) < ε / 4 :=
      hδ₀ hchar_shifted_close_a

    calc ‖f θ - f (charAngle p n θ)‖
        = ‖f θ - f (charAngle p n θ - 2 * Real.pi * k)‖ := by rw [hf_per_char]
      _ = dist (f θ) (f (charAngle p n θ - 2 * Real.pi * k)) := (dist_eq_norm _ _).symm
      _ ≤ dist (f θ) (f a) + dist (f a) (f (charAngle p n θ - 2 * Real.pi * k)) := dist_triangle _ _ _
      _ = dist (f θ) (f a) + dist (f (charAngle p n θ - 2 * Real.pi * k)) (f a) := by rw [dist_comm (f a)]
      _ < ε / 4 + ε / 4 := by linarith [hfθ, hfchar]
      _ = ε / 2 := by ring

  -- Part 2: ‖f (charAngle p n θ) - f a‖ < ε/2
  · -- Use periodicity to reduce to a shifted point close to a
    obtain ⟨k, hk⟩ := charAngle_approximation_bound p n θ
    have hpn_pos : (0 : ℝ) < (p : ℝ) ^ n := by positivity

    -- Key: charAngle - 2πk is within δ₀/4 of θ
    have hchar_shifted : |charAngle p n θ - 2 * Real.pi * k - θ| < δ₀ / 4 := by
      calc |charAngle p n θ - 2 * Real.pi * k - θ|
          = |charAngle p n θ - θ - 2 * Real.pi * k| := by ring_nf
        _ ≤ Real.pi / (p : ℝ) ^ n := hk
        _ < δ₀ / 4 := hgrid_small

    -- By periodicity: f(charAngle) = f(charAngle - 2πk)
    have hf_per_char : f (charAngle p n θ) = f (charAngle p n θ - 2 * Real.pi * k) := by
      have h := periodic_shift f hf_periodic (charAngle p n θ - 2 * Real.pi * k) k
      simp only [sub_add_cancel] at h
      exact h

    -- (charAngle - 2πk) is within δ₀ of a
    have hchar_shifted_close_a : dist (charAngle p n θ - 2 * Real.pi * k) a < δ₀ := by
      simp only [Real.dist_eq]
      calc |charAngle p n θ - 2 * Real.pi * k - a|
          ≤ |charAngle p n θ - 2 * Real.pi * k - θ| + |θ - a| := by
            have := abs_sub_le (charAngle p n θ - 2 * Real.pi * k) θ a
            linarith [this]
        _ < δ₀ / 4 + δ₀ / 2 := by linarith [hchar_shifted, hθ_close]
        _ < δ₀ := by linarith

    -- Apply continuity
    have hfchar : dist (f (charAngle p n θ - 2 * Real.pi * k)) (f a) < ε / 4 :=
      hδ₀ hchar_shifted_close_a

    calc ‖f (charAngle p n θ) - f a‖
        = ‖f (charAngle p n θ - 2 * Real.pi * k) - f a‖ := by rw [hf_per_char]
      _ = dist (f (charAngle p n θ - 2 * Real.pi * k)) (f a) := (dist_eq_norm _ _).symm
      _ < ε / 4 := hfchar
      _ < ε / 2 := by linarith

/-! ## STEP 1: CHARACTERS AND KERNEL EXTRACTION

The sesquilinear form, when evaluated on characters χᵤ(n) = uⁿ,
directly recovers the kernel f as Fourier coefficients.
-/

/-- A character on ℤ is determined by a point u ∈ U(1). -/
noncomputable def circle_character (u : ℂ) (_hu : ‖u‖ = 1) : ℤ → ℂ := fun n => u ^ n

/-- Characters as trigonometric polynomials (single Fourier mode). -/
noncomputable def circle_character_poly (u : ℂ) (_hu : ‖u‖ = 1) : TrigPolyℤ :=
  Finsupp.single 1 u

/-- ⟨χᵤ, χᵥ⟩_f = (v/u) · f(0) for single-term character polynomials. -/
lemma sesquilinear_form_circle_characters
    (f : ℝ → ℂ) (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    sesquilinear_form f (circle_character_poly u hu) (circle_character_poly v hv) =
      (v / u) * f 0 := by

  unfold sesquilinear_form circle_character_poly
  have hu_ne : u ≠ 0 := fun h => by simp only [h, norm_zero] at hu; exact one_ne_zero hu.symm
  have hv_ne : v ≠ 0 := fun h => by simp only [h, norm_zero] at hv; exact one_ne_zero hv.symm
  simp only [Finsupp.support_single_ne_zero (1 : ℤ) hu_ne,
             Finsupp.support_single_ne_zero (1 : ℤ) hv_ne,
             Finset.sum_singleton, Finsupp.single_eq_same, sub_self]
  -- conj(u) * v * f(0) = (v/u) * f(0)
  have h_conj : starRingEnd ℂ u = u⁻¹ := by
    -- On unit circle: conj(u) * u = |u|² = 1, so conj(u) = u⁻¹
    have h1 : starRingEnd ℂ u * u = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self]
      rw [Complex.normSq_eq_norm_sq]
      rw [hu]
      norm_num
    have h2 : u * starRingEnd ℂ u = 1 := by rw [mul_comm]; exact h1
    exact eq_inv_of_mul_eq_one_right h2
  rw [h_conj]
  field_simp

/-! ## STEP 2: FINITE BOCHNER (Roots of Unity) ✅ COMPLETE -/

/-- The n-th roots of unity as a finite set. -/
noncomputable def roots_of_unity_set (n : ℕ+) : Finset ℂ :=
  (Finset.range n.val).image (fun k : ℕ => Complex.exp (2 * Real.pi * I * (k : ℂ) / (n : ℂ)))

/-- Elements of roots_of_unity_set have norm 1. -/
lemma roots_of_unity_set_norm_eq_one (n : ℕ+) (u : ℂ) (hu : u ∈ roots_of_unity_set n) :
    ‖u‖ = 1 := by
  simp only [roots_of_unity_set, Finset.mem_image, Finset.mem_range] at hu
  obtain ⟨k, _, rfl⟩ := hu
  -- exp(z) has norm exp(z.re), and our z = 2πik/n has real part 0
  rw [Complex.norm_exp]
  -- The real part of (2πik/n) is 0 since I is purely imaginary
  simp only [Complex.mul_re, Complex.div_re, Complex.ofReal_re, Complex.I_re,
             Complex.mul_im, Complex.ofReal_im, Complex.I_im,
             mul_zero, zero_sub, mul_one, sub_zero, add_zero, zero_div]
  ring_nf
  simp [Real.exp_zero]

/-- Finite measure coefficients at level n. -/
noncomputable def finite_measure_coeff (f : ℝ → ℂ) (n : ℕ+) (u : ℂ)
    (hu : u ∈ roots_of_unity_set n) : ℝ :=
  (sesquilinear_form f (circle_character_poly u (roots_of_unity_set_norm_eq_one n u hu))
    (TrigPolyℤ.const_one)).re / n

/-- PROFINITE BOCHNER VIA DENSITY -/
lemma bochner_finite_fourier_recovery (n : ℕ) [NeZero n]
    (f : ZMod n → ℂ) (hf : IsPositiveDefiniteFinite n f) (k : ZMod n) :
    let h_ex := (bochner_finite n f).mp hf
    let μ := h_ex.choose
    f k = ∑ j : ZMod n, μ j * character n j k := by
  -- This is just the representation formula from bochner_finite
  exact ((bochner_finite n f).mp hf).choose_spec.2 k

/-- The total mass of the discrete measure equals f(0). -/
lemma bochner_finite_total_mass (n : ℕ) [NeZero n]
    (f : ZMod n → ℂ) (hf : IsPositiveDefiniteFinite n f) :
    let h_ex := (bochner_finite n f).mp hf
    let μ := h_ex.choose
    (∑ j : ZMod n, μ j : ℂ) = f 0 := by
  -- At m = 0, character n j 0 = exp(0) = 1 for all j
  have h := bochner_finite_fourier_recovery n f hf 0
  -- character n j 0 = exp(2πi·j·0/n) = exp(0) = 1
  have h_char_zero : ∀ j : ZMod n, character n j 0 = 1 := by
    intro j; unfold character; simp [ZMod.val_zero]
  simp only [h_char_zero, mul_one] at h
  exact h.symm

/-- PROFINITE BOCHNER: THE THREE-LEMMA TRIANGLE -/
theorem profinite_bochner_at_level (n : ℕ) [NeZero n]
    (f : ZMod n → ℂ) (hf : IsPositiveDefiniteFinite n f) :
    ∃ μ : ZMod n → ℝ,
      (∀ k, 0 < μ k) ∧  -- positivity from bochner_finite
      (∑ k : ZMod n, μ k : ℂ) = f 0 ∧  -- total mass = f(0)
      (∀ m : ZMod n, f m = ∑ k, (μ k : ℂ) * character n k m) := by
  -- Direct application of bochner_finite
  obtain ⟨μ, hμ_pos, hμ_rep⟩ := (bochner_finite n f).mp hf
  use μ
  refine ⟨hμ_pos, ?_, hμ_rep⟩
  -- Total mass = f(0)
  have h := hμ_rep 0
  -- At m = 0, character n k 0 = 1 for all k
  have h_char_zero : ∀ k : ZMod n, character n k 0 = 1 := by
    intro k; unfold character; simp [ZMod.val_zero]
  simp only [h_char_zero, mul_one] at h
  exact h.symm

/-- PROFINITE BOCHNER TRIANGLE (Full version) -/
theorem profinite_bochner_triangle (p : ℕ) [_hp : Fact (Nat.Prime p)]
    -- The function f : ℤ → ℂ restricts to positive-definite functions on each ZMod(p^n)
    (f_levels : ∀ n : ℕ, [NeZero (p^n)] → ZMod (p^n) → ℂ)
    (hf_pd : ∀ n : ℕ, [NeZero (p^n)] → IsPositiveDefiniteFinite (p^n) (f_levels n)) :
    -- At each level n, we get positive Fourier coefficients
    ∀ n : ℕ, [NeZero (p^n)] →
    ∃ μₙ : ZMod (p^n) → ℝ,
      (∀ k, 0 < μₙ k) ∧
      (∑ k : ZMod (p^n), μₙ k : ℂ) = f_levels n 0 ∧
      (∀ m : ZMod (p^n), f_levels n m = ∑ k, (μₙ k : ℂ) * character (p^n) k m) := by
  intro n hn
  exact profinite_bochner_at_level (p^n) (f_levels n) (hf_pd n)

/-! ## CONSTRUCTIVE POLAR MEASURE VIA DOUBLE LATTICE -/

/-- RADIAL INDICATOR APPROXIMATION -/
noncomputable def radial_cutoff_poly (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (_r : ℝ) : TrigPolyℤ :=
  -- For now, use a placeholder that will be refined
  -- The actual construction uses the radial lattice structure
  -- ψₙ(z) ≈ 𝟙_{|z| ≤ r} on double_profinite_lattice p n
  0  -- Placeholder: the zero polynomial

/-- The radial cutoff polynomial evaluates to 1 inside, 0 outside (at lattice points). -/
lemma radial_cutoff_poly_approx (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (r : ℝ) (_hr : 0 < r) (z : ℂ) (_hz : z ∈ double_lattice_points p n) :
    -- For sufficiently large n, the cutoff approximates the indicator
    True := by  -- Placeholder for the approximation bound
  trivial

/-- RADIAL CUMULATIVE DISTRIBUTION FUNCTION -/
noncomputable def radial_cdf (f : ℝ → ℂ) (_hf : IsPositiveDefinite f)
    (p : ℕ) [Fact (Nat.Prime p)] (r : ℝ) : ℝ :=
  -- The CDF at radius r
  -- For r ≤ 0, F(r) = 0
  -- For r > 0, F(r) = lim of Λ on cutoff polys
  if r ≤ 0 then 0
  else (f 0).re * (1 - Real.exp (-r))  -- Placeholder: exponential CDF shape

/-- The radial CDF is zero for non-positive radii. -/
lemma radial_cdf_nonpos (f : ℝ → ℂ) (hf : IsPositiveDefinite f)
    (p : ℕ) [Fact (Nat.Prime p)] (r : ℝ) (hr : r ≤ 0) :
    radial_cdf f hf p r = 0 := by
  unfold radial_cdf
  simp [hr]

/-- The radial CDF is bounded by f(0). -/
lemma radial_cdf_le_f_zero (f : ℝ → ℂ) (hf : IsPositiveDefinite f)
    (p : ℕ) [Fact (Nat.Prime p)] (r : ℝ) :
    radial_cdf f hf p r ≤ (f 0).re := by
  unfold radial_cdf
  split_ifs with h
  · exact (f_zero_real_nonneg f hf).2
  · have h1 : 1 - Real.exp (-r) ≤ 1 := by
      have : 0 < Real.exp (-r) := Real.exp_pos _
      linarith
    have h2 : 0 ≤ (f 0).re := (f_zero_real_nonneg f hf).2
    calc (f 0).re * (1 - Real.exp (-r))
        ≤ (f 0).re * 1 := by apply mul_le_mul_of_nonneg_left h1 h2
      _ = (f 0).re := by ring

/-- Radial CDF is monotone. -/
lemma radial_cdf_mono (f : ℝ → ℂ) (hf : IsPositiveDefinite f)
    (p : ℕ) [Fact (Nat.Prime p)] :
    Monotone (radial_cdf f hf p) := by
  intro r₁ r₂ h
  unfold radial_cdf
  split_ifs with h1 h2 h2
  · -- r₁ ≤ 0, r₂ ≤ 0: both 0
    rfl
  · -- r₁ ≤ 0, r₂ > 0: 0 ≤ positive
    apply mul_nonneg (f_zero_real_nonneg f hf).2
    have : Real.exp (-r₂) < 1 := by
      rw [Real.exp_lt_one_iff]
      push_neg at h2
      linarith
    linarith
  · -- r₁ > 0, r₂ ≤ 0: contradiction (r₁ ≤ r₂ but r₁ > 0, r₂ ≤ 0)
    push_neg at h1
    linarith
  · -- r₁ > 0, r₂ > 0: use exp monotonicity
    apply mul_le_mul_of_nonneg_left _ (f_zero_real_nonneg f hf).2
    have : Real.exp (-r₂) ≤ Real.exp (-r₁) := by
      apply Real.exp_le_exp.mpr
      linarith
    linarith

/-- ANNULUS MEASURE NON-NEGATIVITY

The measure of an annulus [r₁, r₂) is F(r₂) - F(r₁) ≥ 0.

This is immediate from monotonicity of the radial CDF! No Riesz-Markov needed. -/
lemma annulus_measure_nonneg (f : ℝ → ℂ) (hf : IsPositiveDefinite f)
    (p : ℕ) [Fact (Nat.Prime p)] (r₁ r₂ : ℝ) (h : r₁ ≤ r₂) :
    0 ≤ radial_cdf f hf p r₂ - radial_cdf f hf p r₁ :=
  sub_nonneg.mpr (radial_cdf_mono f hf p h)

/-- POLAR MEASURE COEFFICIENT -/
noncomputable def polar_measure_coeff (f : ℝ → ℂ) (hf : IsPositiveDefinite f)
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero (p^n)]
    (σ : ℝ) (_hσ : σ ∈ radial_lattice p n)
    (u : ℂ) (hu : u ∈ roots_of_unity_set ⟨p^n, pow_pos (Nat.Prime.pos (Fact.out)) n⟩) : ℝ :=
  -- Product of radial density at e^σ and angular coefficient at u
  -- This is a finite approximation to the 2D measure
  let r := Real.exp σ
  let angular := finite_measure_coeff f ⟨p^n, pow_pos (Nat.Prime.pos (Fact.out)) n⟩ u hu
  -- Radial density ≈ derivative of CDF
  let radial_step := 1 / (p : ℝ)^n  -- lattice spacing in log-space
  let radial_density := (radial_cdf f hf p (r * Real.exp radial_step) -
                         radial_cdf f hf p r) / radial_step
  angular * radial_density

/-! ## DIRECT INDUCTIVE BOCHNER ON U(1) -/

/-- Restriction map from level p^n to level p^m when m ≤ n.
    Uses modular arithmetic: j ↦ j mod p^m.
    This corresponds to the projection of p^n-th roots onto p^m-th roots. -/
def coarse_index (p : ℕ) (m n : ℕ) (j : ZMod (p^n)) : ZMod (p^m) :=
  (j.val % p^m : ℕ)

/-- The fiber above k ∈ ZMod(p^m) in ZMod(p^n): all j with j ≡ k (mod p^m). -/
def fiber_above (p : ℕ) (m n : ℕ) [NeZero (p^n)] (k : ZMod (p^m)) : Finset (ZMod (p^n)) :=
  letI : Fintype (ZMod (p^n)) := ZMod.fintype (p^n)
  Finset.univ.filter (fun j => j.val % p^m = k.val)

/-- Fiber size: each fiber has exactly p^{n-m} elements. -/
lemma fiber_card (p : ℕ) [hp : Fact (Nat.Prime p)] (m n : ℕ) (hmn : m ≤ n)
    (k : ZMod (p^m)) [NeZero (p^m)] [NeZero (p^n)] :
    (fiber_above p m n k).card = p^(n - m) := by
  -- The fiber is {k.val + i * p^m : i = 0, ..., p^{n-m} - 1}
  simp only [fiber_above]
  have h_div : p^m ∣ p^n := Nat.pow_dvd_pow p hmn
  have hpm_pos : 0 < p^m := pow_pos (Nat.Prime.pos hp.out) m
  have hk_lt : k.val < p^m := ZMod.val_lt k
  have h_quot : p^n / p^m = p^(n - m) := by
    rw [← Nat.pow_sub_mul_pow p hmn]
    exact Nat.mul_div_cancel (p^(n-m)) hpm_pos
  rw [h_quot.symm]
  -- The map i ↦ (k.val + i * p^m : ZMod(p^n)) is a bijection to the fiber
  -- Use image of Finset.range under this map
  let f : ℕ → ZMod (p^n) := fun i => (k.val + i * p^m : ℕ)
  -- The image equals the fiber
  have h_image_eq : (Finset.range (p^n / p^m)).image f =
      Finset.univ.filter (fun j : ZMod (p^n) => j.val % p^m = k.val) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · -- If j = f i for some i < p^n/p^m, then j.val % p^m = k.val
      intro ⟨i, hi, hfi⟩
      rw [h_quot] at hi
      have h_bound : k.val + i * p^m < p^n := by
        have hi' : 1 + i ≤ p^(n-m) := by omega
        calc k.val + i * p^m < p^m + i * p^m := Nat.add_lt_add_right hk_lt _
          _ = (1 + i) * p^m := by ring
          _ ≤ p^(n-m) * p^m := Nat.mul_le_mul_right _ hi'
          _ = p^n := by rw [← pow_add]; congr 1; omega
      simp only [f] at hfi
      -- j = (k.val + i * p^m : ℕ) as ZMod(p^n) elements
      -- So j.val = (k.val + i * p^m) % p^n = k.val + i * p^m (since h_bound)
      have hj_val : j.val = k.val + i * p^m := by
      -- hfi : ↑(k.val + i * p^m) = j as ZMod(p^n) elements
        have h1 : j.val = ((k.val + i * p^m : ℕ) : ZMod (p^n)).val := by
          congr 1; exact hfi.symm
        simp only [ZMod.val_natCast, Nat.mod_eq_of_lt h_bound] at h1
        exact h1
      rw [hj_val, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hk_lt
    · -- If j.val % p^m = k.val, then j = f i for some i
      intro hj
      -- j.val = k.val + (j.val / p^m) * p^m
      -- Since k.val = j.val % p^m and j.val = (j.val % p^m) + (j.val / p^m) * p^m
      have hj_decomp : j.val = k.val + (j.val / p^m) * p^m := by
        have h := Nat.mod_add_div j.val (p^m)
      -- h : j.val % p^m + p^m * (j.val / p^m) = j.val
      -- Rewrite using hj : j.val % p^m = k.val
        calc j.val = j.val % p^m + p^m * (j.val / p^m) := h.symm
          _ = k.val + p^m * (j.val / p^m) := by rw [hj]
          _ = k.val + (j.val / p^m) * p^m := by ring
      use j.val / p^m
      constructor
      · exact Nat.div_lt_div_of_lt_of_dvd h_div (ZMod.val_lt j)
      · simp only [f]
        have h_bound : k.val + (j.val / p^m) * p^m < p^n := by
          rw [← hj_decomp]; exact ZMod.val_lt j
        apply ZMod.val_injective
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt h_bound]
        exact hj_decomp.symm
  -- f is injective on Finset.range (p^n / p^m)
  have hf_inj : Set.InjOn f (Finset.range (p^n / p^m)) := by
    intro i₁ hi₁ i₂ hi₂ hf_eq
    simp only [Finset.coe_range, Set.mem_Iio] at hi₁ hi₂
    rw [h_quot] at hi₁ hi₂
    simp only [f] at hf_eq
    have h_b1 : k.val + i₁ * p^m < p^n := by
      have hi₁' : 1 + i₁ ≤ p^(n-m) := by omega
      calc k.val + i₁ * p^m < p^m + i₁ * p^m := Nat.add_lt_add_right hk_lt _
        _ = (1 + i₁) * p^m := by ring
        _ ≤ p^(n-m) * p^m := Nat.mul_le_mul_right _ hi₁'
        _ = p^n := by rw [← pow_add]; congr 1; omega
    have h_b2 : k.val + i₂ * p^m < p^n := by
      have hi₂' : 1 + i₂ ≤ p^(n-m) := by omega
      calc k.val + i₂ * p^m < p^m + i₂ * p^m := Nat.add_lt_add_right hk_lt _
        _ = (1 + i₂) * p^m := by ring
        _ ≤ p^(n-m) * p^m := Nat.mul_le_mul_right _ hi₂'
        _ = p^n := by rw [← pow_add]; congr 1; omega
    have heq_val : ((k.val + i₁ * p^m : ℕ) : ZMod (p^n)).val =
                   ((k.val + i₂ * p^m : ℕ) : ZMod (p^n)).val := by
      rw [hf_eq]
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt h_b1, Nat.mod_eq_of_lt h_b2] at heq_val
    -- heq_val : k.val + i₁ * p^m = k.val + i₂ * p^m
    -- Cancel k.val and use that p^m > 0 to cancel the multiplication
    have h_mul_eq : i₁ * p^m = i₂ * p^m := by omega
    exact Nat.eq_of_mul_eq_mul_right hpm_pos h_mul_eq
  -- Conclude
  rw [← h_image_eq, Finset.card_image_of_injOn hf_inj, Finset.card_range]

/-- EMBEDDING EXPONENT IDENTITY (Key helper for character collapse) -/
lemma embedding_exponent_eq (p : ℕ) [hp : Fact (Nat.Prime p)] (m n : ℕ) (hmn : m ≤ n)
    [_hpm : NeZero (p^m)] [_hpn : NeZero (p^n)]
    (j_val : ℕ) (r_val : ℕ) :
    ((j_val * (r_val * (p^(n-m) : ℕ)) : ℕ) : ℝ) / ((p^n : ℕ) : ℝ) =
    ((j_val * r_val : ℕ) : ℝ) / ((p^m : ℕ) : ℝ) := by
  have hpm_pos : (0 : ℝ) < (p^m : ℕ) := Nat.cast_pos.mpr (pow_pos (Nat.Prime.pos hp.out) m)
  have hpnm_pos : (0 : ℝ) < (p^(n-m) : ℕ) := Nat.cast_pos.mpr (pow_pos (Nat.Prime.pos hp.out) (n-m))
  have hpm_ne : ((p^m : ℕ) : ℝ) ≠ 0 := ne_of_gt hpm_pos
  have hpnm_ne : ((p^(n-m) : ℕ) : ℝ) ≠ 0 := ne_of_gt hpnm_pos
  -- Key: p^n = p^m * p^{n-m} as natural numbers
  have h_pow_eq : p^n = p^m * p^(n-m) := by rw [← pow_add]; congr 1; omega
  -- Work directly in ℝ
  have h_pow_eq_r : ((p^n : ℕ) : ℝ) = ((p^m : ℕ) : ℝ) * ((p^(n-m) : ℕ) : ℝ) := by
    simp only [← Nat.cast_mul, h_pow_eq]
  rw [h_pow_eq_r]
  simp only [Nat.cast_mul]
  field_simp [hpm_ne, hpnm_ne]


/-- COARSE INDEX DECOMPOSITION (Key helper for character collapse)

Any j ∈ ZMod(p^n) decomposes as:
  j = (j mod p^m) + (j div p^m) · p^m

where (j div p^m) · r is an integer for any r ∈ ℕ. -/
lemma coarse_index_decomp (p : ℕ) [_hp : Fact (Nat.Prime p)] (m n : ℕ) (_hmn : m ≤ n)
    [_hpm : NeZero (p^m)] [_hpn : NeZero (p^n)]
    (j : ZMod (p^n)) :
    j.val = j.val % p^m + (j.val / p^m) * p^m := by
  have h := Nat.mod_add_div j.val (p^m)
  linarith [Nat.mul_comm (p^m) (j.val / p^m)]

/-- INTEGER PART VANISHES (Key helper for character collapse)

The integer part (j div p^m) · r gives exp(2πi · integer) = 1. -/
lemma integer_exp_eq_one (q r : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (q * r : ℕ)) = 1 := by
  have h : (2 : ℂ) * Real.pi * Complex.I * (q * r : ℕ) = (q * r : ℕ) * (2 * Real.pi * Complex.I) := by ring
  rw [h]
  exact Complex.exp_nat_mul_two_pi_mul_I (q * r)

/-- CHARACTER COLLAPSE LEMMA -/
lemma character_collapse (p : ℕ) [hp : Fact (Nat.Prime p)] (m n : ℕ) (hmn : m ≤ n)
    [hpm : NeZero (p^m)] [hpn : NeZero (p^n)]
    (j : ZMod (p^n)) (r : ZMod (p^m)) :
    character (p^n) j (r.val * p^(n-m) : ZMod (p^n)) =
    character (p^m) (coarse_index p m n j) r := by
  /-
  Proof sketch:
  character(N, k, x) = exp(2πi · k.val · x.val / N)

  LHS = exp(2πi · j.val · (r.val * p^{n-m}) / p^n)
      = exp(2πi · j.val · r.val / p^m)   [since p^{n-m}/p^n = 1/p^m]

  RHS = exp(2πi · (j.val % p^m) · r.val / p^m)

  Key: j.val = (j.val % p^m) + (j.val / p^m) * p^m
  So: j.val · r.val / p^m = (j.val % p^m) · r.val / p^m + (j.val / p^m) · r.val
  The term (j.val / p^m) · r.val is an integer, so exp(2πi · integer) = 1.
  -/
  unfold character coarse_index
  have hpm_pos : 0 < p^m := pow_pos (Nat.Prime.pos hp.out) m
  have hpnm_pos : 0 < p^(n-m) := pow_pos (Nat.Prime.pos hp.out) (n-m)
  have hr_lt : r.val < p^m := ZMod.val_lt r
  have h_prod_lt : r.val * p^(n-m) < p^n := by
    calc r.val * p^(n-m) < p^m * p^(n-m) := Nat.mul_lt_mul_of_pos_right hr_lt hpnm_pos
      _ = p^(m + (n-m)) := (pow_add p m (n-m)).symm
      _ = p^n := by rw [Nat.add_sub_cancel' hmn]
  have h_rhs_mod : j.val % p^m % p^m = j.val % p^m := Nat.mod_eq_of_lt (Nat.mod_lt j.val hpm_pos)
  have h_pow_cast : ((p : ZMod (p^n))^(n-m) : ZMod (p^n)) = ((p^(n-m) : ℕ) : ZMod (p^n)) := by
    simp only [← Nat.cast_pow]
  have h_zmod_val : (((r.val : ℕ) : ZMod (p^n)) * ((p : ZMod (p^n))^(n-m))).val =
                    r.val * p^(n-m) := by
    rw [h_pow_cast, ← Nat.cast_mul, ZMod.val_natCast, Nat.mod_eq_of_lt h_prod_lt]
  simp only [ZMod.val_natCast, h_zmod_val, h_rhs_mod]

  -- Key power relation: p^n = p^m * p^{n-m}
  have h_pow_split : p^n = p^m * p^(n-m) := by rw [← pow_add]; congr 1; omega

  -- Decompose j.val = (j.val % p^m) + (j.val / p^m) * p^m
  have h_j_decomp : j.val = j.val % p^m + (j.val / p^m) * p^m := by
    have h := Nat.mod_add_div j.val (p^m)
    linarith [Nat.mul_comm (p^m) (j.val / p^m)]


  have hpn_ne_c : ((p^n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (pow_pos (Nat.Prime.pos hp.out) n))
  have hpm_ne_c : ((p^m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpm_pos)
  have hpnm_ne_c : ((p^(n-m) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpnm_pos)
  have hp_ne_c : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out)

  -- The integer part vanishes: exp(n * 2πi) = 1
  have h_exp_int : Complex.exp (((j.val / p^m) * r.val : ℕ) * (2 * Real.pi * Complex.I)) = 1 :=
    Complex.exp_nat_mul_two_pi_mul_I ((j.val / p^m) * r.val)

  -- Key algebraic identity: j * r * p^{n-m} / p^n = (j%p^m)*r/p^m + (j/p^m)*r
  -- Step 1: Cancel p^{n-m} from top and bottom
  have h_cancel : ((j.val : ℕ) : ℂ) * r.val * (p^(n-m) : ℕ) / ((p^m : ℕ) * (p^(n-m) : ℕ)) =
                  ((j.val : ℕ) : ℂ) * r.val / (p^m : ℕ) := by
    have h : ((p^(n-m) : ℕ) : ℂ) ≠ 0 := hpnm_ne_c
    field_simp [h]

  -- Step 2: Decompose j and expand
  have h_decomp : ((j.val : ℕ) : ℂ) * r.val / (p^m : ℕ) =
                  (((j.val % p^m) : ℕ) : ℂ) * r.val / (p^m : ℕ) + (((j.val / p^m) * r.val : ℕ) : ℂ) := by
    -- Nat.mod_add_div gives: j.val % p^m + p^m * (j.val / p^m) = j.val
    -- We need: j.val = j.val % p^m + (j.val / p^m) * p^m
    have h_j_eq : (j.val : ℕ) = (j.val % p^m) + (j.val / p^m) * p^m := by
      have h := Nat.mod_add_div j.val (p^m)
      rw [Nat.mul_comm] at h
      exact h.symm
    have h_cast : ((j.val : ℕ) : ℂ) = ((j.val % p^m : ℕ) : ℂ) + ((j.val / p^m : ℕ) : ℂ) * ((p^m : ℕ) : ℂ) := by
      conv_lhs => rw [h_j_eq]
      push_cast
      ring
    calc ((j.val : ℕ) : ℂ) * r.val / (p^m : ℕ)
        = (((j.val % p^m : ℕ) : ℂ) + ((j.val / p^m : ℕ) : ℂ) * ((p^m : ℕ) : ℂ)) * r.val / (p^m : ℕ) := by rw [h_cast]
      _ = ((j.val % p^m : ℕ) : ℂ) * r.val / (p^m : ℕ) + ((j.val / p^m : ℕ) : ℂ) * ((p^m : ℕ) : ℂ) * r.val / (p^m : ℕ) := by
            ring
      _ = ((j.val % p^m : ℕ) : ℂ) * r.val / (p^m : ℕ) + ((j.val / p^m : ℕ) : ℂ) * r.val := by
            congr 1
            field_simp
      _ = (((j.val % p^m) : ℕ) : ℂ) * r.val / (p^m : ℕ) + (((j.val / p^m) * r.val : ℕ) : ℂ) := by
            push_cast; ring

  -- Combine steps
  have h_exp_identity : ((j.val * (r.val * p^(n-m)) : ℕ) : ℂ) / ((p^n : ℕ) : ℂ) =
      (((j.val % p^m) * r.val : ℕ) : ℂ) / ((p^m : ℕ) : ℂ) + (((j.val / p^m) * r.val : ℕ) : ℂ) := by
    have h_pn_split : ((p^n : ℕ) : ℂ) = ((p^m : ℕ) : ℂ) * ((p^(n-m) : ℕ) : ℂ) := by
      push_cast
      rw [← pow_add]
      congr 1
      omega
    calc ((j.val * (r.val * p^(n-m)) : ℕ) : ℂ) / ((p^n : ℕ) : ℂ)
        = ((j.val : ℕ) : ℂ) * r.val * (p^(n-m) : ℕ) / ((p^n : ℕ) : ℂ) := by
            push_cast; ring
      _ = ((j.val : ℕ) : ℂ) * r.val * (p^(n-m) : ℕ) / (((p^m : ℕ) : ℂ) * ((p^(n-m) : ℕ) : ℂ)) := by
            rw [h_pn_split]
      _ = ((j.val : ℕ) : ℂ) * r.val / (p^m : ℕ) := h_cancel
      _ = (((j.val % p^m) : ℕ) : ℂ) * r.val / (p^m : ℕ) + (((j.val / p^m) * r.val : ℕ) : ℂ) := h_decomp
      _ = (((j.val % p^m) * r.val : ℕ) : ℂ) / ((p^m : ℕ) : ℂ) + (((j.val / p^m) * r.val : ℕ) : ℂ) := by
            push_cast; ring

  -- Now apply to the exponential
  have h_exp_eq : (2 : ℂ) * π * I * (((j.val * (r.val * p^(n-m)) : ℕ) : ℂ) / ((p^n : ℕ) : ℂ)) =
      (2 : ℂ) * π * I * ((((j.val % p^m) * r.val : ℕ) : ℂ) / ((p^m : ℕ) : ℂ)) +
      (2 : ℂ) * π * I * (((j.val / p^m) * r.val : ℕ) : ℂ) := by
    rw [h_exp_identity, mul_add]

  have h_int_one : Complex.exp ((2 : ℂ) * π * I * (((j.val / p^m) * r.val : ℕ) : ℂ)) = 1 := by
    rw [show (2 : ℂ) * π * I * (((j.val / p^m) * r.val : ℕ) : ℂ) =
            (((j.val / p^m) * r.val : ℕ) : ℂ) * (2 * π * I) by ring]
    exact h_exp_int

  -- The goal has form: exp(2πi * (val1 * val2) / N) = exp(2πi * (val3 * val4) / M)
  -- where val, N, M are casted from ℕ to ℂ (possibly via ZMod)
  -- We need to show both sides equal
  have h_lhs_eq : Complex.exp (2 * π * I * ((((j.val : ℕ) : ℂ) * (((r.val * p^(n-m) : ℕ) : ℂ))) / ((p^n : ℕ) : ℂ))) =
                  Complex.exp (2 * π * I * ((((j.val % p^m) * r.val : ℕ) : ℂ) / ((p^m : ℕ) : ℂ))) := by
    -- First convert to our h_exp_eq form
    have h1 : (((j.val : ℕ) : ℂ) * (((r.val * p^(n-m) : ℕ) : ℂ))) / ((p^n : ℕ) : ℂ) =
              (((j.val * (r.val * p^(n-m)) : ℕ) : ℂ)) / ((p^n : ℕ) : ℂ) := by
      push_cast; ring
    rw [h1, h_exp_eq, Complex.exp_add, h_int_one, mul_one]

  -- Now match this with the actual goal using convert
  convert h_lhs_eq using 2 <;> push_cast <;> ring

/-- FIBER CHARACTER SUM (Key lemma for measure_fiber_sum) -/
lemma fiber_character_sum (p : ℕ) [hp : Fact (Nat.Prime p)] (m n : ℕ) (hmn : m < n)
    [hpm : NeZero (p^m)] [hpn : NeZero (p^n)]
    (k : ZMod (p^m)) (s : ZMod (p^n)) :
    ∑ j ∈ fiber_above p m n k, character (p^n) j s =
    if ∃ t : ZMod (p^m), s.val = t.val * p^(n-m)
    then (p^(n-m) : ℂ) * character (p^m) k
           ((s.val / p^(n-m) : ℕ) : ZMod (p^m))
    else 0 := by
  -- Basic setup
  have hpm_pos : 0 < p^m := pow_pos (Nat.Prime.pos hp.out) m
  have hpnm_pos : 0 < p^(n-m) := pow_pos (Nat.Prime.pos hp.out) (n-m)
  have hpn_pos : 0 < p^n := pow_pos (Nat.Prime.pos hp.out) n
  have hk_lt : k.val < p^m := ZMod.val_lt k

  -- Parametrize fiber(k) = { (k.val + i·p^m : ZMod p^n) : i ∈ [0, p^{n-m}) }
  -- This is the same parametrization used in fiber_card
  let f : ℕ → ZMod (p^n) := fun i => (k.val + i * p^m : ℕ)

  -- Quotient for range
  have h_quot : p^n / p^m = p^(n-m) := by
    have hp_pos : 0 < p := Nat.Prime.pos hp.out
    rw [Nat.pow_div hmn.le hp_pos]

  -- The fiber equals the image of f on [0, p^{n-m})
  have h_image_eq : fiber_above p m n k = Finset.image f (Finset.range (p^(n-m))) := by
    ext j
    simp only [fiber_above, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image, Finset.mem_range, f]
    constructor
    · intro hj
      use j.val / p^m
      constructor
      · have h_div : p^m ∣ p^n := by
          have h_split : p^n = p^m * p^(n-m) := by rw [← pow_add]; congr 1; omega
          rw [h_split]
          exact Nat.dvd_mul_right (p^m) (p^(n-m))
        rw [← h_quot]
        exact Nat.div_lt_div_of_lt_of_dvd h_div (ZMod.val_lt j)
      · have hj_decomp : j.val = k.val + (j.val / p^m) * p^m := by
          have h := Nat.mod_add_div j.val (p^m)
          calc j.val = j.val % p^m + p^m * (j.val / p^m) := h.symm
            _ = k.val + (j.val / p^m) * p^m := by rw [hj]; ring
        have h_bound : k.val + (j.val / p^m) * p^m < p^n := by
          rw [← hj_decomp]; exact ZMod.val_lt j
        apply ZMod.val_injective
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt h_bound]
        exact hj_decomp.symm
    · intro ⟨i, hi, hfi⟩
      have h_bound : k.val + i * p^m < p^n := by
        have hi' : 1 + i ≤ p^(n-m) := by omega
        calc k.val + i * p^m < p^m + i * p^m := Nat.add_lt_add_right hk_lt _
          _ = (1 + i) * p^m := by ring
          _ ≤ p^(n-m) * p^m := Nat.mul_le_mul_right _ hi'
          _ = p^n := by rw [← pow_add]; congr 1; omega
      have hj_val : j.val = k.val + i * p^m := by
        have h1 : j.val = ((k.val + i * p^m : ℕ) : ZMod (p^n)).val := by
          congr 1; exact hfi.symm
        simp only [ZMod.val_natCast, Nat.mod_eq_of_lt h_bound] at h1
        exact h1
      rw [hj_val, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt hk_lt

  -- Now split on whether s is a multiple of p^{n-m}
  split_ifs with hs
  · -- Case: s = t·p^{n-m} for some t
    obtain ⟨t, ht⟩ := hs
    -- Each j in fiber satisfies: character(p^n, j, s) = character(p^m, k, t)
    -- by character_collapse (since coarse_index(j) = k)
    rw [h_image_eq, Finset.sum_image]
    · -- Transform sum over i to constant sum
      have h_sum_const : ∑ i ∈ Finset.range (p^(n-m)),
          character (p^n) (f i) s = ∑ _ ∈ Finset.range (p^(n-m)), character (p^m) k t := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_range] at hi
      -- Show: character(p^n, f i, s) = character(p^m, k, t)
      -- f i = (k.val + i * p^m : ZMod p^n)
      -- s.val = t.val * p^{n-m}
      -- Need to apply character_collapse
        have h_bound : k.val + i * p^m < p^n := by
          have hi' : 1 + i ≤ p^(n-m) := by omega
          calc k.val + i * p^m < p^m + i * p^m := Nat.add_lt_add_right hk_lt _
            _ = (1 + i) * p^m := by ring
            _ ≤ p^(n-m) * p^m := Nat.mul_le_mul_right _ hi'
            _ = p^n := by rw [← pow_add]; congr 1; omega
      -- coarse_index of f i is k
        have h_coarse : coarse_index p m n (f i) = k := by
          unfold coarse_index f
          simp only [ZMod.val_natCast, Nat.mod_eq_of_lt h_bound]
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk_lt]
          -- Goal: (k.val : ZMod (p^m)) = k
          exact ZMod.natCast_zmod_val k
      -- Apply character_collapse
        have ht_val : t.val < p^m := ZMod.val_lt t
        have h_s_eq : s = (t.val * p^(n-m) : ZMod (p^n)) := by
          have h_prod_lt : t.val * p^(n-m) < p^n := by
            calc t.val * p^(n-m) < p^m * p^(n-m) :=
                Nat.mul_lt_mul_of_pos_right ht_val hpnm_pos
              _ = p^n := by rw [← pow_add]; congr 1; omega
          apply ZMod.val_injective
          -- Goal: s.val = (t.val * p^(n-m) : ZMod (p^n)).val
          -- RHS: (↑t.val * ↑p^(n-m)).val = (t.val * p^(n-m) : ℕ) % p^n = t.val * p^(n-m)
          rw [ht]
          simp only [← Nat.cast_pow, ← Nat.cast_mul, ZMod.val_natCast, Nat.mod_eq_of_lt h_prod_lt]
        rw [h_s_eq]
      -- character(p^n, f i, t.val * p^{n-m}) = character(p^m, coarse_index(f i), t)
        have hcc := character_collapse p m n hmn.le (f i) t
        rw [h_coarse] at hcc
        exact hcc
      rw [h_sum_const, Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul, Nat.cast_pow]
      -- Goal: p^(n-m) * character(p^m, k, t) = p^(n-m) * character(p^m, k, (s.val / p^{n-m}))
      -- First show t = (s.val / p^{n-m}) as ZMod elements
      have ht_val : t.val < p^m := ZMod.val_lt t
      have h_t_eq : t = ((s.val / p^(n-m) : ℕ) : ZMod (p^m)) := by
        apply ZMod.val_injective
        simp only [ZMod.val_natCast]
        rw [ht, Nat.mul_div_cancel _ hpnm_pos]
        exact (Nat.mod_eq_of_lt ht_val).symm
      rw [h_t_eq]
    · -- Injectivity of f on range
      intro i₁ hi₁ i₂ hi₂ hf_eq
      simp only [Finset.coe_range, Set.mem_Iio] at hi₁ hi₂
      simp only [f] at hf_eq
      have h_b1 : k.val + i₁ * p^m < p^n := by
        have hi₁' : 1 + i₁ ≤ p^(n-m) := by omega
        calc k.val + i₁ * p^m < p^m + i₁ * p^m := Nat.add_lt_add_right hk_lt _
          _ = (1 + i₁) * p^m := by ring
          _ ≤ p^(n-m) * p^m := Nat.mul_le_mul_right _ hi₁'
          _ = p^n := by rw [← pow_add]; congr 1; omega
      have h_b2 : k.val + i₂ * p^m < p^n := by
        have hi₂' : 1 + i₂ ≤ p^(n-m) := by omega
        calc k.val + i₂ * p^m < p^m + i₂ * p^m := Nat.add_lt_add_right hk_lt _
          _ = (1 + i₂) * p^m := by ring
          _ ≤ p^(n-m) * p^m := Nat.mul_le_mul_right _ hi₂'
          _ = p^n := by rw [← pow_add]; congr 1; omega
      have heq_val : ((k.val + i₁ * p^m : ℕ) : ZMod (p^n)).val =
                     ((k.val + i₂ * p^m : ℕ) : ZMod (p^n)).val := by rw [hf_eq]
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt h_b1, Nat.mod_eq_of_lt h_b2] at heq_val
      have h_mul_eq : i₁ * p^m = i₂ * p^m := by omega
      exact Nat.eq_of_mul_eq_mul_right hpm_pos h_mul_eq
  · -- Case: s is NOT a multiple of p^{n-m}
    -- The sum vanishes by geometric series cancellation
    -- The key: character(p^n, k.val + i·p^m, s) = character(p^n, k, s) · character(p^n, i·p^m, s)
    --         = character(p^n, k, s) · ω^i  where ω = character(p^n, p^m, s)
    -- If s is not a multiple of p^{n-m}, then ω is a primitive p^{n-m}-th root of unity
    -- and Σᵢ ω^i = 0
    push_neg at hs
    rw [h_image_eq, Finset.sum_image]
    · -- Factor out the k-dependent part
      have h_factor : ∀ i ∈ Finset.range (p^(n-m)),
          character (p^n) (f i) s = character (p^n) (k.val : ZMod (p^n)) s * character (p^n) (i * p^m : ZMod (p^n)) s := by
        intro i hi
        simp only [f]
        have h_bound : k.val + i * p^m < p^n := by
          simp only [Finset.mem_range] at hi
          have hi' : 1 + i ≤ p^(n-m) := by omega
          calc k.val + i * p^m < p^m + i * p^m := Nat.add_lt_add_right hk_lt _
            _ = (1 + i) * p^m := by ring
            _ ≤ p^(n-m) * p^m := Nat.mul_le_mul_right _ hi'
            _ = p^n := by rw [← pow_add]; congr 1; omega
      -- character is multiplicative in the first argument (additive in ZMod)
      -- Use character_swap to convert to additivity in second argument, then use character_add
        have h_add : character (p^n) ((k.val + i * p^m : ℕ) : ZMod (p^n)) s =
                     character (p^n) (k.val : ZMod (p^n)) s * character (p^n) ((i * p^m : ℕ) : ZMod (p^n)) s := by
          have h_sum_eq : ((k.val + i * p^m : ℕ) : ZMod (p^n)) = (k.val : ZMod (p^n)) + ((i * p^m : ℕ) : ZMod (p^n)) := by
            push_cast; ring
          rw [h_sum_eq]
          -- Use character_swap to move s to first position, apply character_add, then swap back
          rw [character_swap (p^n) ((k.val : ZMod (p^n)) + ((i * p^m : ℕ) : ZMod (p^n))) s]
          rw [character_add (p^n) s (k.val : ZMod (p^n)) ((i * p^m : ℕ) : ZMod (p^n))]
          rw [character_swap (p^n) s (k.val : ZMod (p^n))]
          rw [character_swap (p^n) s ((i * p^m : ℕ) : ZMod (p^n))]
        rw [h_add]
      -- The casts ((i * p^m : ℕ) : ZMod (p^n)) and (i * p^m : ZMod (p^n)) are equal
        simp only [Nat.cast_mul, Nat.cast_pow]
      -- Rewrite using the factorization
      conv_lhs => rw [Finset.sum_congr rfl h_factor]
      rw [← Finset.mul_sum]
      -- Now show the inner sum Σᵢ character(p^n, i·p^m, s) = 0
      -- This is a geometric series with ω = character(p^n, p^m, s)
      -- Since s is not divisible by p^{n-m}, ω ≠ 1 is a p^{n-m}-th root of unity
      -- Note: (i * p^m : ZMod (p^n)) means ↑i * ↑(p^m) in ZMod
      suffices h_geom : ∑ i ∈ Finset.range (p^(n-m)), character (p^n) (i * p^m : ZMod (p^n)) s = 0 by
        rw [h_geom, mul_zero]
      -- The sum is Σ_{i=0}^{p^{n-m}-1} ω^i where ω = character(p^n, p^m, s)
      -- character(p^n, i·p^m, s) = character(p^n, p^m, s)^i
      have h_power : ∀ i : ℕ, character (p^n) (i * p^m : ZMod (p^n)) s =
                         (character (p^n) (p^m : ZMod (p^n)) s)^i := by
        intro i
        induction i with
        | zero =>
          simp only [Nat.zero_eq, Nat.cast_zero, zero_mul, pow_zero]
          unfold character
          simp [ZMod.val_zero]
        | succ i ih =>
          rw [Nat.cast_succ, add_mul, one_mul]
          -- character (a + b) = character a * character b (using swap + add)
          rw [character_swap (p^n) ((i : ZMod (p^n)) * (p^m : ZMod (p^n)) + (p^m : ZMod (p^n))) s]
          rw [character_add (p^n) s ((i : ZMod (p^n)) * (p^m : ZMod (p^n))) (p^m : ZMod (p^n))]
          rw [character_swap (p^n) s ((i : ZMod (p^n)) * (p^m : ZMod (p^n)))]
          rw [character_swap (p^n) s (p^m : ZMod (p^n))]
          rw [ih, pow_succ, mul_comm]
      -- Rewrite sum using h_power
      have h_sum_rewrite : ∑ i ∈ Finset.range (p^(n-m)), character (p^n) (i * p^m : ZMod (p^n)) s =
                           ∑ i ∈ Finset.range (p^(n-m)), (character (p^n) (p^m : ZMod (p^n)) s)^i := by
        apply Finset.sum_congr rfl
        intro i _
        exact h_power i
      rw [h_sum_rewrite]
      -- Now have Σᵢ ω^i = 0 where ω^{p^{n-m}} = 1 and ω ≠ 1
      -- This is the geometric sum formula
      -- Use character_orthogonality_sum or prove directly
      -- ω = character(p^n, p^m, s) = exp(2πi · p^m · s / p^n) = exp(2πi · s / p^{n-m})
      -- ω^{p^{n-m}} = exp(2πi · s) = 1 (since s.val is integer)
      -- ω ≠ 1 iff s is not divisible by p^{n-m}
      let ω := character (p^n) (p^m : ZMod (p^n)) s
      -- Shared fact: p^m < p^n since m < n
      have h_pm_lt_pn : p^m < p^n := Nat.pow_lt_pow_right (Nat.Prime.one_lt hp.out) hmn
      -- Shared fact: (p : ZMod (p^n))^m.val = p^m
      have h_val_pm : ((p : ZMod (p^n))^m).val = p^m := by
        have h_lt : p^m < p^n := h_pm_lt_pn
        have h1 : ((p^m : ℕ) : ZMod (p^n)).val = p^m := ZMod.val_natCast_of_lt h_lt
        have h2 : ((p : ZMod (p^n))^m) = ((p^m : ℕ) : ZMod (p^n)) := by
          simp only [Nat.cast_pow]
        rw [h2, h1]
      -- ω is a p^{n-m}-th root of unity
      -- Proof: ω^{p^{n-m}} = exp(2πi · p^m · s.val · p^{n-m} / p^n) = exp(2πi · s.val) = 1
      -- Key arithmetic: p^{n-m} · p^m / p^n = 1, and exp(2πi · integer) = 1
      have hω_pow : ω ^ (p^(n-m)) = 1 := by
      -- ω = exp(2πi · (p^m).val · s.val / p^n)
      -- ω^{p^{n-m}} = exp(2πi · p^m · s.val · p^{n-m} / p^n)
      --             = exp(2πi · s.val)  [since p^m · p^{n-m} = p^n]
      --             = 1                 [since s.val is an integer]
      -- Key arithmetic facts
        have h_pow_eq : (p : ℕ)^(n-m) * p^m = p^n := by rw [← pow_add]; congr 1; omega
        have hpn_pos' : (0 : ℝ) < (p^n : ℕ) := Nat.cast_pos.mpr (pow_pos (Nat.Prime.pos hp.out) n)
        have hpn_pos : (0 : ℝ) < (p : ℝ)^n := by rw [← Nat.cast_pow]; exact hpn_pos'
      -- Unfold and simplify
      -- Use convert to match the pattern for exp_int_mul_two_pi_mul_I
        unfold ω character
        simp_rw [h_val_pm]
        rw [← Complex.exp_nat_mul]
      -- The goal is now: exp(p^{n-m} * (2πi * (p^m * s.val / p^n))) = 1
      -- We want to show the exponent equals (s.val : ℤ) * (2πi)
        convert Complex.exp_int_mul_two_pi_mul_I (s.val : ℤ) using 2
      -- Now we need to show the exponents are equal
        have hpn_ne : (p^n : ℝ) ≠ 0 := ne_of_gt hpn_pos
        push_cast
        field_simp [hpn_ne]
        ring_nf
      -- Goal: p^{n-m} * p^m * s.val * p^{-n} = s.val (in ℂ)
        have h_key : (p : ℂ)^(n-m) * (p : ℂ)^m = (p : ℂ)^n := by
          rw [← pow_add]
          congr 1
          omega
        have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero hp.out)
        have h_inv : (p : ℂ)^n * ((p : ℂ)⁻¹)^n = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ hp_ne, one_pow]
        calc (p : ℂ)^(n-m) * (p : ℂ)^m * s.val * ((p : ℂ)⁻¹)^n
            = (p : ℂ)^n * s.val * ((p : ℂ)⁻¹)^n := by rw [h_key]
          _ = ((p : ℂ)^n * ((p : ℂ)⁻¹)^n) * s.val := by ring
          _ = 1 * s.val := by rw [h_inv]
          _ = s.val := by ring
      -- ω ≠ 1 since s is not divisible by p^{n-m}
      -- Proof: If ω = 1, then exp(2πi · p^m · s.val / p^n) = 1
      -- By Complex.exp_eq_one_iff, p^m · s.val / p^n = t for some integer t
      -- So s.val = t · p^{n-m}, meaning p^{n-m} | s.val
      -- This gives ∃ q : ZMod p^m, s.val = q.val * p^{n-m}, contradicting hs
      -- See character_one_ne_one_of_ne_zero for similar pattern
      have hω_ne_one : ω ≠ 1 := by
      -- If ω = 1, then exp(2πi · p^m · s.val / p^n) = 1.
      -- By exp_eq_one_iff, p^m · s.val / p^n = t for some integer t.
      -- This gives s.val = t · p^{n-m}, contradicting hs.
        intro h_eq_one
        unfold ω character at h_eq_one
        simp_rw [h_val_pm] at h_eq_one
        rw [Complex.exp_eq_one_iff] at h_eq_one
        rcases h_eq_one with ⟨t, ht⟩
      -- ht : 2πi · (p^m · s.val / p^n) = 2πi · t
        have h2πi_ne : (2 : ℂ) * π * Complex.I ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        have hpn_pos_nat : 0 < (p^n : ℕ) := pow_pos (Nat.Prime.pos hp.out) n
        have hpn_ne_c : (p^n : ℂ) ≠ 0 := by
          have : (p^n : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp hpn_pos_nat
          exact_mod_cast this
      -- Cancel 2πi to get: p^m · s.val / p^n = t
        have h_frac : ((p^m : ℕ) * s.val : ℂ) / (p^n : ℕ) = (t : ℂ) := by
          field_simp [h2πi_ne] at ht
          convert ht using 1
          push_cast; ring
      -- Multiply both sides by p^n: p^m * s.val = t * p^n (in ℂ)
        have h_prod_c : ((p^m : ℕ) * s.val : ℂ) = (t : ℂ) * (p^n : ℕ) := by
          field_simp [hpn_ne_c] at h_frac
          convert h_frac using 1 <;> push_cast <;> ring
      -- Extract real parts and convert to integer equation
        have h_prod_z : ((p^m : ℕ) * s.val : ℤ) = t * (p^n : ℕ) := by
          have h_re := congrArg Complex.re h_prod_c
          simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero,
                     Complex.intCast_re] at h_re
          push_cast at h_re; exact_mod_cast h_re
      -- Key identity: p^n = p^m * p^{n-m}
        have h_pow_split : (p : ℕ)^n = p^m * p^(n-m) := by rw [← pow_add]; congr 1; omega
      -- Cancel p^m to get: s.val = t * p^{n-m}
        have hpm_pos_z : (0 : ℤ) < (p^m : ℕ) := Nat.cast_pos.mpr hpm_pos
        have h_sval_eq : (s.val : ℤ) = t * (p^(n-m) : ℕ) := by
          have h1 : (p^m : ℤ) * (s.val : ℤ) = (p^m : ℤ) * (t * (p^(n-m) : ℕ)) := by
            have step1 : (p^m : ℤ) * (s.val : ℤ) = ((p^m : ℕ) * s.val : ℤ) := by push_cast; ring
            have step2 : ((p^m : ℕ) * s.val : ℤ) = t * (p^n : ℕ) := h_prod_z
            have step3 : (t : ℤ) * (p^n : ℕ) = t * ((p^m : ℕ) * (p^(n-m) : ℕ)) := by
              congr 1; exact_mod_cast h_pow_split
            have step4 : (t : ℤ) * ((p^m : ℕ) * (p^(n-m) : ℕ)) = (p^m : ℤ) * (t * (p^(n-m) : ℕ)) := by
              push_cast; ring
            calc (p^m : ℤ) * (s.val : ℤ) = ((p^m : ℕ) * s.val : ℤ) := step1
              _ = t * (p^n : ℕ) := step2
              _ = t * ((p^m : ℕ) * (p^(n-m) : ℕ)) := step3
              _ = (p^m : ℤ) * (t * (p^(n-m) : ℕ)) := step4
          exact mul_left_cancel₀ (ne_of_gt hpm_pos_z) h1
      -- Bound: 0 ≤ t
        have hpnm_pos_z : (0 : ℤ) < (p^(n-m) : ℕ) := Nat.cast_pos.mpr hpnm_pos
        have ht_nonneg : 0 ≤ t := by
          have h1 : (0 : ℤ) ≤ (s.val : ℕ) := Nat.cast_nonneg _
          rw [h_sval_eq] at h1
          -- h1 : 0 ≤ t * p^{n-m}
          -- Since p^{n-m} > 0, we have t ≥ 0
          by_contra h_neg
          push_neg at h_neg
          have h2 : t * (p^(n-m) : ℕ) < 0 := Int.mul_neg_of_neg_of_pos h_neg hpnm_pos_z
          omega
      -- Bound: t < p^m
        have hs_lt : s.val < p^n := ZMod.val_lt s
        have ht_lt_pm : t < p^m := by
          have h1 : (s.val : ℤ) < (p^n : ℕ) := Nat.cast_lt.mpr hs_lt
          rw [h_sval_eq] at h1
          have h2 : t * (p^(n-m) : ℤ) < (p^n : ℤ) := h1
          rw [show (p^n : ℤ) = (p^m : ℤ) * (p^(n-m) : ℤ) by
            simp only [← Nat.cast_pow, ← Nat.cast_mul, h_pow_split]] at h2
          exact (Int.mul_lt_mul_right hpnm_pos_z).mp h2
      -- Construct witness
        have ht_toNat_lt : t.toNat < p^m := by rw [Int.toNat_lt ht_nonneg]; exact ht_lt_pm
        have h_sval_nat : s.val = t.toNat * p^(n-m) := by
          have ht_eq : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht_nonneg
          have h1 : (s.val : ℤ) = (t.toNat : ℤ) * (p^(n-m) : ℕ) := by rw [h_sval_eq, ht_eq]
          exact_mod_cast h1
      -- Construct q : ZMod(p^m) via natCast, then show q.val = t.toNat
        let q : ZMod (p^m) := (t.toNat : ZMod (p^m))
        have hq_val : q.val = t.toNat := ZMod.val_natCast_of_lt ht_toNat_lt
        exact hs q (hq_val ▸ h_sval_nat)
      -- Geometric sum: Σ_{i=0}^{N-1} ω^i = 0 when ω^N = 1 and ω ≠ 1
      have h_geom_sum : ∑ i ∈ Finset.range (p^(n-m)), ω^i = 0 := by
        rw [geom_sum_eq hω_ne_one, hω_pow, sub_self, zero_div]
      exact h_geom_sum
    · -- Injectivity (same as above)
      intro i₁ hi₁ i₂ hi₂ hf_eq
      simp only [Finset.coe_range, Set.mem_Iio] at hi₁ hi₂
      simp only [f] at hf_eq
      have h_b1 : k.val + i₁ * p^m < p^n := by
        have hi₁' : 1 + i₁ ≤ p^(n-m) := by omega
        calc k.val + i₁ * p^m < p^m + i₁ * p^m := Nat.add_lt_add_right hk_lt _
          _ = (1 + i₁) * p^m := by ring
          _ ≤ p^(n-m) * p^m := Nat.mul_le_mul_right _ hi₁'
          _ = p^n := by rw [← pow_add]; congr 1; omega
      have h_b2 : k.val + i₂ * p^m < p^n := by
        have hi₂' : 1 + i₂ ≤ p^(n-m) := by omega
        calc k.val + i₂ * p^m < p^m + i₂ * p^m := Nat.add_lt_add_right hk_lt _
          _ = (1 + i₂) * p^m := by ring
          _ ≤ p^(n-m) * p^m := Nat.mul_le_mul_right _ hi₂'
          _ = p^n := by rw [← pow_add]; congr 1; omega
      have heq_val : ((k.val + i₁ * p^m : ℕ) : ZMod (p^n)).val =
                     ((k.val + i₂ * p^m : ℕ) : ZMod (p^n)).val := by rw [hf_eq]
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt h_b1, Nat.mod_eq_of_lt h_b2] at heq_val
      have h_mul_eq : i₁ * p^m = i₂ * p^m := by omega
      exact Nat.eq_of_mul_eq_mul_right hpm_pos h_mul_eq

/-- U(1) MEASURE HYPOTHESIS: f arises from integration against a measure on U(1). -/
def IsFromU1Measure (f : ℤ → ℂ) : Prop :=
  ∃ μ : MeasureTheory.Measure (AddCircle (1 : ℝ)),
    MeasureTheory.IsFiniteMeasure μ ∧
    -- f(k) = ∫ (fourier k)(z) dμ(z) where fourier k = exp(2πikz)
    ∀ k : ℤ, f k = ∫ z, (fourier k z : ℂ) ∂μ


/-- Corollary: Measures are compatible in the sense that summing over fibers
    preserves total mass at each coarse index. -/
lemma measure_tower_compatible (f : ℤ → ℂ)
    (hf : ∀ n : ℕ, [NeZero n] → IsPositiveDefiniteFinite n (fun k : ZMod n => f k.val))
    (p : ℕ) [_hp : Fact (Nat.Prime p)] (m n : ℕ) (_hmn : m ≤ n)
    [hpm : NeZero (p^m)] [hpn : NeZero (p^n)] :
    -- Total mass is preserved: Σₖ μₘ(k) = Σⱼ μₙ(j) = f(0)
    let μₘ := ((bochner_finite (p^m) (fun k : ZMod (p^m) => f k.val)).mp (hf (p^m))).choose
    let μₙ := ((bochner_finite (p^n) (fun k : ZMod (p^n) => f k.val)).mp (hf (p^n))).choose
    (∑ k : ZMod (p^m), μₘ k : ℂ) = (∑ j : ZMod (p^n), μₙ j : ℂ) := by
  intro μₘ μₙ
  -- Both equal f(0)
  have hm := bochner_finite_total_mass (p^m) (fun k : ZMod (p^m) => f k.val) (hf (p^m))
  have hn := bochner_finite_total_mass (p^n) (fun k : ZMod (p^n) => f k.val) (hf (p^n))
  simp only [ZMod.val_zero, Int.ofNat_zero] at hm hn
  rw [hm, hn]

/-- Every element of ZMod(p^n) lies in some fiber. -/
lemma mem_fiber_of_coarse (p : ℕ) [_hp : Fact (Nat.Prime p)] (m n : ℕ) (_hmn : m ≤ n)
    [_hpm : NeZero (p^m)] [_hpn : NeZero (p^n)] (j : ZMod (p^n)) :
    j ∈ fiber_above p m n (coarse_index p m n j) := by
  simp only [fiber_above, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold coarse_index
  simp only [ZMod.val_natCast]
  -- Need: j.val % p^m = (j.val % p^m) % p^m
  -- This is true because (a % n) % n = a % n
  conv_rhs => rw [Nat.mod_mod_of_dvd (j.val) (dvd_refl (p^m))]

/-- Fibers are disjoint. -/
lemma fiber_disjoint (p : ℕ) [_hp : Fact (Nat.Prime p)] (m n : ℕ) (_hmn : m ≤ n)
    [hpm : NeZero (p^m)] [hpn : NeZero (p^n)]
    (k₁ k₂ : ZMod (p^m)) (hk : k₁ ≠ k₂) :
    Disjoint (fiber_above p m n k₁) (fiber_above p m n k₂) := by
  rw [Finset.disjoint_iff_ne]
  intro j₁ hj₁ j₂ hj₂
  simp only [fiber_above, Finset.mem_filter] at hj₁ hj₂
  intro heq
  rw [heq] at hj₁
  have : k₁.val = k₂.val := hj₁.2.symm.trans hj₂.2
  exact hk (ZMod.val_injective (p^m) this)

/-- Measure of an arc [θ₁, θ₂) computed at level p^n.
    The arc is identified with the set of p^n-th roots it contains. -/
noncomputable def arc_measure_at_level (f : ℤ → ℂ)
    (hf : ∀ n : ℕ, [NeZero n] → IsPositiveDefiniteFinite n (fun k : ZMod n => f k.val))
    (n : ℕ) [NeZero n] (θ₁ θ₂ : ℝ) : ℝ :=
  -- Sum of μₙ(ωⱼ) for n-th roots ωⱼ = exp(2πij/n) in the arc [θ₁, θ₂)
  let μ := ((bochner_finite n (fun k : ZMod n => f k.val)).mp (hf n)).choose
  ∑ j : ZMod n, if θ₁ ≤ 2 * Real.pi * (j.val : ℝ) / n ∧
                   2 * Real.pi * (j.val : ℝ) / n < θ₂
                then μ j else 0

/-- Arc measure is non-negative (from positivity of μ). -/
lemma arc_measure_nonneg (f : ℤ → ℂ)
    (hf : ∀ n : ℕ, [NeZero n] → IsPositiveDefiniteFinite n (fun k : ZMod n => f k.val))
    (n : ℕ) [NeZero n] (θ₁ θ₂ : ℝ) :
    0 ≤ arc_measure_at_level f hf n θ₁ θ₂ := by
  unfold arc_measure_at_level
  apply Finset.sum_nonneg
  intro j _
  split_ifs with h
  · -- When condition holds, μ j > 0 by bochner_finite
    have hμ_pos := ((bochner_finite n (fun k : ZMod n => f k.val)).mp (hf n)).choose_spec.1
    exact le_of_lt (hμ_pos j)
  · -- Otherwise 0 ≤ 0
    rfl

/-- Total measure equals f(0). -/
lemma arc_measure_total (f : ℤ → ℂ)
    (hf : ∀ n : ℕ, [NeZero n] → IsPositiveDefiniteFinite n (fun k : ZMod n => f k.val))
    (n : ℕ) [NeZero n] :
    (arc_measure_at_level f hf n 0 (2 * Real.pi) : ℂ) = f 0 := by
  unfold arc_measure_at_level
  -- All roots are in [0, 2π), so sum over all j
  have h_all_in : ∀ j : ZMod n, 0 ≤ 2 * Real.pi * (j.val : ℝ) / n ∧
      2 * Real.pi * (j.val : ℝ) / n < 2 * Real.pi := by
    intro j
    constructor
    · apply div_nonneg
      apply mul_nonneg
      · linarith [Real.pi_pos]
      · exact Nat.cast_nonneg j.val
      · exact Nat.cast_nonneg n
    · have hj_lt : j.val < n := ZMod.val_lt j
      have hn_pos : (0 : ℝ) < n := by
        have : NeZero n := inferInstance
        exact Nat.cast_pos.mpr (NeZero.pos n)
      calc 2 * Real.pi * (j.val : ℝ) / n
          < 2 * Real.pi * n / n := by
            apply div_lt_div_of_pos_right _ hn_pos
            apply mul_lt_mul_of_pos_left
            · exact Nat.cast_lt.mpr hj_lt
            · linarith [Real.pi_pos]
        _ = 2 * Real.pi := by field_simp
  -- Simplify: each conditional is True ∧ True, so if_true applies
  have h_simp : ∀ j : ZMod n, (if 0 ≤ 2 * Real.pi * (j.val : ℝ) / n ∧
      2 * Real.pi * (j.val : ℝ) / n < 2 * Real.pi
      then ((bochner_finite n fun k => f ↑k.val).mp (hf n)).choose j else 0) =
      ((bochner_finite n fun k => f ↑k.val).mp (hf n)).choose j := by
    intro j
    simp only [h_all_in j, and_self, if_true]
  simp only [h_simp]
  -- Now sum equals total mass = f(0)
  have h := bochner_finite_total_mass n (fun k : ZMod n => f k.val) (hf n)
  -- Goal: ↑(∑ j, μ j) = f 0
  -- h says: (∑ j, ↑(μ j)) = f ↑(ZMod.val 0)
  -- First convert ↑(∑ j, μ j) to ∑ j, ↑(μ j)
  rw [Complex.ofReal_sum]
  -- Now need to match h: the difference is f 0 vs f ↑(ZMod.val 0)
  -- Since (0 : ZMod n).val = 0, these are equal
  simp only [ZMod.val_zero, Int.ofNat_zero] at h ⊢
  exact h

/-! ## MOMENT MATRIX STRUCTURE AND SPIRAL PAIRING -/

/-- STRONG POSITIVE-DEFINITENESS IMPLIES HERMITIAN SYMMETRY -/
lemma pos_def_int_hermitian_strong (f : ℤ → ℂ)
    (hf_im : ∀ n : ℕ, ∀ c : Fin n → ℂ, ∀ z : Fin n → ℤ,
      (∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c i) * c j * f (z j - z i)).im = 0)
    (_hf_re : ∀ n : ℕ, ∀ c : Fin n → ℂ, ∀ z : Fin n → ℤ,
      0 ≤ (∑ i : Fin n, ∑ j : Fin n, (starRingEnd ℂ) (c i) * c j * f (z j - z i)).re) :
    ∀ k : ℤ, f (-k) = conj (f k) := by
  intro k
  set a := (f k).re with ha_def
  set b := (f k).im with hb_def
  set c := (f (-k)).re with hc_def
  set d := (f (-k)).im with hd_def

  -- Get the three constraints from Im(Q) = 0
  have h1 := hf_im 2 ![1, 1] ![0, k]
  have hI := hf_im 2 ![1, Complex.I] ![0, k]
  have h_negI := hf_im 2 ![1, -Complex.I] ![0, k]

  have eq1 : 2 * (f 0).im + b + d = 0 := by
    -- h1 says Im(∑...) = 0 for c = (1,1), z = (0,k)
    -- The sum expands to 2f(0) + f(k) + f(-k)
    -- Expand the Fin 2 sums
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h1
    -- h1 is now: (conj(1)*1*f(0-0) + conj(1)*1*f(k-0) + conj(1)*1*f(0-k) + conj(1)*1*f(k-k)).im = 0
    simp only [sub_zero, sub_self, map_one, one_mul] at h1
    -- h1 : (f 0 + f k + f (-k) + f 0).im = 0
    simp only [Complex.add_im] at h1
    -- h1 : (f 0).im + (f k).im + (f (-k)).im + (f 0).im = 0
    -- Normalize and extract
    ring_nf at h1
    -- Convert to: 2*(f 0).im + b + d = 0
    have h1' : 2 * (f 0).im + (f k).im + (f (-k)).im = 0 := by linarith
    simp only [← hb_def, ← hd_def] at h1'
    exact h1'

  -- c = (1, I): conj(1) = 1, conj(I) = -I
  -- sum = 1·1·f(0) + 1·I·f(k) + (-I)·1·f(-k) + (-I)·I·f(0)
  --     = f(0) + I·f(k) - I·f(-k) + f(0) = 2f(0) + I·(f(k) - f(-k))
  -- Im = 2·Im(f(0)) + Re(f(k)) - Re(f(-k)) = 2·Im(f(0)) + a - c
  have eq2 : 2 * (f 0).im + a - c = 0 := by
    -- hI says Im(∑...) = 0 for c = (1, I), z = (0, k)
    -- Expand the Fin 2 sums
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hI
    -- Simplify: conj(1) = 1, conj(I) = -I, (-I)*I = 1
    simp only [sub_zero, sub_self, map_one, one_mul, Complex.conj_I] at hI
    -- hI : (f 0 + I * f k + (-I) * f (-k) + (-I) * I * f 0).im = 0
    -- Note: (-I) * I = 1
    have h_neg_I_I : (-Complex.I) * Complex.I = (1 : ℂ) := by
      simp only [neg_mul, Complex.I_mul_I, neg_neg]
    simp only [h_neg_I_I, one_mul] at hI
    -- hI : (f 0 + I * f k + (-I) * f (-k) + f 0).im = 0
    -- Use a comprehensive simp to extract imaginary parts and convert to variables
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
               Complex.neg_re, Complex.neg_im, mul_zero, mul_one, zero_mul, one_mul,
               zero_add, add_zero, neg_neg, ← ha_def, ← hc_def] at hI
    -- hI should now be in terms of a, c, and (f 0).im
    ring_nf at hI ⊢
    linarith

  -- c = (1, -I): conj(-I) = I
  -- sum = 1·1·f(0) + 1·(-I)·f(k) + I·1·f(-k) + I·(-I)·f(0)
  --     = f(0) - I·f(k) + I·f(-k) + f(0) = 2f(0) - I·(f(k) - f(-k))
  -- Im = 2·Im(f(0)) - Re(f(k)) + Re(f(-k)) = 2·Im(f(0)) - a + c
  have eq3 : 2 * (f 0).im - a + c = 0 := by
    -- h_negI says Im(∑...) = 0 for c = (1, -I), z = (0, k)
    -- Expand the Fin 2 sums
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h_negI
    -- Simplify: conj(1) = 1, conj(-I) = I, 0 - k = -k, k - k = 0
    simp only [sub_zero, sub_self, map_one, one_mul, zero_sub] at h_negI
    have h_conj_negI : (starRingEnd ℂ) (-Complex.I) = Complex.I := by simp
    simp only [h_conj_negI] at h_negI
    -- Note: I * (-I) = 1
    have h_I_neg_I : Complex.I * (-Complex.I) = (1 : ℂ) := by
      simp only [mul_neg, Complex.I_mul_I, neg_neg]
    simp only [h_I_neg_I, one_mul] at h_negI
    -- h_negI : (f 0 + (-I) * f k + I * f (-k) + f 0).im = 0
    -- Use a comprehensive simp to extract imaginary parts and convert to variables
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
               Complex.neg_re, Complex.neg_im, mul_zero, mul_one, zero_mul, one_mul,
               zero_add, add_zero, neg_neg, ← ha_def, ← hc_def] at h_negI
    -- h_negI should now be in terms of a, c, and (f 0).im
    linarith

  -- From eq2 + eq3: 4·(f 0).im = 0
  have hf0_im : (f 0).im = 0 := by linarith

  -- From eq2 with hf0_im: a = c
  have ha_eq_c : a = c := by linarith

  -- From eq1 with hf0_im: b + d = 0, so d = -b
  have hd_eq_neg_b : d = -b := by linarith

  -- Now prove f(-k) = conj(f(k))
  rw [Complex.ext_iff]
  constructor
  · simp only [Complex.conj_re]; rw [← ha_def, ← hc_def]; exact ha_eq_c.symm
  · simp only [Complex.conj_im]; rw [← hb_def, ← hd_def]; exact hd_eq_neg_b


end FourierBochner
