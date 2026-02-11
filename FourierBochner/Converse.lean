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

lemma ΛTrigℤ_nonneg_of_nonneg (f : ℝ → ℂ) (hf : IsPositiveDefinite f)
    (R : TrigPolyℤ) (h_R_real : ∀ θ : 𝕋, (R.toCircle θ).im = 0)
    (h_R_nonneg : ∀ θ : 𝕋, 0 ≤ (R.toCircle θ).re) :
    0 ≤ (ΛTrigℤ f R).re := by
  obtain ⟨P, rfl⟩ := fejer_riesz R h_R_real h_R_nonneg
  exact ΛTrigℤ_normSq_nonneg f hf P

/-- The Fejér kernel is non-negative on the circle (its real part). -/
lemma fejerKernel_nonneg (N : ℕ) (θ : 𝕋) :
    0 ≤ ((fejerKernel N).toCircle θ).re := by
  unfold fejerKernel
  rw [TrigPolyℤ.normSq_toCircle_eval]
  simp only [Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- For any polynomial P, the sup norm bound |P(t)|² ≤ ‖P‖²_∞ translates to a bound on Λ(|P|²). -/
lemma ΛTrigℤ_normSq_bound (f : ℝ → ℂ) (hf : IsPositiveDefinite f) (P : TrigPolyℤ) :
    (ΛTrigℤ f (TrigPolyℤ.normSq P)).re ≤ ‖P.toCircle‖ ^ 2 * (f 0).re := by
  let R : TrigPolyℤ := (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) - TrigPolyℤ.normSq P
  -- Step 2: Show R.toCircle θ ≥ 0 for all θ (pointwise non-negativity)
  have h_R_nonneg : ∀ θ : 𝕋, 0 ≤ (TrigPolyℤ.toCircle R θ).re := by
    intro θ
    -- R.toCircle θ = const(‖P‖²) - (normSq P).toCircle θ
    --              = ‖P‖² - |P.toCircle θ|²  (by evaluation formula)
    --              ≥ 0  (by definition of sup norm)
    -- First unfold R
    show (TrigPolyℤ.toCircle
    ((Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) - TrigPolyℤ.normSq P) θ).re ≥ 0
    -- Use linearity of toCircle: (A - B).toCircle = A.toCircle - B.toCircle
    have h_toCircle_sub :
     TrigPolyℤ.toCircle ((Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) - TrigPolyℤ.normSq P) =
        TrigPolyℤ.toCircle (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) -
         TrigPolyℤ.toCircle (TrigPolyℤ.normSq P) := by
      have h_sub : (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) - TrigPolyℤ.normSq P =
          (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) + ((-1 : ℂ) • TrigPolyℤ.normSq P) := by
        simp [sub_eq_add_neg, neg_one_smul]
      rw [h_sub, TrigPolyℤ.toCircle_add, TrigPolyℤ.toCircle_smul]
      rw [neg_one_smul ℂ P.normSq.toCircle, sub_eq_add_neg]
    simp only [h_toCircle_sub, ContinuousMap.coe_sub, Pi.sub_apply]
    -- Now we need to evaluate (Finsupp.single 0 c).toCircle θ = c
    -- This is a constant polynomial, which evaluates to its constant coefficient
    have h_const_eval : TrigPolyℤ.toCircle (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) θ =
     ‖P.toCircle‖ ^ 2 :=
      TrigPolyℤ.toCircle_single_zero _ _
    -- Use normSq_toCircle_eval
    have h_normSq_eval : TrigPolyℤ.toCircle (TrigPolyℤ.normSq P) θ =
     Complex.normSq (P.toCircle θ) :=
      TrigPolyℤ.normSq_toCircle_eval P θ
    rw [h_const_eval, h_normSq_eval]
    -- Now show: (‖P‖² - |P θ|²).re ≥ 0
    -- Note: Complex.normSq returns ℝ, so it's embedded as ℂ via ofReal
    simp only [Complex.sub_re, Complex.ofReal_re]
    -- Simplify (↑‖P‖ ^ 2).re to ‖P‖²
    have h_real_re : (↑‖P.toCircle‖ ^ 2 : ℂ).re = ‖P.toCircle‖ ^ 2 := by
      simp only [pow_succ, pow_zero, mul_one, Complex.ofReal_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.one_re]
    rw [h_real_re]
    -- Now: ‖P‖² - normSq(P θ) ≥ 0
    -- This follows from normSq(P θ) ≤ ‖P‖²
    have h_bound : Complex.normSq (P.toCircle θ) ≤ ‖P.toCircle‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      have h_le : ‖P.toCircle θ‖ ≤ ‖P.toCircle‖ := ContinuousMap.norm_coe_le_norm _ _
      nlinarith [sq_nonneg ‖P.toCircle θ‖, sq_nonneg ‖P.toCircle‖, h_le, norm_nonneg (P.toCircle θ),
        norm_nonneg P.toCircle]
    linarith
  have h_R_real : ∀ θ : 𝕋, (TrigPolyℤ.toCircle R θ).im = 0 := by
    intro θ
    show (TrigPolyℤ.toCircle
      ((Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) - TrigPolyℤ.normSq P) θ).im = 0
    have h_toCircle_sub :
      TrigPolyℤ.toCircle ((Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) - TrigPolyℤ.normSq P) =
        TrigPolyℤ.toCircle (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) -
         TrigPolyℤ.toCircle (TrigPolyℤ.normSq P) := by
      have h_sub : (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) - TrigPolyℤ.normSq P =
          (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) + ((-1 : ℂ) • TrigPolyℤ.normSq P) := by
        simp [sub_eq_add_neg, neg_one_smul]
      rw [h_sub, TrigPolyℤ.toCircle_add, TrigPolyℤ.toCircle_smul]
      rw [neg_one_smul ℂ P.normSq.toCircle, sub_eq_add_neg]
    simp only [h_toCircle_sub, ContinuousMap.coe_sub, Pi.sub_apply]
    rw [TrigPolyℤ.toCircle_single_zero, TrigPolyℤ.normSq_toCircle_eval]
    simp only [Complex.sub_im, ← Complex.ofReal_pow, Complex.ofReal_im, sub_zero]
  have h_Λ_R_nonneg : 0 ≤ (ΛTrigℤ f R).re := by
    exact ΛTrigℤ_nonneg_of_nonneg f hf R h_R_real h_R_nonneg
  -- Step 4: Expand Λ(R) using linearity
  have h_Λ_R_expand : ΛTrigℤ f R =
      ΛTrigℤ f (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) - ΛTrigℤ f (TrigPolyℤ.normSq P) := by
    show ΛTrigℤ f (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ) - TrigPolyℤ.normSq P) =
        ΛTrigℤ f (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) - ΛTrigℤ f (TrigPolyℤ.normSq P)
    have h_lin : ΛTrigℤ f (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ) - TrigPolyℤ.normSq P) =
        ΛTrigℤ f (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) +
          ΛTrigℤ f ((-1 : ℂ) • TrigPolyℤ.normSq P) := by
      rw [sub_eq_add_neg]
      have : -TrigPolyℤ.normSq P = (-1 : ℂ) • TrigPolyℤ.normSq P := by simp [neg_one_smul]
      rw [this]
      exact ΛTrigℤ_add f _ _
    rw [h_lin, ΛTrigℤ_smul]
    simp only [neg_one_mul, sub_eq_add_neg]
  -- Evaluate Λ on const polynomial
  have h_Λ_const : ΛTrigℤ f (Finsupp.single 0 (‖P.toCircle‖ ^ 2 : ℂ)) =
      ‖P.toCircle‖ ^ 2 * f 0 := by
    unfold ΛTrigℤ
    by_cases h : (‖P.toCircle‖ ^ 2 : ℂ) = 0
    · simp [h]
    · rw [Finsupp.support_single_ne_zero _ h]
      simp only [Finset.sum_singleton, Finsupp.single_eq_same, Int.cast_zero]
  -- Step 5: Conclude
  rw [h_Λ_R_expand] at h_Λ_R_nonneg
  simp only [Complex.sub_re] at h_Λ_R_nonneg
  rw [h_Λ_const] at h_Λ_R_nonneg
  -- Now: 0 ≤ (‖P‖² * f(0)).re - Λ(normSq P).re
  -- Goal: Λ(normSq P).re ≤ ‖P‖² * f(0).re
  have h_real : ((‖P.toCircle‖ ^ 2 : ℝ) : ℂ) = ‖P.toCircle‖ ^ 2 := by norm_cast
  rw [← h_real] at h_Λ_R_nonneg
  simp only [Complex.mul_re, Complex.ofReal_re,
   Complex.ofReal_im, zero_mul, sub_zero] at h_Λ_R_nonneg
  linarith

/-- BOUNDEDNESS LEMMA: ΛTrigℤ is bounded by the positive-definiteness constant. -/
lemma ΛTrigℤ_bounded (f : ℝ → ℂ) (hf_pos : IsPositiveDefinite f) (P : TrigPolyℤ) :
    ‖ΛTrigℤ f P‖ ≤ (f 0).re * ‖P.toCircle‖ := by
  -- PROOF using Cauchy-Schwarz for positive functionals
  -- Step 1: Handle f(0) = 0 case
  by_cases h_f0 : (f 0).re = 0
  · -- If f(0) = 0, then by Cauchy-Schwarz all Λ values are bounded by 0
    have h_CS := cauchy_schwarz_for_Λ f hf_pos P TrigPolyℤ.const_one
    -- h_CS: normSq (sesq f_neg P const_one) ≤ Λ(normSq const_one) * Λ(normSq P)
    -- normSq const_one = const_one, so Λ(normSq const_one) = f(0)
    have h_normSq_one : TrigPolyℤ.normSq TrigPolyℤ.const_one = TrigPolyℤ.const_one := by
      ext k
      unfold TrigPolyℤ.normSq TrigPolyℤ.const_one
      simp only [Finsupp.ofSupportFinite_coe]
      rw [Finsupp.support_single_ne_zero _ one_ne_zero]
      simp only [Finset.sum_singleton, Finsupp.single_eq_same, map_one, one_mul, zero_add]
    have h_Λ_one : ΛTrigℤ f (TrigPolyℤ.normSq TrigPolyℤ.const_one) = f 0 := by
      rw [h_normSq_one, ΛTrigℤ_const_one]
    -- Since (f 0).re = 0 and f(0) is real for positive-definite f, f(0) = 0
    have h_f0_eq : f 0 = 0 := by
      have h_real := (f_zero_real_nonneg f hf_pos).1
      rw [Complex.ext_iff]; constructor
      · exact h_f0
      · rw [h_real]; simp
    rw [h_Λ_one, h_f0_eq] at h_CS
    simp only [Complex.zero_re, zero_mul] at h_CS
    -- h_CS now says normSq (...) ≤ 0, so the sesquilinear form is 0
    have h_sesq_zero : sesquilinear_form (fun x => f (-x)) P TrigPolyℤ.const_one = 0 := by
      have : Complex.normSq (sesquilinear_form (fun x => f (-x)) P TrigPolyℤ.const_one) ≤ 0 := h_CS
      have h_nonneg :=
       Complex.normSq_nonneg (sesquilinear_form (fun x => f (-x)) P TrigPolyℤ.const_one)
      have h_eq : Complex.normSq (sesquilinear_form (fun x => f (-x)) P TrigPolyℤ.const_one) = 0 :=
        le_antisymm this h_nonneg
      exact Complex.normSq_eq_zero.mp h_eq
    -- Relate sesquilinear_form to ΛTrigℤ to show ΛTrigℤ f P = 0
    have h_sesq_eq : sesquilinear_form (fun x => f (-x)) P TrigPolyℤ.const_one =
        conj (ΛTrigℤ f P) := by
      unfold sesquilinear_form ΛTrigℤ
      rw [const_one_support]
      simp only [Finset.sum_singleton, Int.cast_zero, sub_zero]
      unfold TrigPolyℤ.const_one
      simp only [Finsupp.single_eq_same, mul_one]
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      have h_fn : f (-(m : ℝ)) = conj (f m) := hf_pos.1 m
      rw [h_fn, ← map_mul]
    rw [h_sesq_eq] at h_sesq_zero
    have h_Λ_zero : ΛTrigℤ f P = 0 := by
      have : conj (ΛTrigℤ f P) = conj 0 := by rw [h_sesq_zero]; simp
      simpa using this
    simp [h_Λ_zero, h_f0]
  · -- Main case: f(0) > 0
    have hf0_pos : 0 < (f 0).re := by
      have := hf_pos.zero_nonneg
      push_neg at h_f0
      exact this.lt_of_ne' h_f0
    -- Step 2: Use Cauchy-Schwarz
    have h_CS := cauchy_schwarz_for_Λ f hf_pos P TrigPolyℤ.const_one
    -- Relate sesquilinear_form to ΛTrigℤ
    have h_sesq_eq : sesquilinear_form (fun x => f (-x)) P TrigPolyℤ.const_one =
        conj (ΛTrigℤ f P) := by
      unfold sesquilinear_form ΛTrigℤ
      rw [const_one_support]
      simp only [Finset.sum_singleton, Int.cast_zero, sub_zero]
      unfold TrigPolyℤ.const_one
      simp only [Finsupp.single_eq_same, mul_one]
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      have h_fn : f (-(m : ℝ)) = conj (f m) := hf_pos.1 m
      rw [h_fn, ← map_mul]
    -- normSq const_one = const_one
    have h_normSq_one : TrigPolyℤ.normSq TrigPolyℤ.const_one = TrigPolyℤ.const_one := by
      ext k
      unfold TrigPolyℤ.normSq TrigPolyℤ.const_one
      simp only [Finsupp.ofSupportFinite_coe]
      rw [Finsupp.support_single_ne_zero _ one_ne_zero]
      simp only [Finset.sum_singleton, Finsupp.single_eq_same, map_one, one_mul, zero_add]
    have h_Λ_one : ΛTrigℤ f (TrigPolyℤ.normSq TrigPolyℤ.const_one) = f 0 := by
      rw [h_normSq_one, ΛTrigℤ_const_one]
    -- Now: |Λ P|² = normSq(conj(Λ P)) = normSq(sesq...) ≤ Λ(normSq 1) * Λ(normSq P)
    have h_bound1 : Complex.normSq (ΛTrigℤ f P) ≤
        (f 0).re * (ΛTrigℤ f (TrigPolyℤ.normSq P)).re := by
      calc Complex.normSq (ΛTrigℤ f P)
          = Complex.normSq (conj (ΛTrigℤ f P)) := by rw [Complex.normSq_conj]
        _ = Complex.normSq (sesquilinear_form (fun x => f (-x)) P TrigPolyℤ.const_one) := by
            rw [h_sesq_eq]
        _ ≤ (ΛTrigℤ f (TrigPolyℤ.normSq TrigPolyℤ.const_one)).re *
            (ΛTrigℤ f (TrigPolyℤ.normSq P)).re := h_CS
        _ = (f 0).re * (ΛTrigℤ f (TrigPolyℤ.normSq P)).re := by rw [h_Λ_one]
    -- Step 3: Use ΛTrigℤ_normSq_bound
    have h_bound2 : (ΛTrigℤ f (TrigPolyℤ.normSq P)).re ≤ ‖P.toCircle‖ ^ 2 * (f 0).re :=
      ΛTrigℤ_normSq_bound f hf_pos P
    -- Step 4: Combine
    have h_normSq_bound : Complex.normSq (ΛTrigℤ f P) ≤ ((f 0).re * ‖P.toCircle‖) ^ 2 := by
      calc Complex.normSq (ΛTrigℤ f P)
          ≤ (f 0).re * (ΛTrigℤ f (TrigPolyℤ.normSq P)).re := h_bound1
        _ ≤ (f 0).re * (‖P.toCircle‖ ^ 2 * (f 0).re) := by
            apply mul_le_mul_of_nonneg_left h_bound2 hf_pos.zero_nonneg
        _ = ((f 0).re * ‖P.toCircle‖) ^ 2 := by ring
    -- Step 5: Take square root
    have h_nonneg : 0 ≤ (f 0).re * ‖P.toCircle‖ := by
      apply mul_nonneg hf_pos.zero_nonneg (norm_nonneg _)
    calc ‖ΛTrigℤ f P‖
        = Real.sqrt (‖ΛTrigℤ f P‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
      _ = Real.sqrt (Complex.normSq (ΛTrigℤ f P)) := by rw [Complex.normSq_eq_norm_sq]
      _ ≤ Real.sqrt (((f 0).re * ‖P.toCircle‖) ^ 2) := Real.sqrt_le_sqrt h_normSq_bound
      _ = (f 0).re * ‖P.toCircle‖ := Real.sqrt_sq h_nonneg

/-- Extend ΛTrigℤ to all of C(𝕋, ℂ) using the fact that ΛTrigℤ is linear on the dense -/
noncomputable def Λ_on_circle (f : ℝ → ℂ) (hf_pos : IsPositiveDefinite f)
    (g : C(𝕋, ℂ)) : ℂ := by
  classical
  -- Step 2: for each n, approximate within 1/(n+1)
  have approx : ∀ n : ℕ, ∃ P : TrigPolyℤ, ‖g - P.toCircle‖ < (1 : ℝ) / (n + 1) := by
    intro n
    have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
      -- robust positivity: 0 < 1/(n+1)
      have : (0 : ℝ) < (n + 1 : ℝ) := by
        exact_mod_cast Nat.succ_pos n
      simpa using (one_div_pos.mpr this)
    exact approx_by_trigpoly g ((1 : ℝ) / (n + 1)) hpos
  -- Step 3: choose a specific approximating sequence
  let P_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx n)
  have P_seq_spec (n : ℕ) : ‖g - (P_seq n).toCircle‖ < (1 : ℝ) / (n + 1) :=
    Classical.choose_spec (approx n)
  -- Step 4: show ΛTrigℤ(f, P_seq n) is Cauchy using the boundedness lemma
  have cauchy :
      ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m →
        ‖ΛTrigℤ f (P_seq n) - ΛTrigℤ f (P_seq m)‖ < ε := by
    intro ε hε
    have hf0_nonneg : 0 ≤ (f 0).re := hf_pos.zero_nonneg
    by_cases h_f0_zero : (f 0).re = 0
    · -- If (f 0).re = 0, ΛTrigℤ is forced to be 0 by your bound.
      refine ⟨0, ?_⟩
      intro n m _ _
      have bound_zero : ∀ P, ‖ΛTrigℤ f P‖ ≤ 0 := by
        intro P
        have h := ΛTrigℤ_bounded f hf_pos P
      -- rewrite the RHS to 0 using h_f0_zero
      -- `simp` should now close it
        simpa [h_f0_zero] using h
      have Λ_zero : ∀ P, ΛTrigℤ f P = 0 := by
        intro P
        exact norm_le_zero_iff.mp (bound_zero P)
      simpa [Λ_zero, hε]
    · have hf0_pos : 0 < (f 0).re := lt_of_le_of_ne hf0_nonneg (Ne.symm h_f0_zero)
      -- choose N with 2*(f0)/ (N+1) < ε
      obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * (f 0).re / (N + 1 : ℝ) < ε := by
      -- basic Archimedean choice
        obtain ⟨N, hN⟩ := exists_nat_gt (2 * (f 0).re / ε)
        refine ⟨N, ?_⟩
        have hε' : 0 < ε := hε
        have hpos : 0 < (N + 1 : ℝ) := by positivity
      -- A clean way: since (2*f0)/ε < N, we get (2*f0)/(N+1) < ε.
        have hN' : 2 * (f 0).re / ε < (N : ℝ) := by exact_mod_cast hN
      -- Since N < N + 1, we have 2*f0/ε < N + 1
        have hN1 : 2 * (f 0).re / ε < (N : ℝ) + 1
         := lt_of_lt_of_le hN' (le_add_of_nonneg_right (by linarith))
      -- Rearrange: 2*f0 < ε*(N+1), so 2*f0/(N+1) < ε
        rw [div_lt_iff₀ hpos]
        calc 2 * (f 0).re = (2 * (f 0).re / ε) * ε := by field_simp
          _ < ((N : ℝ) + 1) * ε := by nlinarith
          _ = ε * ((N : ℝ) + 1) := by ring
      refine ⟨N, ?_⟩
      intro n m hn hm
      -- Use ΛTrigℤ linearity to convert difference into ΛTrigℤ of a difference
      have h_neg (P : TrigPolyℤ) : ΛTrigℤ f (-P) = - ΛTrigℤ f P := by
      -- (-P) = (-1) • P
        simpa [one_smul, sub_eq_add_neg] using (ΛTrigℤ_smul (f:=f) (-1 : ℂ) P)
      have h_sub :
          ΛTrigℤ f (P_seq n - P_seq m) = ΛTrigℤ f (P_seq n) - ΛTrigℤ f (P_seq m) := by
      -- expand subtraction as add + (-1)• and use your linearity lemmas
      -- this avoids any fragile `rw` pattern-matching
        simp [sub_eq_add_neg, h_neg, ΛTrigℤ_add]
      -- Now rewrite goal using h_sub in the reverse direction
      have :
          ‖ΛTrigℤ f (P_seq n) - ΛTrigℤ f (P_seq m)‖ =
            ‖ΛTrigℤ f (P_seq n - P_seq m)‖ := by
        simpa [h_sub]  -- just rearranges
      -- Bound via ΛTrigℤ_bounded and then bound the supnorm difference
      -- by triangle inequality against g
      calc
        ‖ΛTrigℤ f (P_seq n) - ΛTrigℤ f (P_seq m)‖
            = ‖ΛTrigℤ f (P_seq n - P_seq m)‖ := this
        _ ≤ (f 0).re * ‖(P_seq n - P_seq m).toCircle‖ := ΛTrigℤ_bounded f hf_pos _
        _ = (f 0).re * ‖(P_seq n).toCircle - (P_seq m).toCircle‖ := by
              -- push `toCircle` through subtraction
              -- (uses toCircle_add + toCircle_smul)
              congr 1
              -- Goal: (P_seq n - P_seq m).toCircle = (P_seq n).toCircle - (P_seq m).toCircle
              have h_sub : P_seq n - P_seq m = P_seq n + ((-1 : ℂ) • P_seq m) := by
                simp [sub_eq_add_neg, neg_one_smul]
              rw [h_sub, TrigPolyℤ.toCircle_add, TrigPolyℤ.toCircle_smul]
              -- Now: (P_seq n).toCircle + (-1) • (P_seq m).toCircle
              -- = (P_seq n).toCircle - (P_seq m).toCircle
              rw [neg_one_smul ℂ (P_seq m).toCircle, sub_eq_add_neg]
        _ ≤ (f 0).re * (‖g - (P_seq n).toCircle‖ + ‖g - (P_seq m).toCircle‖) := by
              apply mul_le_mul_of_nonneg_left
              · -- triangle inequality in `C(𝕋,ℂ)`
                have :
                    (P_seq n).toCircle - (P_seq m).toCircle =
                      ((P_seq n).toCircle - g) + (g - (P_seq m).toCircle) := by
                  abel
                calc
                  ‖(P_seq n).toCircle - (P_seq m).toCircle‖
                      = ‖((P_seq n).toCircle - g) + (g - (P_seq m).toCircle)‖ := by
                          rw [this]
                  _ ≤ ‖(P_seq n).toCircle - g‖ + ‖g - (P_seq m).toCircle‖ := norm_add_le _ _
                  _ = ‖g - (P_seq n).toCircle‖ + ‖g - (P_seq m).toCircle‖ := by
                        simp [norm_sub_rev]
              · exact hf0_nonneg
        _ < (f 0).re * ((1 : ℝ) / (n + 1) + (1 : ℝ) / (m + 1)) := by
              -- use P_seq_spec bounds
              have hn' : ‖g - (P_seq n).toCircle‖ < (1 : ℝ) / (n + 1) := P_seq_spec n
              have hm' : ‖g - (P_seq m).toCircle‖ < (1 : ℝ) / (m + 1) := P_seq_spec m
              have : ‖g - (P_seq n).toCircle‖ + ‖g - (P_seq m).toCircle‖
                    < (1 : ℝ) / (n + 1) + (1 : ℝ) / (m + 1) := by
                linarith
              exact (mul_lt_mul_of_pos_left this hf0_pos)
        _ ≤ (f 0).re * ((1 : ℝ) / (N + 1) + (1 : ℝ) / (N + 1)) := by
              apply mul_le_mul_of_nonneg_left
              · -- monotonicity: N ≤ n ⇒ 1/(n+1) ≤ 1/(N+1)
                have hn_cast : (N + 1 : ℝ) ≤ (n + 1 : ℝ) := by
                  exact_mod_cast Nat.add_le_add_right hn 1
                have hm_cast : (N + 1 : ℝ) ≤ (m + 1 : ℝ) := by
                  exact_mod_cast Nat.add_le_add_right hm 1
                have hposN : 0 < (N + 1 : ℝ) := by positivity
                have hn_le : (1 : ℝ) / (n + 1) ≤ (1 : ℝ) / (N + 1) :=
                  one_div_le_one_div_of_le hposN hn_cast
                have hm_le : (1 : ℝ) / (m + 1) ≤ (1 : ℝ) / (N + 1) :=
                  one_div_le_one_div_of_le hposN hm_cast
                linarith
              · exact hf0_nonneg
        _ = 2 * (f 0).re / (N + 1 : ℝ) := by ring
        _ < ε := hN
  -- Step 5: get a limit in ℂ from Cauchy
  have limit_exists : ∃ L : ℂ,
      Filter.Tendsto (fun n => ΛTrigℤ f (P_seq n)) Filter.atTop (nhds L) := by
    have h_cauchy_seq : CauchySeq (fun n => ΛTrigℤ f (P_seq n)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := cauchy ε hε
      refine ⟨N, ?_⟩
      intro n hn m hm
      -- dist = norm difference
      simpa [dist_eq_norm] using (hN n m hn hm)
    -- ℂ is complete, so CauchySeq → convergent
    exact cauchySeq_tendsto_of_complete h_cauchy_seq
  exact Classical.choose limit_exists
/-! ### Profinite Analogy Lemmas
These lemmas prove properties of Λ_on_circle by exact analogy with
`continuous_if_profinitecontinuous_at`. The key technique: triangle inequality!
-/
/-- PROFINITE ANALOGY LEMMA 1: Constant approximating sequences converge -/
lemma Λ_on_circle_constant_seq (f : ℝ → ℂ) (hf_pos : IsPositiveDefinite f)
    (P : TrigPolyℤ) :
    Λ_on_circle f hf_pos (P.toCircle) = ΛTrigℤ f P := by
  -- The definition Λ_on_circle uses Classical.choose to pick an approximating sequence.
  -- However, the limit is unique (ℂ is Hausdorff), so we can compute it using ANY
  -- valid approximating sequence.
  -- Choose the constant sequence Q_seq(n) = P:
  --   ‖P.toCircle - P.toCircle‖ = 0 < 1/(n+1) ✓
  -- Then Λ_on_circle(P.toCircle) = lim_{n→∞} ΛTrigℤ(P) = ΛTrigℤ(P)
  -- Let L be the value returned by Λ_on_circle
  set L := Λ_on_circle f hf_pos P.toCircle with hL_def
  -- We need to show L = ΛTrigℤ f P
  -- The definition constructs an approximating sequence and takes its limit.
  -- We'll show that ANY sequence
  -- approximating P.toCircle has ΛTrigℤ values converging to ΛTrigℤ f P.
  -- Key boundedness: for any Q, R approximating the same g:
  -- ‖ΛTrigℤ f Q - ΛTrigℤ f R‖ ≤ (f 0).re * ‖Q.toCircle - R.toCircle‖
  have h_bound_diff : ∀ Q R : TrigPolyℤ, ‖ΛTrigℤ f Q - ΛTrigℤ f R‖ ≤
      (f 0).re * ‖Q.toCircle - R.toCircle‖ := by
    intro Q R
    have h_lin : ΛTrigℤ f Q - ΛTrigℤ f R = ΛTrigℤ f (Q - R) := by
      have h_neg (S : TrigPolyℤ) : ΛTrigℤ f (-S) = - ΛTrigℤ f S := by
        simpa [one_smul, sub_eq_add_neg] using (ΛTrigℤ_smul (f:=f) (-1 : ℂ) S)
      simp [sub_eq_add_neg, h_neg, ΛTrigℤ_add]
    rw [h_lin]
    have h_toCircle_sub : (Q - R).toCircle = Q.toCircle - R.toCircle := by
      have h_sub : Q - R = Q + ((-1 : ℂ) • R) := by simp [sub_eq_add_neg, neg_one_smul]
      rw [h_sub, TrigPolyℤ.toCircle_add, TrigPolyℤ.toCircle_smul]
      rw [neg_one_smul ℂ R.toCircle, sub_eq_add_neg]
    calc ‖ΛTrigℤ f (Q - R)‖
        ≤ (f 0).re * ‖(Q - R).toCircle‖ := ΛTrigℤ_bounded f hf_pos _
      _ = (f 0).re * ‖Q.toCircle - R.toCircle‖ := by rw [h_toCircle_sub]
  -- For the definition's sequence approximating P.toCircle with error < 1/(n+1),
  -- the ΛTrigℤ values converge to some limit (this is what Λ_on_circle computes).
  -- We show this limit equals ΛTrigℤ f P using uniqueness.
  -- Show that L = ΛTrigℤ f P by showing the distance is arbitrarily small
  suffices ∀ ε > 0, dist L (ΛTrigℤ f P) < ε by
    have := eq_of_forall_dist_le (fun ε hε => le_of_lt (this ε hε))
    exact this
  intro ε hε
  -- The constant sequence (P, P, P, ...) approximates P.toCircle with error 0.
  -- Any other approximating sequence Q_seq with ‖P.toCircle - Q_seq(n).toCircle‖ < 1/(n+1)
  -- has ‖ΛTrigℤ f P - ΛTrigℤ f (Q_seq n)‖ ≤ (f 0).re * (0 + 1/(n+1)) → 0.
  -- So both converge to the same limit, hence L = ΛTrigℤ f P.
  by_cases h_f0_zero : (f 0).re = 0
  · -- If f(0) = 0, then ΛTrigℤ f is the zero functional by boundedness
    have h_zero : ∀ Q : TrigPolyℤ, ΛTrigℤ f Q = 0 := by
      intro Q
      have h := ΛTrigℤ_bounded f hf_pos Q
      simp only [h_f0_zero, zero_mul, nonpos_iff_eq_zero] at h
      exact norm_le_zero_iff.mp h
    -- L = 0 = ΛTrigℤ f P since everything is zero
    rw [h_zero P]
    -- Λ_on_circle applied to any function returns 0 when f(0) = 0
    -- L is a limit of the sequence ΛTrigℤ f (Q_seq n) where each term is 0
    have hL_zero : L = 0 := by
      -- Use the same approach as the f(0) > 0 case:
      -- Build an approximating sequence and show limit uniqueness
      have approx : ∀ n : ℕ, ∃ Q : TrigPolyℤ,
          ‖P.toCircle - Q.toCircle‖ < (1 : ℝ) / (n + 1) := by
        intro n
        have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
          have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
          simpa using (one_div_pos.mpr this)
        exact approx_by_trigpoly P.toCircle _ hpos
      let Q_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx n)
      -- The sequence ΛTrigℤ f (Q_seq n) is constantly 0
      have h_seq_zero : ∀ n, ΛTrigℤ f (Q_seq n) = 0 := fun n => h_zero (Q_seq n)
      -- So ΛTrigℤ f (Q_seq n) → 0
      have h_tends_0 : Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds 0) := by
        simp_rw [h_seq_zero]
        exact tendsto_const_nhds
      -- The sequence is trivially Cauchy (all terms equal)
      have cauchy : CauchySeq (fun n => ΛTrigℤ f (Q_seq n)) := by
        rw [Metric.cauchySeq_iff]
        intro ε' hε'
        use 0
        intro n _ m _
        simp [dist_eq_norm, h_seq_zero, hε']
      have limit_exists : ∃ L' : ℂ, Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds L') := cauchySeq_tendsto_of_complete cauchy
      -- By uniqueness, L = 0
      have h_def_limit := Classical.choose_spec limit_exists
      exact tendsto_nhds_unique h_def_limit h_tends_0
    rw [hL_zero]
    simp [hε]
  · -- f(0) > 0 case
    have hf0_pos : 0 < (f 0).re := lt_of_le_of_ne hf_pos.zero_nonneg (Ne.symm h_f0_zero)
    -- The approximating sequence from the definition
    have approx : ∀ n : ℕ, ∃ Q : TrigPolyℤ,
        ‖P.toCircle - Q.toCircle‖ < (1 : ℝ) / (n + 1) := by
      intro n
      have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
        have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
        simpa using (one_div_pos.mpr this)
      exact approx_by_trigpoly P.toCircle _ hpos
    let Q_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx n)
    have Q_spec : ∀ n, ‖P.toCircle - (Q_seq n).toCircle‖ < (1 : ℝ) / (n + 1) :=
      fun n => Classical.choose_spec (approx n)
    -- Show ΛTrigℤ f (Q_seq n) → ΛTrigℤ f P
    have h_tends_P : Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
        Filter.atTop (nhds (ΛTrigℤ f P)) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨M, hM⟩ := exists_nat_gt ((f 0).re / δ)
      use M
      intro n hn
      rw [dist_eq_norm]
      have hM' : (f 0).re / δ < (M : ℝ) := by exact_mod_cast hM
      have hposM : 0 < (M + 1 : ℝ) := by positivity
      calc ‖ΛTrigℤ f (Q_seq n) - ΛTrigℤ f P‖
          ≤ (f 0).re * ‖(Q_seq n).toCircle - P.toCircle‖ := h_bound_diff _ _
        _ = (f 0).re * ‖P.toCircle - (Q_seq n).toCircle‖ := by rw [norm_sub_rev]
        _ < (f 0).re * (1 / (n + 1)) := mul_lt_mul_of_pos_left (Q_spec n) hf0_pos
        _ ≤ (f 0).re * (1 / (M + 1)) := by
            apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
            have hn_cast : (M + 1 : ℝ) ≤ (n + 1 : ℝ) := by
              exact_mod_cast Nat.add_le_add_right hn 1
            exact one_div_le_one_div_of_le hposM hn_cast
        _ = (f 0).re / (M + 1) := by ring
        _ < δ := by
            rw [div_lt_iff₀ hposM]
            have h1 : (f 0).re < (M : ℝ) * δ := by
              have := (div_lt_iff₀ hδ).mp hM'
              linarith
            calc (f 0).re < (M : ℝ) * δ := h1
              _ < (M + 1 : ℝ) * δ := by linarith
              _ = δ * (M + 1 : ℝ) := by ring
    -- The sequence is Cauchy
    have cauchy : CauchySeq (fun n => ΛTrigℤ f (Q_seq n)) := by
      rw [Metric.cauchySeq_iff]
      intro δ hδ
      obtain ⟨M, hM⟩ := exists_nat_gt (2 * (f 0).re / δ)
      use M
      intro n hn m hm
      rw [dist_eq_norm]
      have hM' : 2 * (f 0).re / δ < (M : ℝ) := by exact_mod_cast hM
      have hposM : 0 < (M + 1 : ℝ) := by positivity
      calc ‖ΛTrigℤ f (Q_seq n) - ΛTrigℤ f (Q_seq m)‖
          ≤ (f 0).re * ‖(Q_seq n).toCircle - (Q_seq m).toCircle‖ := h_bound_diff _ _
        _ ≤ (f 0).re * (‖P.toCircle - (Q_seq n).toCircle‖ +
            ‖P.toCircle - (Q_seq m).toCircle‖) := by
            apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
            calc ‖(Q_seq n).toCircle - (Q_seq m).toCircle‖
                = ‖((Q_seq n).toCircle - P.toCircle) + (P.toCircle - (Q_seq m).toCircle)‖ := by
                    ring_nf
              _ ≤ ‖(Q_seq n).toCircle - P.toCircle‖ + ‖P.toCircle - (Q_seq m).toCircle‖ :=
                    norm_add_le _ _
              _ = ‖P.toCircle - (Q_seq n).toCircle‖ + ‖P.toCircle - (Q_seq m).toCircle‖ := by
                    rw [norm_sub_rev]
        _ < (f 0).re * ((1 : ℝ) / (n + 1) + (1 : ℝ) / (m + 1)) := by
            apply mul_lt_mul_of_pos_left _ hf0_pos
            exact add_lt_add (Q_spec n) (Q_spec m)
        _ ≤ (f 0).re * ((1 : ℝ) / (M + 1) + (1 : ℝ) / (M + 1)) := by
            apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
            have hn_cast : (M + 1 : ℝ) ≤ (n + 1 : ℝ) := by
              exact_mod_cast Nat.add_le_add_right hn 1
            have hm_cast : (M + 1 : ℝ) ≤ (m + 1 : ℝ) := by
              exact_mod_cast Nat.add_le_add_right hm 1
            exact add_le_add (one_div_le_one_div_of_le hposM hn_cast)
                             (one_div_le_one_div_of_le hposM hm_cast)
        _ = 2 * (f 0).re / (M + 1) := by ring
        _ < δ := by
            rw [div_lt_iff₀ hposM]
            have h1 : 2 * (f 0).re < (M : ℝ) * δ := by
              have := (div_lt_iff₀ hδ).mp hM'
              linarith
            calc 2 * (f 0).re < (M : ℝ) * δ := h1
              _ < (M + 1 : ℝ) * δ := by linarith
              _ = δ * (M + 1 : ℝ) := by ring
    have limit_exists : ∃ L' : ℂ, Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
        Filter.atTop (nhds L') :=
      cauchySeq_tendsto_of_complete cauchy
    -- L is the chosen limit, h_tends_P shows convergence to ΛTrigℤ f P
    -- By uniqueness, L = ΛTrigℤ f P
    have hL_eq : L = ΛTrigℤ f P := by
      -- The definition of Λ_on_circle picks a limit of some approximating sequence
      -- Our Q_seq is one such sequence (it approximates P.toCircle)
      -- We've shown Q_seq → ΛTrigℤ f P
      -- By uniqueness of limits in ℂ (Hausdorff), L = ΛTrigℤ f P
      have h_def_limit := Classical.choose_spec limit_exists
      exact tendsto_nhds_unique h_def_limit h_tends_P
    rw [hL_eq]
    simp [hε]
/-- Any approximating sequence for g converges to Λ_on_circle f hf_pos g.
    This is the key lemma for showing additivity and scalar multiplication. -/
lemma Λ_on_circle_approx_tendsto (f : ℝ → ℂ) (hf_pos : IsPositiveDefinite f)
    (g : C(𝕋, ℂ)) (P_seq : ℕ → TrigPolyℤ)
    (hP : ∀ n, ‖g - (P_seq n).toCircle‖ < (1 : ℝ) / (n + 1)) :
    Filter.Tendsto (fun n => ΛTrigℤ f (P_seq n)) Filter.atTop
      (nhds (Λ_on_circle f hf_pos g)) := by
  set L := Λ_on_circle f hf_pos g with hL_def
  -- Key boundedness lemma
  have h_bound_diff : ∀ Q R : TrigPolyℤ, ‖ΛTrigℤ f Q - ΛTrigℤ f R‖ ≤
      (f 0).re * ‖Q.toCircle - R.toCircle‖ := by
    intro Q R
    have h_lin : ΛTrigℤ f Q - ΛTrigℤ f R = ΛTrigℤ f (Q - R) := by
      have h_neg (S : TrigPolyℤ) : ΛTrigℤ f (-S) = - ΛTrigℤ f S := by
        simpa [one_smul, sub_eq_add_neg] using (ΛTrigℤ_smul (f:=f) (-1 : ℂ) S)
      simp [sub_eq_add_neg, h_neg, ΛTrigℤ_add]
    rw [h_lin]
    have h_toCircle_sub : (Q - R).toCircle = Q.toCircle - R.toCircle := by
      have h_sub : Q - R = Q + ((-1 : ℂ) • R) := by simp [sub_eq_add_neg, neg_one_smul]
      rw [h_sub, TrigPolyℤ.toCircle_add, TrigPolyℤ.toCircle_smul]
      rw [neg_one_smul ℂ R.toCircle, sub_eq_add_neg]
    calc ‖ΛTrigℤ f (Q - R)‖
        ≤ (f 0).re * ‖(Q - R).toCircle‖ := ΛTrigℤ_bounded f hf_pos _
      _ = (f 0).re * ‖Q.toCircle - R.toCircle‖ := by rw [h_toCircle_sub]
  by_cases h_f0_zero : (f 0).re = 0
  · -- If f(0) = 0, all ΛTrigℤ values are 0, so L = 0
    have h_zero : ∀ Q : TrigPolyℤ, ΛTrigℤ f Q = 0 := by
      intro Q
      have h := ΛTrigℤ_bounded f hf_pos Q
      simp only [h_f0_zero, zero_mul, nonpos_iff_eq_zero] at h
      exact norm_le_zero_iff.mp h
    have hL_zero : L = 0 := by
      have approx : ∀ n : ℕ, ∃ Q : TrigPolyℤ,
          ‖g - Q.toCircle‖ < (1 : ℝ) / (n + 1) := by
        intro n
        have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
          have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
          simpa using (one_div_pos.mpr this)
        exact approx_by_trigpoly _ _ hpos
      let Q_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx n)
      have h_seq_zero : ∀ n, ΛTrigℤ f (Q_seq n) = 0 := fun n => h_zero (Q_seq n)
      have h_tends_0 : Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds 0) := by simp_rw [h_seq_zero]; exact tendsto_const_nhds
      have cauchy : CauchySeq (fun n => ΛTrigℤ f (Q_seq n)) := by
        rw [Metric.cauchySeq_iff]; intro ε' hε'; use 0
        intro n _ m _; simp [dist_eq_norm, h_seq_zero, hε']
      have limit_exists : ∃ L' : ℂ, Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds L') := cauchySeq_tendsto_of_complete cauchy
      exact tendsto_nhds_unique (Classical.choose_spec limit_exists) h_tends_0
    rw [hL_zero]
    simp_rw [h_zero]
    exact tendsto_const_nhds
  · -- f(0) > 0 case
    have hf0_pos : 0 < (f 0).re := lt_of_le_of_ne hf_pos.zero_nonneg (Ne.symm h_f0_zero)
    rw [Metric.tendsto_atTop]
    intro δ hδ
    -- First, build the reference approximating sequence Q_seq
    have approx' : ∀ k : ℕ, ∃ Q : TrigPolyℤ, ‖g - Q.toCircle‖ < (1 : ℝ) / (k + 1) := by
      intro k
      have hpos : 0 < ((1 : ℝ) / (k + 1)) := by
        have : (0 : ℝ) < (k + 1 : ℝ) := by exact_mod_cast Nat.succ_pos k
        simpa using (one_div_pos.mpr this)
      exact approx_by_trigpoly g _ hpos
    let Q_seq : ℕ → TrigPolyℤ := fun k => Classical.choose (approx' k)
    have Q_spec : ∀ k, ‖g - (Q_seq k).toCircle‖ < (1 : ℝ) / (k + 1) :=
      fun k => Classical.choose_spec (approx' k)
    have h_tends_L : Filter.Tendsto (fun k => ΛTrigℤ f (Q_seq k)) Filter.atTop (nhds L) := by
      have cauchy : CauchySeq (fun k => ΛTrigℤ f (Q_seq k)) := by
        rw [Metric.cauchySeq_iff]
        intro ε' hε'
        obtain ⟨N, hN⟩ := exists_nat_gt (2 * (f 0).re / ε')
        use N
        intro i hi j hj
        rw [dist_eq_norm]
        have hN' : 2 * (f 0).re / ε' < (N : ℝ) := by exact_mod_cast hN
        have hposN : 0 < (N + 1 : ℝ) := by positivity
        calc ‖ΛTrigℤ f (Q_seq i) - ΛTrigℤ f (Q_seq j)‖
            ≤ (f 0).re * ‖(Q_seq i).toCircle - (Q_seq j).toCircle‖ := h_bound_diff _ _
          _ ≤ (f 0).re * (‖g - (Q_seq i).toCircle‖ + ‖g - (Q_seq j).toCircle‖) := by
              apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
              calc ‖(Q_seq i).toCircle - (Q_seq j).toCircle‖
                  = ‖((Q_seq i).toCircle - g) + (g - (Q_seq j).toCircle)‖ := by ring_nf
                _ ≤ ‖(Q_seq i).toCircle - g‖ + ‖g - (Q_seq j).toCircle‖ := norm_add_le _ _
                _ = ‖g - (Q_seq i).toCircle‖ + ‖g - (Q_seq j).toCircle‖ := by rw [norm_sub_rev]
          _ < (f 0).re * (1 / (i + 1) + 1 / (j + 1)) := by
              apply mul_lt_mul_of_pos_left _ hf0_pos
              exact add_lt_add (Q_spec i) (Q_spec j)
          _ ≤ (f 0).re * (1 / (N + 1) + 1 / (N + 1)) := by
              apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
              have hi_cast : (N + 1 : ℝ) ≤ (i + 1 : ℝ) := by
                exact_mod_cast Nat.add_le_add_right hi 1
              have hj_cast : (N + 1 : ℝ) ≤ (j + 1 : ℝ) := by
                exact_mod_cast Nat.add_le_add_right hj 1
              exact add_le_add (one_div_le_one_div_of_le hposN hi_cast)
                               (one_div_le_one_div_of_le hposN hj_cast)
          _ = 2 * (f 0).re / (N + 1) := by ring
          _ < ε' := by
              rw [div_lt_iff₀ hposN]
              have h1 : 2 * (f 0).re < (N : ℝ) * ε' := by
                have := (div_lt_iff₀ hε').mp hN'
                linarith
              calc 2 * (f 0).re < (N : ℝ) * ε' := h1
                _ < (N + 1 : ℝ) * ε' := by linarith
                _ = ε' * (N + 1 : ℝ) := by ring
      exact Classical.choose_spec (cauchySeq_tendsto_of_complete cauchy)
    -- Now extract the N' for convergence of Q_seq to L
    have hδ2 : 0 < δ / 2 := by linarith
    rw [Metric.tendsto_atTop] at h_tends_L
    obtain ⟨N', hN'⟩ := h_tends_L (δ / 2) hδ2
    -- Get M for the bound: need 4 * (f 0).re / δ < M to get 2*(f 0).re/(M+1) < δ/2
    obtain ⟨M, hM⟩ := exists_nat_gt (4 * (f 0).re / δ)
    -- Use max M N' so we have both bounds
    use max M N'
    intro n hn
    rw [dist_eq_norm]
    have hn_M : n ≥ M := le_trans (le_max_left M N') hn
    have hn_N' : n ≥ N' := le_trans (le_max_right M N') hn
    -- Now show ‖ΛTrigℤ f (P_seq n) - L‖ < δ
    have hM' : 4 * (f 0).re / δ < (M : ℝ) := by exact_mod_cast hM
    have hposM : 0 < (M + 1 : ℝ) := by positivity
    -- Use triangle: ‖P_seq - L‖ ≤ ‖P_seq - Q_seq‖ + ‖Q_seq - L‖
    -- Step 1: Triangle inequality
    have step1 : ‖ΛTrigℤ f (P_seq n) - L‖ ≤
        ‖ΛTrigℤ f (P_seq n) - ΛTrigℤ f (Q_seq n)‖ + ‖ΛTrigℤ f (Q_seq n) - L‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub (ΛTrigℤ f (P_seq n)) (ΛTrigℤ f (Q_seq n)) L
      linarith [this]
    -- Step 2: Bound the first term using h_bound_diff
    have step2 : ‖ΛTrigℤ f (P_seq n) - ΛTrigℤ f (Q_seq n)‖ ≤
        (f 0).re * ‖(P_seq n).toCircle - (Q_seq n).toCircle‖ := h_bound_diff _ _
    -- Step 3: Bound the norm of difference using triangle
    have step3 : ‖(P_seq n).toCircle - (Q_seq n).toCircle‖ ≤
        ‖g - (P_seq n).toCircle‖ + ‖g - (Q_seq n).toCircle‖ := by
      calc ‖(P_seq n).toCircle - (Q_seq n).toCircle‖
          = ‖((P_seq n).toCircle - g) + (g - (Q_seq n).toCircle)‖ := by ring_nf
        _ ≤ ‖(P_seq n).toCircle - g‖ + ‖g - (Q_seq n).toCircle‖ := norm_add_le _ _
        _ = ‖g - (P_seq n).toCircle‖ + ‖g - (Q_seq n).toCircle‖ := by rw [norm_sub_rev]
    -- Step 4: Use the approximation bounds
    have step4 : ‖g - (P_seq n).toCircle‖ + ‖g - (Q_seq n).toCircle‖ <
        1 / (n + 1) + 1 / (n + 1) := add_lt_add (hP n) (Q_spec n)
    -- Step 5: Use monotonicity n ≥ M
    have hn_cast : (M + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hn_M 1
    have step5 : (1 : ℝ) / (n + 1) ≤ 1 / (M + 1) := one_div_le_one_div_of_le hposM hn_cast
    -- Step 6: First bound
    have h_first : 2 * (f 0).re / (M + 1) < δ / 2 := by
      rw [div_lt_iff₀ hposM]
      have h1 : 4 * (f 0).re < (M : ℝ) * δ := by
        have := (div_lt_iff₀ hδ).mp hM'
        linarith
      linarith
    -- Step 7: Second bound from convergence
    have h_second : ‖ΛTrigℤ f (Q_seq n) - L‖ < δ / 2 := by
      have h := hN' n hn_N'
      rw [dist_eq_norm] at h
      exact h
    -- Combine all steps
    have h_combine : ‖ΛTrigℤ f (P_seq n) - L‖ < δ := by
      have h_step2' : ‖ΛTrigℤ f (P_seq n) - ΛTrigℤ f (Q_seq n)‖ ≤
          (f 0).re * (1 / (n + 1) + 1 / (n + 1)) := by
        calc ‖ΛTrigℤ f (P_seq n) - ΛTrigℤ f (Q_seq n)‖
            ≤ (f 0).re * ‖(P_seq n).toCircle - (Q_seq n).toCircle‖ := step2
          _ ≤ (f 0).re * (‖g - (P_seq n).toCircle‖ + ‖g - (Q_seq n).toCircle‖) := by
              apply mul_le_mul_of_nonneg_left step3 hf_pos.zero_nonneg
          _ ≤ (f 0).re * (1 / (n + 1) + 1 / (n + 1)) := by
              apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
              linarith [step4]
      have h_step2'' : ‖ΛTrigℤ f (P_seq n) - ΛTrigℤ f (Q_seq n)‖ ≤
          (f 0).re * (1 / (M + 1) + 1 / (M + 1)) := by
        calc ‖ΛTrigℤ f (P_seq n) - ΛTrigℤ f (Q_seq n)‖
            ≤ (f 0).re * (1 / (n + 1) + 1 / (n + 1)) := h_step2'
          _ ≤ (f 0).re * (1 / (M + 1) + 1 / (M + 1)) := by
              apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
              linarith [step5]
      have h_eq : (f 0).re * (1 / (M + 1) + 1 / (M + 1)) = 2 * (f 0).re / (M + 1) := by ring
      calc ‖ΛTrigℤ f (P_seq n) - L‖
          ≤ ‖ΛTrigℤ f (P_seq n) - ΛTrigℤ f (Q_seq n)‖ + ‖ΛTrigℤ f (Q_seq n) - L‖ := step1
        _ ≤ (f 0).re * (1 / (M + 1) + 1 / (M + 1)) + ‖ΛTrigℤ f (Q_seq n) - L‖ := by
            linarith [h_step2'']
        _ = 2 * (f 0).re / (M + 1) + ‖ΛTrigℤ f (Q_seq n) - L‖ := by rw [h_eq]
        _ < δ / 2 + δ / 2 := by linarith
        _ = δ := by ring
    exact h_combine
/-- PROFINITE ANALOGY LEMMA 2: Λ_on_circle is additive. -/
lemma Λ_on_circle_add (f : ℝ → ℂ) (hf_pos : IsPositiveDefinite f)
    (g₁ g₂ : C(𝕋, ℂ)) :
    Λ_on_circle f hf_pos (g₁ + g₂) =
      Λ_on_circle f hf_pos g₁ + Λ_on_circle f hf_pos g₂ := by
  -- Set names for the three limits
  set L := Λ_on_circle f hf_pos (g₁ + g₂) with hL_def
  set L₁ := Λ_on_circle f hf_pos g₁ with hL₁_def
  set L₂ := Λ_on_circle f hf_pos g₂ with hL₂_def
  -- Key boundedness lemma
  have h_bound_diff : ∀ Q R : TrigPolyℤ, ‖ΛTrigℤ f Q - ΛTrigℤ f R‖ ≤
      (f 0).re * ‖Q.toCircle - R.toCircle‖ := by
    intro Q R
    have h_lin : ΛTrigℤ f Q - ΛTrigℤ f R = ΛTrigℤ f (Q - R) := by
      have h_neg (S : TrigPolyℤ) : ΛTrigℤ f (-S) = - ΛTrigℤ f S := by
        simpa [one_smul, sub_eq_add_neg] using (ΛTrigℤ_smul (f:=f) (-1 : ℂ) S)
      simp [sub_eq_add_neg, h_neg, ΛTrigℤ_add]
    rw [h_lin]
    have h_toCircle_sub : (Q - R).toCircle = Q.toCircle - R.toCircle := by
      have h_sub : Q - R = Q + ((-1 : ℂ) • R) := by simp [sub_eq_add_neg, neg_one_smul]
      rw [h_sub, TrigPolyℤ.toCircle_add, TrigPolyℤ.toCircle_smul]
      rw [neg_one_smul ℂ R.toCircle, sub_eq_add_neg]
    calc ‖ΛTrigℤ f (Q - R)‖
        ≤ (f 0).re * ‖(Q - R).toCircle‖ := ΛTrigℤ_bounded f hf_pos _
      _ = (f 0).re * ‖Q.toCircle - R.toCircle‖ := by rw [h_toCircle_sub]
  -- Show L = L₁ + L₂ by showing distance is arbitrarily small
  suffices ∀ ε > 0, dist L (L₁ + L₂) < ε by
    exact eq_of_forall_dist_le (fun ε hε => le_of_lt (this ε hε))
  intro ε hε
  by_cases h_f0_zero : (f 0).re = 0
  · -- If f(0) = 0, all ΛTrigℤ values are 0
    have h_zero : ∀ Q : TrigPolyℤ, ΛTrigℤ f Q = 0 := by
      intro Q
      have h := ΛTrigℤ_bounded f hf_pos Q
      simp only [h_f0_zero, zero_mul, nonpos_iff_eq_zero] at h
      exact norm_le_zero_iff.mp h
    -- When all ΛTrigℤ are 0, all limits are 0
    have hL_zero : L = 0 := by
      have approx : ∀ n : ℕ, ∃ Q : TrigPolyℤ,
          ‖(g₁ + g₂) - Q.toCircle‖ < (1 : ℝ) / (n + 1) := by
        intro n
        have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
          have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
          simpa using (one_div_pos.mpr this)
        exact approx_by_trigpoly _ _ hpos
      let Q_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx n)
      have h_seq_zero : ∀ n, ΛTrigℤ f (Q_seq n) = 0 := fun n => h_zero (Q_seq n)
      have h_tends_0 : Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds 0) := by simp_rw [h_seq_zero]; exact tendsto_const_nhds
      have cauchy : CauchySeq (fun n => ΛTrigℤ f (Q_seq n)) := by
        rw [Metric.cauchySeq_iff]; intro ε' hε'; use 0
        intro n _ m _; simp [dist_eq_norm, h_seq_zero, hε']
      have limit_exists : ∃ L' : ℂ, Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds L') := cauchySeq_tendsto_of_complete cauchy
      exact tendsto_nhds_unique (Classical.choose_spec limit_exists) h_tends_0
    have hL₁_zero : L₁ = 0 := by
      have approx : ∀ n : ℕ, ∃ Q : TrigPolyℤ,
          ‖g₁ - Q.toCircle‖ < (1 : ℝ) / (n + 1) := by
        intro n
        have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
          have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
          simpa using (one_div_pos.mpr this)
        exact approx_by_trigpoly _ _ hpos
      let Q_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx n)
      have h_seq_zero : ∀ n, ΛTrigℤ f (Q_seq n) = 0 := fun n => h_zero (Q_seq n)
      have h_tends_0 : Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds 0) := by simp_rw [h_seq_zero]; exact tendsto_const_nhds
      have cauchy : CauchySeq (fun n => ΛTrigℤ f (Q_seq n)) := by
        rw [Metric.cauchySeq_iff]; intro ε' hε'; use 0
        intro n _ m _; simp [dist_eq_norm, h_seq_zero, hε']
      have limit_exists : ∃ L' : ℂ, Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds L') := cauchySeq_tendsto_of_complete cauchy
      exact tendsto_nhds_unique (Classical.choose_spec limit_exists) h_tends_0
    have hL₂_zero : L₂ = 0 := by
      have approx : ∀ n : ℕ, ∃ Q : TrigPolyℤ,
          ‖g₂ - Q.toCircle‖ < (1 : ℝ) / (n + 1) := by
        intro n
        have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
          have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
          simpa using (one_div_pos.mpr this)
        exact approx_by_trigpoly _ _ hpos
      let Q_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx n)
      have h_seq_zero : ∀ n, ΛTrigℤ f (Q_seq n) = 0 := fun n => h_zero (Q_seq n)
      have h_tends_0 : Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds 0) := by simp_rw [h_seq_zero]; exact tendsto_const_nhds
      have cauchy : CauchySeq (fun n => ΛTrigℤ f (Q_seq n)) := by
        rw [Metric.cauchySeq_iff]; intro ε' hε'; use 0
        intro n _ m _; simp [dist_eq_norm, h_seq_zero, hε']
      have limit_exists : ∃ L' : ℂ, Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds L') := cauchySeq_tendsto_of_complete cauchy
      exact tendsto_nhds_unique (Classical.choose_spec limit_exists) h_tends_0
    rw [hL_zero, hL₁_zero, hL₂_zero]
    simp [hε]
  · -- f(0) > 0 case: Use the sum approximating sequence
    have hf0_pos : 0 < (f 0).re := lt_of_le_of_ne hf_pos.zero_nonneg (Ne.symm h_f0_zero)
    -- Get approximating sequences for g₁ and g₂
    have approx₁ : ∀ n : ℕ, ∃ P : TrigPolyℤ, ‖g₁ - P.toCircle‖ < (1 : ℝ) / (n + 1) := by
      intro n
      have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
        have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
        simpa using (one_div_pos.mpr this)
      exact approx_by_trigpoly g₁ _ hpos
    have approx₂ : ∀ n : ℕ, ∃ Q : TrigPolyℤ, ‖g₂ - Q.toCircle‖ < (1 : ℝ) / (n + 1) := by
      intro n
      have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
        have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
        simpa using (one_div_pos.mpr this)
      exact approx_by_trigpoly g₂ _ hpos
    let P_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx₁ n)
    let Q_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx₂ n)
    have P_spec : ∀ n, ‖g₁ - (P_seq n).toCircle‖ < (1 : ℝ) / (n + 1) :=
      fun n => Classical.choose_spec (approx₁ n)
    have Q_spec : ∀ n, ‖g₂ - (Q_seq n).toCircle‖ < (1 : ℝ) / (n + 1) :=
      fun n => Classical.choose_spec (approx₂ n)
    -- The combined sequence approximates (g₁ + g₂)
    have sum_spec : ∀ n, ‖(g₁ + g₂) - (P_seq n + Q_seq n).toCircle‖ < 2 / (n + 1) := by
      intro n
      have h_toCircle_add : (P_seq n + Q_seq n).toCircle =
          (P_seq n).toCircle + (Q_seq n).toCircle := TrigPolyℤ.toCircle_add _ _
      calc ‖(g₁ + g₂) - (P_seq n + Q_seq n).toCircle‖
          = ‖(g₁ + g₂) - ((P_seq n).toCircle + (Q_seq n).toCircle)‖ := by rw [h_toCircle_add]
        _ = ‖(g₁ - (P_seq n).toCircle) + (g₂ - (Q_seq n).toCircle)‖ := by ring_nf
        _ ≤ ‖g₁ - (P_seq n).toCircle‖ + ‖g₂ - (Q_seq n).toCircle‖ := norm_add_le _ _
        _ < 1 / (n + 1) + 1 / (n + 1) := add_lt_add (P_spec n) (Q_spec n)
        _ = 2 / (n + 1) := by ring
    -- Key: the sum sequence converges to L (since it approximates g₁ + g₂)
    -- and its ΛTrigℤ values equal ΛTrigℤ(P_seq) + ΛTrigℤ(Q_seq) by linearity
    -- Strategy: show that ΛTrigℤ f (P_seq n + Q_seq n) is Cauchy, hence converges
    -- Then show convergence to both L and L₁ + L₂
    have h_lin : ∀ n, ΛTrigℤ f (P_seq n + Q_seq n) =
        ΛTrigℤ f (P_seq n) + ΛTrigℤ f (Q_seq n) := fun n => ΛTrigℤ_add f (P_seq n) (Q_seq n)
    -- The sum sequence is Cauchy
    have cauchy_sum : CauchySeq (fun n => ΛTrigℤ f (P_seq n + Q_seq n)) := by
      rw [Metric.cauchySeq_iff]
      intro δ hδ
      obtain ⟨N, hN⟩ := exists_nat_gt (4 * (f 0).re / δ)
      use N
      intro n hn m hm
      rw [dist_eq_norm]
      have hN' : 4 * (f 0).re / δ < (N : ℝ) := by exact_mod_cast hN
      have hposN : 0 < (N + 1 : ℝ) := by positivity
      calc ‖ΛTrigℤ f (P_seq n + Q_seq n) - ΛTrigℤ f (P_seq m + Q_seq m)‖
          ≤ (f 0).re * ‖(P_seq n + Q_seq n).toCircle - (P_seq m + Q_seq m).toCircle‖ :=
              h_bound_diff _ _
        _ = (f 0).re * ‖((P_seq n).toCircle + (Q_seq n).toCircle) -
              ((P_seq m).toCircle + (Q_seq m).toCircle)‖ := by
            rw [TrigPolyℤ.toCircle_add, TrigPolyℤ.toCircle_add]
        _ ≤ (f 0).re * (‖(g₁ + g₂) - ((P_seq n).toCircle + (Q_seq n).toCircle)‖ +
              ‖(g₁ + g₂) - ((P_seq m).toCircle + (Q_seq m).toCircle)‖) := by
            apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
            calc ‖((P_seq n).toCircle + (Q_seq n).toCircle) -
                    ((P_seq m).toCircle + (Q_seq m).toCircle)‖
                = ‖(((P_seq n).toCircle + (Q_seq n).toCircle) - (g₁ + g₂)) +
                    ((g₁ + g₂) - ((P_seq m).toCircle + (Q_seq m).toCircle))‖ := by ring_nf
              _ ≤ ‖((P_seq n).toCircle + (Q_seq n).toCircle) - (g₁ + g₂)‖ +
                    ‖(g₁ + g₂) - ((P_seq m).toCircle + (Q_seq m).toCircle)‖ := norm_add_le _ _
              _ = ‖(g₁ + g₂) - ((P_seq n).toCircle + (Q_seq n).toCircle)‖ +
                    ‖(g₁ + g₂) - ((P_seq m).toCircle + (Q_seq m).toCircle)‖ := by rw [norm_sub_rev]
        _ < (f 0).re * (2 / (n + 1) + 2 / (m + 1)) := by
            apply mul_lt_mul_of_pos_left _ hf0_pos
            have hn_spec' : ‖(g₁ + g₂) -
             ((P_seq n).toCircle + (Q_seq n).toCircle)‖ < 2 / (n + 1) := by
              have h := sum_spec n
              rw [TrigPolyℤ.toCircle_add] at h
              exact h
            have hm_spec' : ‖(g₁ + g₂) -
             ((P_seq m).toCircle + (Q_seq m).toCircle)‖ < 2 / (m + 1) := by
              have h := sum_spec m
              rw [TrigPolyℤ.toCircle_add] at h
              exact h
            exact add_lt_add hn_spec' hm_spec'
        _ ≤ (f 0).re * (2 / (N + 1) + 2 / (N + 1)) := by
            apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
            have hn_cast : (N + 1 : ℝ) ≤ (n + 1 : ℝ) := by
              exact_mod_cast Nat.add_le_add_right hn 1
            have hm_cast : (N + 1 : ℝ) ≤ (m + 1 : ℝ) := by
              exact_mod_cast Nat.add_le_add_right hm 1
            have h1 : 2 / (n + 1 : ℝ) ≤ 2 / (N + 1 : ℝ) :=
              div_le_div_of_nonneg_left (by linarith) hposN hn_cast
            have h2 : 2 / (m + 1 : ℝ) ≤ 2 / (N + 1 : ℝ) :=
              div_le_div_of_nonneg_left (by linarith) hposN hm_cast
            linarith
        _ = 4 * (f 0).re / (N + 1) := by ring
        _ < δ := by
            rw [div_lt_iff₀ hposN]
            have h1 : 4 * (f 0).re < (N : ℝ) * δ := by
              have := (div_lt_iff₀ hδ).mp hN'
              linarith
            calc 4 * (f 0).re < (N : ℝ) * δ := h1
              _ < (N + 1 : ℝ) * δ := by linarith
              _ = δ * (N + 1 : ℝ) := by ring
    -- Strategy: Show the sum sequence converges, and by uniqueness with
    -- the defining sequence for L, we get convergence to L.
    -- Then show convergence to L₁ + L₂ using linearity.
    have limit_sum := cauchySeq_tendsto_of_complete cauchy_sum
    let L_sum := Classical.choose limit_sum
    have h_tends_L_sum : Filter.Tendsto (fun n => ΛTrigℤ f (P_seq n + Q_seq n))
        Filter.atTop (nhds L_sum) := Classical.choose_spec limit_sum
    -- Key: L_sum = L because both are limits of approximating sequences for g₁ + g₂
    -- Use the "any approximating sequence gives the same limit" principle
    have h_L_eq_L_sum : L = L_sum := by
      -- Both L and L_sum are limits of Cauchy sequences of ΛTrigℤ values
      -- for approximating sequences of g₁ + g₂. By uniqueness of limits, L = L_sum.
      -- This follows from showing L_sum = L directly via limit uniqueness.
      suffices ∀ ε' > 0, dist L L_sum < ε' by
        exact eq_of_forall_dist_le (fun ε' hε' => le_of_lt (this ε' hε'))
      intro ε' hε'
      -- Get N large enough: need 9 * (f 0).re / ε' < M to get 3*(f 0).re/(M+1) < ε'/3
      obtain ⟨M, hM⟩ := exists_nat_gt (9 * (f 0).re / ε')
      have hM' : 9 * (f 0).re / ε' < (M : ℝ) := by exact_mod_cast hM
      have hposM : 0 < (M + 1 : ℝ) := by positivity
      -- Both sequences eventually get close to their respective limits
      rw [Metric.tendsto_atTop] at h_tends_L_sum
      obtain ⟨N₁, hN₁⟩ := h_tends_L_sum (ε' / 3) (by linarith)
      -- For L, we use that the defining sequence also converges
      -- The defining sequence for L approximates g₁ + g₂ with error < 1/(n+1)
      have approx_L : ∀ n : ℕ, ∃ R : TrigPolyℤ,
          ‖(g₁ + g₂) - R.toCircle‖ < (1 : ℝ) / (n + 1) := by
        intro n
        have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
          have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
          simpa using (one_div_pos.mpr this)
        exact approx_by_trigpoly _ _ hpos
      let R_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx_L n)
      have R_spec : ∀ n, ‖(g₁ + g₂) - (R_seq n).toCircle‖ < (1 : ℝ) / (n + 1) :=
        fun n => Classical.choose_spec (approx_L n)
      have cauchy_R : CauchySeq (fun n => ΛTrigℤ f (R_seq n)) := by
        rw [Metric.cauchySeq_iff]
        intro δ hδ
        obtain ⟨N, hN⟩ := exists_nat_gt (2 * (f 0).re / δ)
        use N
        intro n hn m hm
        rw [dist_eq_norm]
        have hN'' : 2 * (f 0).re / δ < (N : ℝ) := by exact_mod_cast hN
        have hposN : 0 < (N + 1 : ℝ) := by positivity
        calc ‖ΛTrigℤ f (R_seq n) - ΛTrigℤ f (R_seq m)‖
            ≤ (f 0).re * ‖(R_seq n).toCircle - (R_seq m).toCircle‖ := h_bound_diff _ _
          _ ≤ (f 0).re * (‖(g₁ + g₂) - (R_seq n).toCircle‖ +
                ‖(g₁ + g₂) - (R_seq m).toCircle‖) := by
              apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
              calc ‖(R_seq n).toCircle - (R_seq m).toCircle‖
                  = ‖((R_seq n).toCircle - (g₁ + g₂)) + ((g₁ + g₂) - (R_seq m).toCircle)‖ := by
                      ring_nf
                _ ≤ ‖(R_seq n).toCircle - (g₁ + g₂)‖ + ‖(g₁ + g₂) - (R_seq m).toCircle‖ :=
                      norm_add_le _ _
                _ = ‖(g₁ + g₂) - (R_seq n).toCircle‖ + ‖(g₁ + g₂) - (R_seq m).toCircle‖ := by
                      rw [norm_sub_rev]
          _ < (f 0).re * (1 / (n + 1) + 1 / (m + 1)) := by
              apply mul_lt_mul_of_pos_left _ hf0_pos
              exact add_lt_add (R_spec n) (R_spec m)
          _ ≤ (f 0).re * (1 / (N + 1) + 1 / (N + 1)) := by
              apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
              have hn_cast : (N + 1 : ℝ) ≤ (n + 1 : ℝ) := by
                exact_mod_cast Nat.add_le_add_right hn 1
              have hm_cast : (N + 1 : ℝ) ≤ (m + 1 : ℝ) := by
                exact_mod_cast Nat.add_le_add_right hm 1
              exact add_le_add (one_div_le_one_div_of_le hposN hn_cast)
                               (one_div_le_one_div_of_le hposN hm_cast)
          _ = 2 * (f 0).re / (N + 1) := by ring
          _ < δ := by
              rw [div_lt_iff₀ hposN]
              have h1 : 2 * (f 0).re < (N : ℝ) * δ := by
                have := (div_lt_iff₀ hδ).mp hN''
                linarith
              calc 2 * (f 0).re < (N : ℝ) * δ := h1
                _ < (N + 1 : ℝ) * δ := by linarith
                _ = δ * (N + 1 : ℝ) := by ring
      -- R_seq converges to L by Λ_on_circle_approx_tendsto
      have h_tends_R_to_L : Filter.Tendsto (fun n => ΛTrigℤ f (R_seq n))
          Filter.atTop (nhds L) := Λ_on_circle_approx_tendsto f hf_pos (g₁ + g₂) R_seq R_spec
      -- Now use triangle inequality: dist L L_sum ≤ dist L (ΛTrigℤ f (R_seq n)) +
      --   dist (ΛTrigℤ f (R_seq n)) (ΛTrigℤ f (P_seq n + Q_seq n)) +
      --   dist (ΛTrigℤ f (P_seq n + Q_seq n)) L_sum
      rw [Metric.tendsto_atTop] at h_tends_R_to_L
      obtain ⟨N₂, hN₂⟩ := h_tends_R_to_L (ε' / 3) (by linarith)
      -- Pick n large enough for both convergences and the approximation bound
      let n := max (max M N₁) N₂
      have hn_M : n ≥ M := le_trans (le_max_left M N₁) (le_max_left _ N₂)
      have hn_N₁ : n ≥ N₁ := le_trans (le_max_right M N₁) (le_max_left _ N₂)
      have hn_N₂ : n ≥ N₂ := le_max_right _ N₂
      have h1 : dist (ΛTrigℤ f (R_seq n)) L < ε' / 3 := hN₂ n hn_N₂
      have h2 : dist (ΛTrigℤ f (P_seq n + Q_seq n)) L_sum < ε' / 3 := hN₁ n hn_N₁
      -- Both approximate g₁ + g₂, so their ΛTrigℤ values are close
      have h3 : dist (ΛTrigℤ f (R_seq n)) (ΛTrigℤ f (P_seq n + Q_seq n)) < ε' / 3 := by
        rw [dist_eq_norm]
        have hR := R_spec n
        have hS : ‖(g₁ + g₂) - (P_seq n + Q_seq n).toCircle‖ < 2 / (n + 1) := sum_spec n
        have hposn : 0 < (n + 1 : ℝ) := by positivity
        calc ‖ΛTrigℤ f (R_seq n) - ΛTrigℤ f (P_seq n + Q_seq n)‖
            ≤ (f 0).re * ‖(R_seq n).toCircle - (P_seq n + Q_seq n).toCircle‖ := h_bound_diff _ _
          _ ≤ (f 0).re * (‖(g₁ + g₂) - (R_seq n).toCircle‖ +
                ‖(g₁ + g₂) - (P_seq n + Q_seq n).toCircle‖) := by
              apply mul_le_mul_of_nonneg_left _ hf_pos.zero_nonneg
              calc ‖(R_seq n).toCircle - (P_seq n + Q_seq n).toCircle‖
                  = ‖((R_seq n).toCircle - (g₁ + g₂)) +
                      ((g₁ + g₂) - (P_seq n + Q_seq n).toCircle)‖ := by ring_nf
                _ ≤ ‖(R_seq n).toCircle - (g₁ + g₂)‖ +
                      ‖(g₁ + g₂) - (P_seq n + Q_seq n).toCircle‖ := norm_add_le _ _
                _ = ‖(g₁ + g₂) - (R_seq n).toCircle‖ +
                      ‖(g₁ + g₂) - (P_seq n + Q_seq n).toCircle‖ := by rw [norm_sub_rev]
          _ < (f 0).re * (1 / (n + 1) + 2 / (n + 1)) := by
              apply mul_lt_mul_of_pos_left _ hf0_pos
              exact add_lt_add hR hS
          _ = 3 * (f 0).re / (n + 1) := by ring
          _ ≤ 3 * (f 0).re / (M + 1) := by
              have h_numer_nonneg : 0 ≤ 3 * (f 0).re := by
                have := hf_pos.zero_nonneg
                linarith
              have h_denom_le : (M + 1 : ℝ) ≤ (n + 1 : ℝ) := by
                exact_mod_cast Nat.add_le_add_right hn_M 1
              exact div_le_div_of_nonneg_left h_numer_nonneg hposM h_denom_le
          _ < ε' / 3 := by
              rw [div_lt_iff₀ hposM]
              -- Goal: 3 * (f 0).re < ε' / 3 * (M + 1)
              -- From 9 * (f 0).re / ε' < M, we get 9 * (f 0).re < M * ε' ≤ (M + 1) * ε'
              -- So 3 * (f 0).re < (M + 1) * ε' / 3 = ε' / 3 * (M + 1)
              have h1 : 9 * (f 0).re < (M : ℝ) * ε' := by
                have := (div_lt_iff₀ hε').mp hM'
                linarith
              have h2 : 9 * (f 0).re < (M + 1 : ℝ) * ε' := by linarith
              linarith
      calc dist L L_sum
          ≤ dist L (ΛTrigℤ f (R_seq n)) + dist (ΛTrigℤ f (R_seq n)) L_sum := dist_triangle _ _ _
        _ ≤ dist L (ΛTrigℤ f (R_seq n)) +
         (dist (ΛTrigℤ f (R_seq n)) (ΛTrigℤ f (P_seq n + Q_seq n)) +
              dist (ΛTrigℤ f (P_seq n + Q_seq n)) L_sum) := by
            linarith [dist_triangle (ΛTrigℤ f (R_seq n)) (ΛTrigℤ f (P_seq n + Q_seq n)) L_sum]
        _ < ε' / 3 + (ε' / 3 + ε' / 3) := by
            have h1' : dist L (ΛTrigℤ f (R_seq n)) < ε' / 3 := by rw [dist_comm]; exact h1
            linarith [h1', h2, h3]
        _ = ε' := by ring
    -- Now h_tends_L_sum : ... → L_sum and h_L_eq_L_sum : L = L_sum
    -- So the sum sequence → L
    have h_tends_L : Filter.Tendsto (fun n => ΛTrigℤ f (P_seq n + Q_seq n))
        Filter.atTop (nhds L) := by
      rw [h_L_eq_L_sum]
      exact h_tends_L_sum
    -- The sum sequence also converges to L₁ + L₂ by linearity
    have h_tends_L₁L₂ : Filter.Tendsto (fun n => ΛTrigℤ f (P_seq n + Q_seq n))
        Filter.atTop (nhds (L₁ + L₂)) := by
      simp_rw [h_lin]
      -- P_seq → L₁ and Q_seq → L₂ by Λ_on_circle_approx_tendsto
      have h_P_tends : Filter.Tendsto (fun n => ΛTrigℤ f (P_seq n))
          Filter.atTop (nhds L₁) := Λ_on_circle_approx_tendsto f hf_pos g₁ P_seq P_spec
      have h_Q_tends : Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
          Filter.atTop (nhds L₂) := Λ_on_circle_approx_tendsto f hf_pos g₂ Q_seq Q_spec
      exact Filter.Tendsto.add h_P_tends h_Q_tends
    -- By uniqueness of limits, L = L₁ + L₂
    rw [dist_eq_norm]
    have h_eq := tendsto_nhds_unique h_tends_L h_tends_L₁L₂
    rw [h_eq]
    simp [hε]

/-- PROFINITE ANALOGY LEMMA 3: Λ_on_circle is homogeneous. -/
lemma Λ_on_circle_smul (f : ℝ → ℂ) (hf_pos : IsPositiveDefinite f)
    (c : ℂ) (g : C(𝕋, ℂ)) :
    Λ_on_circle f hf_pos (c • g) = c * Λ_on_circle f hf_pos g := by
  -- Special case c = 0
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul ℂ g, zero_mul]
    have h0 : (0 : C(𝕋, ℂ)) = (0 : TrigPolyℤ).toCircle := by
      ext θ; simp [TrigPolyℤ.toCircle]
    rw [h0]
    exact Λ_on_circle_constant_seq f hf_pos (0 : TrigPolyℤ)
  -- c ≠ 0 case: use distance argument like Λ_on_circle_add
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set L := Λ_on_circle f hf_pos (c • g) with hL_def
  set L' := c * Λ_on_circle f hf_pos g with hL'_def
  -- Show L = L' by showing distance is arbitrarily small
  suffices ∀ ε > 0, dist L L' < ε by
    exact eq_of_forall_dist_le (fun ε hε => le_of_lt (this ε hε))
  intro ε hε
  -- Get approximating sequence for g
  have approx : ∀ n : ℕ, ∃ P : TrigPolyℤ, ‖g - P.toCircle‖ < (1 : ℝ) / (n + 1) := by
    intro n
    have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
      have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      simpa using (one_div_pos.mpr this)
    exact approx_by_trigpoly g _ hpos
  let P_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx n)
  have P_spec : ∀ n, ‖g - (P_seq n).toCircle‖ < (1 : ℝ) / (n + 1) :=
    fun n => Classical.choose_spec (approx n)
  -- P_seq → Λ_on_circle f hf_pos g
  have h_P_tends : Filter.Tendsto (fun n => ΛTrigℤ f (P_seq n))
      Filter.atTop (nhds (Λ_on_circle f hf_pos g)) :=
    Λ_on_circle_approx_tendsto f hf_pos g P_seq P_spec
  -- c • P_seq → c * Λ_on_circle f hf_pos g = L' by linearity
  have h_lin : ∀ n, ΛTrigℤ f (c • P_seq n) = c * ΛTrigℤ f (P_seq n) :=
    fun n => ΛTrigℤ_smul f c (P_seq n)
  have h_scaled_tends : Filter.Tendsto (fun n => ΛTrigℤ f (c • P_seq n))
      Filter.atTop (nhds L') := by
    simp_rw [h_lin]
    exact Filter.Tendsto.const_mul c h_P_tends
  -- Get approximating sequence for c • g directly
  have approx_cg : ∀ n : ℕ, ∃ Q : TrigPolyℤ, ‖(c • g) - Q.toCircle‖ < (1 : ℝ) / (n + 1) := by
    intro n
    have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
      have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      simpa using (one_div_pos.mpr this)
    exact approx_by_trigpoly (c • g) _ hpos
  let Q_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx_cg n)
  have Q_spec : ∀ n, ‖(c • g) - (Q_seq n).toCircle‖ < (1 : ℝ) / (n + 1) :=
    fun n => Classical.choose_spec (approx_cg n)
  -- Q_seq → L = Λ_on_circle f hf_pos (c • g)
  have h_Q_tends : Filter.Tendsto (fun n => ΛTrigℤ f (Q_seq n))
      Filter.atTop (nhds L) :=
    Λ_on_circle_approx_tendsto f hf_pos (c • g) Q_seq Q_spec
  -- Strategy: show that c • P_seq approximates c • g well enough to use uniqueness
  -- Key observation: ‖(c • g) - (c • P).toCircle‖ = ‖c‖ * ‖g - P.toCircle‖
  have h_approx_cP : ∀ n, ‖(c • g) - (c • P_seq n).toCircle‖ < ‖c‖ * (1 / (n + 1)) := by
    intro n
    rw [TrigPolyℤ.toCircle_smul]
    rw [show c • g - c • (P_seq n).toCircle = c • (g - (P_seq n).toCircle) from (smul_sub c g _).symm]
    rw [norm_smul]
    exact mul_lt_mul_of_pos_left (P_spec n) hc_pos
  -- But we need rate 1/(n+1), not ‖c‖/(n+1). So we re-index.
  -- Choose k(n) large enough that ‖c‖/(k(n)+1) ≤ 1/(n+1)
  -- i.e., k(n) ≥ ‖c‖(n+1) - 1
  -- We'll use k(n) = ⌈‖c‖(n+1)⌉ to ensure k(n)+1 ≥ ‖c‖(n+1)
  let k : ℕ → ℕ := fun n => Nat.ceil (‖c‖ * (n + 1 : ℝ))
  have h_cP_approx : ∀ n, ‖(c • g) - (c • P_seq (k n)).toCircle‖ < (1 : ℝ) / (n + 1) := by
    intro n
    rw [TrigPolyℤ.toCircle_smul]
    rw [show c • g - c • (P_seq (k n)).toCircle = c • (g - (P_seq (k n)).toCircle) from (smul_sub c g _).symm]
    rw [norm_smul]
    have h_Pk : ‖g - (P_seq (k n)).toCircle‖ < (1 : ℝ) / (k n + 1) := P_spec (k n)
    apply lt_of_lt_of_le (mul_lt_mul_of_pos_left h_Pk hc_pos)
    rw [mul_one_div]
    -- Need to show: ‖c‖ / (k n + 1) ≤ 1 / (n + 1)
    have h_ceil : ‖c‖ * (n + 1 : ℝ) ≤ (k n : ℝ) := Nat.le_ceil _
    have h_pos_kn : (0 : ℝ) < (k n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos (k n)
    have h_pos_n : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
    -- We'll show ‖c‖ ≤ (k n + 1) / (n + 1), which gives the desired inequality
    suffices h_suff : ‖c‖ * (n + 1) ≤ (k n + 1 : ℝ) by
      have h_mid : ‖c‖ ≤ (k n + 1 : ℝ) / (n + 1) := by
        have : ‖c‖ * (n + 1) / (n + 1) ≤ (k n + 1 : ℝ) / (n + 1) :=
          div_le_div_of_nonneg_right h_suff (le_of_lt h_pos_n)
        simp only [mul_div_assoc] at this
        rwa [div_self (ne_of_gt h_pos_n), mul_one] at this
      calc ‖c‖ / (k n + 1 : ℝ)
          ≤ ((k n + 1) / (n + 1)) / (k n + 1) := by
              apply div_le_div_of_nonneg_right h_mid (le_of_lt h_pos_kn)
        _ = 1 / (n + 1) := by field_simp
    linarith [h_ceil]
  -- Now c • P_seq ∘ k also converges to L
  have h_cP_k_tends : Filter.Tendsto (fun n => ΛTrigℤ f (c • P_seq (k n)))
      Filter.atTop (nhds L) := by
    -- Use Λ_on_circle_approx_tendsto with the reindexed sequence
    have h_seq_spec : ∀ n, ‖(c • g) - (c • P_seq (k n)).toCircle‖ < (1 : ℝ) / (n + 1) :=
      h_cP_approx
    exact Λ_on_circle_approx_tendsto f hf_pos (c • g) (fun n => c • P_seq (k n)) h_seq_spec
  -- But ΛTrigℤ f (c • P_seq (k n)) = c * ΛTrigℤ f (P_seq (k n))
  have h_eq_scaled : ∀ n, ΛTrigℤ f (c • P_seq (k n)) = c * ΛTrigℤ f (P_seq (k n)) :=
    fun n => ΛTrigℤ_smul f c (P_seq (k n))
  -- k tends to infinity, so P_seq ∘ k → Λ_on_circle f hf_pos g as well
  have h_k_atTop : Filter.Tendsto k Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    use Nat.ceil (b / ‖c‖) + 1
    intro n hn
    have h_pos_c : 0 < ‖c‖ := hc_pos
    have h_bound : (n + 1 : ℝ) ≥ (Nat.ceil (b / ‖c‖) + 1 + 1 : ℝ) := by
      have : Nat.ceil (b / ‖c‖) + 1 + 1 ≤ n + 1 := by omega
      exact_mod_cast this
    have h_div_bound : (Nat.ceil (b / ‖c‖) + 1 + 1 : ℝ) ≥ b / ‖c‖ + 1 := by
      have := Nat.le_ceil (b / ‖c‖)
      linarith
    have h_final : (k n : ℝ) ≥ (b : ℝ) := by
      calc (k n : ℝ)
          ≥ ‖c‖ * (n + 1 : ℝ) := Nat.le_ceil _
        _ ≥ ‖c‖ * (Nat.ceil (b / ‖c‖) + 1 + 1 : ℝ) := by
            apply mul_le_mul_of_nonneg_left h_bound (le_of_lt h_pos_c)
        _ ≥ ‖c‖ * (b / ‖c‖ + 1) := by
            apply mul_le_mul_of_nonneg_left h_div_bound (le_of_lt h_pos_c)
        _ = (b : ℝ) + ‖c‖ := by field_simp
        _ ≥ (b : ℝ) := by linarith
    have h_ceil_b : Nat.ceil (b : ℝ) = b := Nat.ceil_natCast b
    rw [← h_ceil_b]
    exact Nat.ceil_le.mpr h_final
  have h_Pk_tends : Filter.Tendsto (fun n => ΛTrigℤ f (P_seq (k n)))
      Filter.atTop (nhds (Λ_on_circle f hf_pos g)) :=
    h_P_tends.comp h_k_atTop
  have h_cPk_tends' : Filter.Tendsto (fun n => c * ΛTrigℤ f (P_seq (k n)))
      Filter.atTop (nhds (c * Λ_on_circle f hf_pos g)) :=
    Filter.Tendsto.const_mul c h_Pk_tends
  -- Now h_cP_k_tends : ... → L and h_cPk_tends' : ... → c * Λ(...g) = L'
  simp_rw [h_eq_scaled] at h_cP_k_tends
  have h_eq : L = L' := tendsto_nhds_unique h_cP_k_tends h_cPk_tends'
  rw [h_eq, dist_self]
  exact hε

/-- For functions in the span of trig polys, Λ can be computed -/
lemma Λ_on_span (f : ℝ → ℂ) (hf_pos : IsPositiveDefinite f) (g : C(𝕋, ℂ))
    (hg : g ∈ Submodule.span ℂ (Set.range TrigPolyℤ.toCircle)) :
    ∃ (val : ℂ), Λ_on_circle f hf_pos g = val ∧
    ∀ P : TrigPolyℤ, g = P.toCircle → val = ΛTrigℤ f P := by
  -- Use span induction: prove the property for all elements in the span
  induction hg using Submodule.span_induction with
  | mem x hx =>
      -- BASE CASE: x ∈ range TrigPolyℤ.toCircle (like "θ is a character")
      obtain ⟨P, rfl⟩ := hx
      use ΛTrigℤ f P
      constructor
      · -- Λ_on_circle(P.toCircle) = ΛTrigℤ(P) by constant sequence lemma
        exact Λ_on_circle_constant_seq f hf_pos P
      · intro Q hQ
      -- If P.toCircle = Q.toCircle then P = Q by Fourier uniqueness
        have : P = Q := TrigPolyℤ.toCircle_injective hQ
        rw [this]
  | zero =>
      -- ZERO CASE: special case of base case with P = 0
      use 0
      constructor
      · -- 0 = (0 : TrigPolyℤ).toCircle, so use base case
        have : (0 : C(𝕋, ℂ)) = (0 : TrigPolyℤ).toCircle := by
          ext θ; simp [TrigPolyℤ.toCircle]
        rw [this]
        exact Λ_on_circle_constant_seq f hf_pos 0
      · intro P hP
      -- If 0 = P.toCircle, then P = 0 by injectivity
        have : P = 0 := TrigPolyℤ.toCircle_injective hP.symm
        simp [this, ΛTrigℤ]
  | add g₁ g₂ _hg₁ _hg₂ ih₁ ih₂ =>
      -- uses Λ_on_circle_add
      obtain ⟨v₁, h₁₁, h₁₂⟩ := ih₁
      obtain ⟨v₂, h₂₁, h₂₂⟩ := ih₂
      use v₁ + v₂
      constructor
      · -- Λ(g₁ + g₂) = Λ(g₁) + Λ(g₂) = v₁ + v₂
        calc Λ_on_circle f hf_pos (g₁ + g₂)
            = Λ_on_circle f hf_pos g₁ + Λ_on_circle f hf_pos g₂ :=
                Λ_on_circle_add f hf_pos g₁ g₂
          _ = v₁ + v₂ := by rw [h₁₁, h₂₁]
      · intro P hP
      -- If g₁ + g₂ = P.toCircle, then v₁ + v₂ = ΛTrigℤ f P
      -- by using the constant sequence lemma on P
        have : ΛTrigℤ f P = Λ_on_circle f hf_pos (P.toCircle) :=
          (Λ_on_circle_constant_seq f hf_pos P).symm
        rw [this, ← hP]
      -- Now LHS = Λ(g₁ + g₂) = v₁ + v₂ by first part
        symm
        calc Λ_on_circle f hf_pos (g₁ + g₂)
            = Λ_on_circle f hf_pos g₁ + Λ_on_circle f hf_pos g₂ :=
                Λ_on_circle_add f hf_pos g₁ g₂
          _ = v₁ + v₂ := by rw [h₁₁, h₂₁]
  | smul c g₁ _hg₁ ih₁ =>
      -- SCALAR CASE: uses Λ_on_circle_smul
      obtain ⟨v, hv₁, hv₂⟩ := ih₁
      use c * v
      constructor
      · -- Λ(c • g) = c * Λ(g) = c * v
        calc Λ_on_circle f hf_pos (c • g₁)
            = c * Λ_on_circle f hf_pos g₁ := Λ_on_circle_smul f hf_pos c g₁
          _ = c * v := by rw [hv₁]
      · intro P hP
        have : ΛTrigℤ f P = Λ_on_circle f hf_pos (P.toCircle) :=
          (Λ_on_circle_constant_seq f hf_pos P).symm
        rw [this, ← hP]
        symm
        calc Λ_on_circle f hf_pos (c • g₁)
            = c * Λ_on_circle f hf_pos g₁ := Λ_on_circle_smul f hf_pos c g₁
          _ = c * v := by rw [hv₁]

/-- Λ agrees with ΛTrigℤ on trigonometric polynomials.
    This is the key property that allows us to extend the functional.

    Direct corollary of Λ_on_span with the base case. -/
lemma Λ_on_circle_eq_ΛTrigℤ (f : ℝ → ℂ) (hf_pos : IsPositiveDefinite f) (P : TrigPolyℤ) :
    Λ_on_circle f hf_pos (P.toCircle) = ΛTrigℤ f P := by
  exact Λ_on_circle_constant_seq f hf_pos P

/-- Λ is continuous (bounded) as a functional on C(𝕋, ℂ). -/
lemma Λ_on_circle_continuous (f : ℝ → ℂ) (hf_pos : IsPositiveDefinite f) :
    Continuous (Λ_on_circle f hf_pos) := by
  -- Show sequential continuity: g_n → g implies Λ(g_n) → Λ(g)
  -- This is sufficient for continuity on a metric space
  rw [Metric.continuous_iff]
  intro g ε hε
  -- We need to find δ > 0 such that ‖h - g‖ < δ implies ‖Λ(h) - Λ(g)‖ < ε
  by_cases h_f0_zero : (f 0).re = 0
  · -- If f(0) = 0, then Λ is identically 0
    use 1
    constructor
    · linarith
    intro h _
    have h_zero : ∀ P : TrigPolyℤ, ΛTrigℤ f P = 0 := by
      intro P
      have h_bound := ΛTrigℤ_bounded f hf_pos P
      simp only [h_f0_zero, zero_mul, nonpos_iff_eq_zero] at h_bound
      exact norm_le_zero_iff.mp h_bound
    -- Therefore Λ(g) = 0 for all g (by approximation)
    have Λ_zero : ∀ g : C(𝕋, ℂ), Λ_on_circle f hf_pos g = 0 := by
      intro g'
      have approx : ∀ n : ℕ, ∃ P : TrigPolyℤ, ‖g' - P.toCircle‖ < (1 : ℝ) / (n + 1) := by
        intro n
        have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
          have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
          simpa using (one_div_pos.mpr this)
        exact approx_by_trigpoly g' _ hpos
      let P_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx n)
      have h_seq_zero : ∀ n, ΛTrigℤ f (P_seq n) = 0 := fun n => h_zero (P_seq n)
      have h_tends_0 : Filter.Tendsto (fun n => ΛTrigℤ f (P_seq n))
          Filter.atTop (nhds 0) := by simp_rw [h_seq_zero]; exact tendsto_const_nhds
      have P_spec : ∀ n, ‖g' - (P_seq n).toCircle‖ < (1 : ℝ) / (n + 1) :=
        fun n => Classical.choose_spec (approx n)
      have h_tends_L : Filter.Tendsto (fun n => ΛTrigℤ f (P_seq n))
          Filter.atTop (nhds (Λ_on_circle f hf_pos g')) :=
        Λ_on_circle_approx_tendsto f hf_pos g' P_seq P_spec
      have : Λ_on_circle f hf_pos g' = 0 := tendsto_nhds_unique h_tends_L h_tends_0
      exact this
    simp [Λ_zero, hε]
  -- Main case: f(0) > 0
  have hf_pos_re : 0 < (f 0).re := by
    push_neg at h_f0_zero
    exact (f_zero_real_nonneg f hf_pos).2.lt_of_ne h_f0_zero.symm
  use ε / (f 0).re
  constructor
  · exact div_pos hε hf_pos_re
  intro h h_dist
  -- Use the triangle inequality with approximating sequences
  -- Strategy: approximate both g and h, use boundedness
  have h_bound_diff : ∀ g₁ g₂ : C(𝕋, ℂ),
      ‖Λ_on_circle f hf_pos g₁ - Λ_on_circle f hf_pos g₂‖ ≤ (f 0).re * ‖g₁ - g₂‖ := by
    intro g₁ g₂
    -- Get approximating sequences
    have approx₁ : ∀ n : ℕ, ∃ P : TrigPolyℤ, ‖g₁ - P.toCircle‖ < (1 : ℝ) / (n + 1) := by
      intro n; have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
        have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
        simpa using (one_div_pos.mpr this)
      exact approx_by_trigpoly g₁ _ hpos
    have approx₂ : ∀ n : ℕ, ∃ Q : TrigPolyℤ, ‖g₂ - Q.toCircle‖ < (1 : ℝ) / (n + 1) := by
      intro n; have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
        have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
        simpa using (one_div_pos.mpr this)
      exact approx_by_trigpoly g₂ _ hpos
    -- The bound follows from the bound on ΛTrigℤ and taking limits
    -- Strategy: Use linearity to write Λ(g₁) - Λ(g₂) = Λ(g₁ - g₂)
    have h_linear_diff : Λ_on_circle f hf_pos g₁ - Λ_on_circle f hf_pos g₂ =
        Λ_on_circle f hf_pos (g₁ - g₂) := by
      have h_add := Λ_on_circle_add f hf_pos g₁ (-g₂)
      have h_smul := Λ_on_circle_smul f hf_pos (-1 : ℂ) g₂
      rw [neg_one_smul ℂ g₂, neg_one_mul] at h_smul
      calc Λ_on_circle f hf_pos g₁ - Λ_on_circle f hf_pos g₂
          = Λ_on_circle f hf_pos g₁ + (-Λ_on_circle f hf_pos g₂) := by ring
        _ = Λ_on_circle f hf_pos g₁ + Λ_on_circle f hf_pos (-g₂) := by rw [← h_smul]
        _ = Λ_on_circle f hf_pos (g₁ + (-g₂)) := by rw [← h_add]
        _ = Λ_on_circle f hf_pos (g₁ - g₂) := by simp [sub_eq_add_neg]
    rw [h_linear_diff]
    -- Now approximate g₁ - g₂ and use ΛTrigℤ_bounded in the limit
    have approx_diff : ∀ n : ℕ, ∃ R : TrigPolyℤ, ‖(g₁ - g₂) - R.toCircle‖ < (1 : ℝ) / (n + 1) := by
      intro n; have hpos : 0 < ((1 : ℝ) / (n + 1)) := by
        have : (0 : ℝ) < (n + 1 : ℝ) := by exact_mod_cast Nat.succ_pos n
        simpa using (one_div_pos.mpr this)
      exact approx_by_trigpoly (g₁ - g₂) _ hpos
    let R_seq : ℕ → TrigPolyℤ := fun n => Classical.choose (approx_diff n)
    have R_spec : ∀ n, ‖(g₁ - g₂) - (R_seq n).toCircle‖ < (1 : ℝ) / (n + 1) :=
      fun n => Classical.choose_spec (approx_diff n)
    -- R_seq → Λ(g₁ - g₂)
    have h_R_tends : Filter.Tendsto (fun n => ΛTrigℤ f (R_seq n))
        Filter.atTop (nhds (Λ_on_circle f hf_pos (g₁ - g₂))) :=
      Λ_on_circle_approx_tendsto f hf_pos (g₁ - g₂) R_seq R_spec
    -- For each n: ‖ΛTrigℤ f (R_seq n)‖ ≤ (f 0).re * ‖(R_seq n).toCircle‖
    have h_bound_seq : ∀ n, ‖ΛTrigℤ f (R_seq n)‖ ≤ (f 0).re * ‖(R_seq n).toCircle‖ :=
      fun n => ΛTrigℤ_bounded f hf_pos (R_seq n)
    -- And ‖(R_seq n).toCircle‖ ≤ ‖g₁ - g₂‖ + ‖(g₁ - g₂) - (R_seq n).toCircle‖
    have h_trig_norm_bound : ∀ n, ‖(R_seq n).toCircle‖ ≤ ‖g₁ - g₂‖ + 1 / (n + 1) := by
      intro n
      calc ‖(R_seq n).toCircle‖
          = ‖(g₁ - g₂) - ((g₁ - g₂) - (R_seq n).toCircle)‖ := by ring_nf
        _ ≤ ‖g₁ - g₂‖ + ‖(g₁ - g₂) - (R_seq n).toCircle‖ := norm_sub_le _ _
        _ ≤ ‖g₁ - g₂‖ + 1 / (n + 1) := by linarith [R_spec n]
    -- Therefore in the limit: ‖Λ(g₁ - g₂)‖ ≤ (f 0).re * ‖g₁ - g₂‖
    have h_seq_bound : ∀ n, ‖ΛTrigℤ f (R_seq n)‖ ≤ (f 0).re * (‖g₁ - g₂‖ + 1 / (n + 1)) := by
      intro n
      calc ‖ΛTrigℤ f (R_seq n)‖
          ≤ (f 0).re * ‖(R_seq n).toCircle‖ := h_bound_seq n
        _ ≤ (f 0).re * (‖g₁ - g₂‖ + 1 / (n + 1)) := by
            apply mul_le_mul_of_nonneg_left (h_trig_norm_bound n)
            exact (f_zero_real_nonneg f hf_pos).2
    -- Take the limit as n → ∞
    have h_lim : Filter.Tendsto (fun n : ℕ => (f 0).re * (‖g₁ - g₂‖ + 1 / (n + 1 : ℝ)))
        Filter.atTop (nhds ((f 0).re * ‖g₁ - g₂‖)) := by
      suffices Filter.Tendsto (fun n : ℕ => ‖g₁ - g₂‖ + 1 / (n + 1 : ℝ)) Filter.atTop (nhds ‖g₁ - g₂‖) by
        apply Filter.Tendsto.const_mul (f 0).re this
      have h_inv_zero : Filter.Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) Filter.atTop (nhds 0) := by
        simp only [div_eq_mul_inv, one_mul]
        refine Filter.Tendsto.inv_tendsto_atTop ?_
        have : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)) Filter.atTop Filter.atTop := by
          apply Filter.tendsto_atTop_add_const_right
          exact tendsto_natCast_atTop_atTop
        exact this
      convert h_inv_zero.const_add ‖g₁ - g₂‖ using 2
      simp [add_comm]
    have h_norm_tends : Filter.Tendsto (fun n => ‖ΛTrigℤ f (R_seq n)‖)
        Filter.atTop (nhds ‖Λ_on_circle f hf_pos (g₁ - g₂)‖) := by
      apply Filter.Tendsto.norm h_R_tends
    exact le_of_tendsto_of_tendsto h_norm_tends h_lim (Filter.Eventually.of_forall h_seq_bound)
  calc dist (Λ_on_circle f hf_pos h) (Λ_on_circle f hf_pos g)
      = ‖Λ_on_circle f hf_pos h - Λ_on_circle f hf_pos g‖ := dist_eq_norm _ _
    _ ≤ (f 0).re * ‖h - g‖ := h_bound_diff h g
    _ = (f 0).re * dist h g := by rw [dist_eq_norm]
    _ < (f 0).re * (ε / (f 0).re) := by
        apply mul_lt_mul_of_pos_left h_dist hf_pos_re
    _ = ε := by field_simp

end FourierBochner
