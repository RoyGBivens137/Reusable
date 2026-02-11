/-
Copyright (c) 2025 Zachary Mullaghy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Mullaghy, Gianfranco Romaelle
-/
import FourierBochner.Character
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

/-! ## The 2×2 Gram Matrix Analysis -/

/-- The quadratic form for a 2×2 case with points {0, x} and coefficients {c₀, c₁}. -/
lemma gram_2x2_expansion (f : ℝ → ℂ) (x : ℝ) (c₀ c₁ : ℂ) :
    ∑ i : Fin 2, ∑ j : Fin 2, conj (![c₀, c₁] i) * ![c₀, c₁] j * f (![0, x] i - ![0, x] j) =
    conj c₀ * c₀ * f 0 + conj c₀ * c₁ * f (-x) + conj c₁ * c₀ * f x + conj c₁ * c₁ * f 0 := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf

/-- Simplified expansion for the 2×2 quadratic form. -/
lemma gram_2x2_simplified (f : ℝ → ℂ) (x : ℝ) (c₀ c₁ : ℂ) :
    conj c₀ * c₀ * f 0 + conj c₀ * c₁ * f (-x) + conj c₁ * c₀ * f x + conj c₁ * c₁ * f 0 =
    (normSq c₀ + normSq c₁) * f 0 + conj c₀ * c₁ * f (-x) + conj c₁ * c₀ * f x := by
  simp only [normSq_eq_conj_mul_self]
  ring

theorem IsPositiveDefinite.conj_symm {f : ℝ → ℂ} (hf : IsPositiveDefinite f) (x : ℝ) :
    conj (f x) = f (-x) := by
  rw [← hf.1 x]

/-- Boundedness: |f(x)| ≤ f(0). -/
theorem IsPositiveDefinite.norm_le_zero {f : ℝ → ℂ} (hf : IsPositiveDefinite f) (x : ℝ) :
    ‖f x‖ ≤ (f 0).re := by
  -- f(0) is real
  have h_f0_eq : f 0 = (f 0).re := by
    have h_symm := hf.conj_symm 0
    rw [neg_zero] at h_symm
    have h_im := Complex.conj_eq_iff_im.mp h_symm
    exact Complex.ext rfl h_im
  -- Use discriminant argument: consider quadratic form with c = [λ, -1]
  -- The 2×2 Gram matrix [[f(0), f(x)], [conj(f(x)), f(0)]] is PSD
  -- So det ≥ 0: f(0)² - |f(x)|² ≥ 0

  -- For any λ ∈ ℂ, the quadratic form is ≥ 0:
  -- |λ|² f(0) + λ conj(f(x)) + conj(λ) f(x) + f(0) ≥ 0
  -- Choose λ = -f(x)/f(0) (when f(0) ≠ 0) to get the bound
  have h_f0_nonneg := hf.zero_nonneg
  by_cases h_z : (f 0).re = 0
  · -- Case f(0) = 0: then f(x) = 0
    have h_f0_zero : f 0 = 0 := by rw [h_f0_eq, h_z]; simp
    have h_q := hf.2 2 ![0, x] ![1, -f x]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
               sub_self, zero_sub, sub_zero, map_one, map_neg, one_mul, mul_one,
               neg_mul, mul_neg, neg_neg] at h_q
    rw [h_f0_zero, hf.1 x] at h_q
    simp only [mul_zero, zero_add, add_zero] at h_q
    -- h_q: 0 ≤ (conj(f x) * f x + conj(f x) * f x).re = 2 * normSq(f x)
    have : normSq (f x) ≤ 0 := by
      -- Direct computation: star z * z has real part = normSq z
      have ns_eq : ((starRingEnd ℂ) (f x) * f x).re = normSq (f x) := by
        rw [Complex.normSq_apply]
        rw [starRingEnd_apply]
        rw [Complex.star_def]
        rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring
      -- h_q says 0 ≤ -(star(fx) * fx) - (star(fx) * fx)
      -- which is 0 ≤ -2 * (star(fx) * fx)
      -- Taking real parts: 0 ≤ -2 * normSq(fx)
      have : 0 ≤ - (2 : ℝ) * normSq (f x) := by
        calc (0 : ℝ)
            ≤ (-(f x * (starRingEnd ℂ) (f x)) + -((starRingEnd ℂ) (f x) * f x)).re := h_q
          _ = (- (f x * (starRingEnd ℂ) (f x) + (starRingEnd ℂ) (f x) * f x)).re := by
                simp only [neg_add_rev]; ring_nf
          _ = - ((f x * (starRingEnd ℂ) (f x) + (starRingEnd ℂ) (f x) * f x).re) := Complex.neg_re _
          _ = - ((f x * (starRingEnd ℂ) (f x)).re + ((starRingEnd ℂ) (f x) * f x).re) := by
                simp only [Complex.add_re]
          _ = - (normSq (f x) + normSq (f x)) := by
                have comm : (f x * (starRingEnd ℂ) (f x)).re = normSq (f x) := by
                  rw [mul_comm, ns_eq]
                rw [comm, ns_eq]
          _ = - (2 * normSq (f x)) := by ring
          _ = -2 * normSq (f x) := by ring
      linarith
    have h_fx_zero := Complex.normSq_eq_zero.mp (le_antisymm this (Complex.normSq_nonneg _))
    simp [h_fx_zero, h_z]
  · -- Case f(0) > 0: discriminant via the "optimal" coefficient choice
    have h_pos : 0 < (f 0).re := lt_of_le_of_ne h_f0_nonneg (Ne.symm h_z)
    set a : ℝ := (f 0).re
    have ha0 : (a : ℂ) ≠ 0 := by
      -- since a ≠ 0 in ℝ, its coercion to ℂ is ≠ 0
      exact_mod_cast (show a ≠ 0 from h_z)
    -- quadratic form at points [0,x] and coefficients [1, -(f x)/(a:ℂ)]
    have h_q := hf.2 2 ![0, x] ![1, -(f x) / (a : ℂ)]
    -- Expand the 2×2 sum
    -- After simp, you want something like:
    -- 0 ≤ (a - normSq (f x)/a).re = a - normSq (f x)/a
    -- (because it's real)
    have h_simp :
      (∑ i : Fin 2, ∑ j : Fin 2,
        conj (![1, -(f x) / (a : ℂ)] i) *
          (![1, -(f x) / (a : ℂ)] j) *
          f (![0, x] i - ![0, x] j)).re
        =
      a - (normSq (f x)) / a := by
      -- Expand the 2×2 sum manually:
      -- (i=0,j=0): conj(1) * 1 * f(0) = f(0)
      -- (i=0,j=1): conj(1) * (-(f x)/a) * f(-x) = -(f x)/a * conj(f x)
      -- (i=1,j=0): conj(-(f x)/a) * 1 * f(x) = -conj(f x)/a * f(x)
      -- (i=1,j=1): conj(-(f x)/a) * (-(f x)/a) * f(0) = normSq(f x) / a^2 * a
      have hf0 : f 0 = (a : ℂ) := by simpa [a] using h_f0_eq
      have hfx : f (-x) = conj (f x) := by simpa using (hf.1 x)
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
                 sub_self, zero_sub, sub_zero]
      rw [hf0, hfx]
      -- Compute term by term
      -- After expansion we get: a + (-(f x) / a) * conj(f x) + (conj(-(f x) / a)) * f(x) + ...
      -- Use the fact that for real a: conj(a) = a and (starRingEnd ℂ) a = a
      have star_a : (starRingEnd ℂ) (a : ℂ) = (a : ℂ) := by
        rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal]
      simp only [map_one, map_neg, map_div₀, one_mul, mul_one, star_a]
      have ns_eq : (starRingEnd ℂ) (f x) * f x = (normSq (f x) : ℂ) :=
        (@Complex.normSq_eq_conj_mul_self (f x)).symm
      -- Compute: a - (f x)/a * conj(f x) - conj(f x)/a * f(x) + conj(f x) * (f x) / a
      --        = a - 2 * normSq(f x) / a + normSq(f x) / a
      --        = a - normSq(f x) / a
      calc (↑a + -f x / ↑a * (starRingEnd ℂ) (f x) +
                  (-(starRingEnd ℂ) (f x) / ↑a * f x +
                   -(starRingEnd ℂ) (f x) / ↑a * (-f x / ↑a) * ↑a)).re
          = (↑a + -f x / ↑a * (starRingEnd ℂ) (f x) - (starRingEnd ℂ) (f x) / ↑a * f x +
                   (starRingEnd ℂ) (f x) * f x / ↑a).re := by
            congr 1
            field_simp
            ring
        _ = (↑a - (f x * (starRingEnd ℂ) (f x)) / ↑a - (starRingEnd ℂ) (f x) * f x / ↑a +
                   (starRingEnd ℂ) (f x) * f x / ↑a).re := by
            congr 1
            ring
        _ = (↑a - (f x * (starRingEnd ℂ) (f x)) / ↑a).re := by
            congr 1
            ring
        _ = (↑a - (starRingEnd ℂ) (f x) * f x / ↑a).re := by
            congr 1
            rw [mul_comm (f x)]
        _ = ((a : ℂ) - (normSq (f x) : ℂ) / (a : ℂ)).re := by
            congr 1
            rw [ns_eq]
        _ = ((a : ℂ) - ((normSq (f x) / a) : ℝ)).re := by
            congr 1
            push_cast
            rfl
        _ = a - normSq (f x) / a := by
            rw [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]
    have : 0 ≤ a - normSq (f x) / a := by
      -- rewrite h_q using h_simp
      have := h_q
      rw [h_simp] at this
      exact this
    -- finish: rearrange to normSq ≤ a^2, then take sqrt
    have h_normSq : normSq (f x) ≤ a^2 := by
      -- from 0 ≤ a - normSq/a  ⇒  normSq ≤ a^2
      have ha : 0 ≤ a := le_of_lt h_pos
      -- multiply both sides by a > 0
      have := (sub_nonneg.mp this)
      -- this gives normSq/a ≤ a
      have h1 : normSq (f x) / a ≤ a := this
      -- multiply by a (positive)
      have h2 : normSq (f x) ≤ a * a := by
        have := (mul_le_mul_of_nonneg_left h1 ha)
      -- (a)*(normSq/a) = normSq
        have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast h_z
        calc normSq (f x)
            = a * (normSq (f x) / a) := by field_simp
          _ ≤ a * a := this
      simpa [pow_two] using h2
    -- convert normSq bound to norm bound
    -- Mathlib has: `Complex.normSq_eq_norm_sq`
    have hxnorm : ‖f x‖^2 ≤ a^2 := by
      simpa [Complex.normSq_eq_norm_sq] using h_normSq
    -- now take sqrt: ‖f x‖ ≤ a since both sides ≥ 0
    have : ‖f x‖ ≤ a := by
      have ha : 0 ≤ a := le_of_lt h_pos
      have h1 : ‖f x‖ = Real.sqrt (‖f x‖^2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      have h2 : a = Real.sqrt (a^2) := by
        rw [Real.sqrt_sq ha]
      rw [h1, h2]
      exact Real.sqrt_le_sqrt hxnorm
    simpa [a] using this

/-! ## Key Algebraic Identities -/

/-- The norm squared of a complex number equals conj(z) * z. -/
lemma normSq_eq_conj_mul (z : ℂ) : (normSq z : ℂ) = conj z * z := by
  rw [normSq_eq_conj_mul_self]

/-- Key identity: The squared norm of a sum equals the double sum of products.
    |Σₖ aₖ|² = Σᵢⱼ conj(aᵢ) · aⱼ

    Proof: |Σₖ aₖ|² = conj(Σₖ aₖ) * (Σₖ aₖ) = (Σᵢ conj(aᵢ))(Σⱼ aⱼ) = Σᵢⱼ conj(aᵢ) · aⱼ -/
lemma normSq_sum_eq_double_sum {n : ℕ} (a : Fin n → ℂ) :
    (normSq (∑ k, a k) : ℂ) = ∑ i, ∑ j, conj (a i) * a j := by
  rw [normSq_eq_conj_mul_self]
  rw [map_sum]
  rw [sum_mul]
  congr 1
  ext i
  rw [mul_sum]

/-- The real part version of the norm-sum identity. -/
lemma normSq_sum_eq_double_sum_re {n : ℕ} (a : Fin n → ℂ) :
    normSq (∑ k, a k) = (∑ i, ∑ j, conj (a i) * a j).re := by
  have h := normSq_sum_eq_double_sum a
  -- The LHS is real, so we can extract the real part
  have h_real : (normSq (∑ k, a k) : ℂ).re = normSq (∑ k, a k) := by
    simp only [ofReal_re]
  rw [← h_real, h]

/-! ## Trigonometric Polynomial Identity -/

/-- The core Bochner identity: the double sum of exponentials equals |trigPoly|².
    Σᵢⱼ conj(cᵢ) · cⱼ · exp(2πi(xᵢ-xⱼ)ξ) = |Σₖ cₖ exp(-2πixₖξ)|² -/
lemma bochner_trig_identity {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) (ξ : ℝ) :
    ∑ i, ∑ j, conj (c i) * c j * exp (2 * π * I * (x i - x j) * ξ) =
    normSq (∑ k, c k * exp (-2 * π * I * x k * ξ)) := by
  -- The proof expands both sides and shows equality
  -- First rewrite exp of difference as product of exps
  have h_exp_split : ∀ i j, exp (2 * π * I * (x i - x j) * ξ) =
      exp (2 * π * I * x i * ξ) * exp (-2 * π * I * x j * ξ) := by
    intros i j
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [h_exp_split]
  -- Now LHS = Σᵢⱼ conj(cᵢ) · cⱼ · exp(2πixᵢξ) · exp(-2πixⱼξ)
  -- RHS = conj(Σₖ cₖ exp(-2πixₖξ)) · (Σₖ cₖ exp(-2πixₖξ))
  rw [normSq_eq_conj_mul_self]
  rw [map_sum]
  -- conj(cₖ * exp(-2πixₖξ)) = conj(cₖ) * exp(2πixₖξ)
  have h_conj_term : ∀ k, conj (c k * exp (-2 * π * I * x k * ξ)) =
      conj (c k) * exp (2 * π * I * x k * ξ) := by
    intro k
    rw [map_mul]
    congr 1
    -- conj (exp (-2 * π * I * x k * ξ)) = exp (2 * π * I * x k * ξ)
    rw [← Complex.exp_conj]
    -- Now show conj (-2 * π * I * x k * ξ) = 2 * π * I * x k * ξ
    simp only [conj_ofReal, conj_I, map_mul, map_neg]
    -- Now show cexp ((starRingEnd ℂ) 2 * π * I * x k * ξ) = cexp (π * I * x k * ξ * 2)
    congr 1
    simp [starRingEnd_apply]
  simp_rw [h_conj_term]
  -- Now RHS = (Σᵢ conj(cᵢ) exp(2πixᵢξ)) * (Σⱼ cⱼ exp(-2πixⱼξ))
  rw [sum_mul]
  congr 1
  ext i
  rw [mul_sum]
  congr 1
  ext j
  ring

/-! ## The Bochner Bridge -/

/-- The "Forward" Bochner Direction (Integrable Version): -/
theorem pos_def_of_fourier_nonneg_integrable {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hf_inv : ∀ t, f t = ∫ ξ, (g ξ : ℂ) * exp (2 * π * I * t * ξ))
    (hg_nonneg : ∀ ξ, 0 ≤ g ξ)
    (hg_int : Integrable g) :
    IsPositiveDefinite f := by
  constructor
  · -- Symmetry: f(-x) = conj f(x)
    intro x
    simp only [hf_inv]
    simp only [Complex.conj_ofReal, map_mul, ← Complex.exp_conj, ← integral_conj]
    congr 1
    ext1 ξ
    congr 1
    push_cast
    simp [Complex.conj_I, map_ofNat]
  · -- Quadratic form non-negativity
    intro n x c
    have h_ident : (∑ i, ∑ j, conj (c i) * c j * f (x i - x j)) =
        ∫ ξ, (g ξ : ℂ) * (∑ i, ∑ j, conj (c i) * c j * exp (2 * π * I * (x i - x j) * ξ)) := by
      classical
      -- Integrability: g integrable + ‖exp‖=1 ⟹ g*exp integrable
      have h_term_int : ∀ (i j : Fin n),
          Integrable (fun ξ : ℝ =>
            (g ξ : ℂ) * (conj (c i) * c j * exp (2 * π * I * (x i - x j) * ξ))) := by
        intro i j
      -- Rearrange: (g * (c*c*exp)) = (c*c) * (g * exp)
        have : (fun ξ : ℝ => (g ξ : ℂ)
         * (conj (c i) * c j * exp (2 * π * I * (x i - x j) * ξ))) =
               (fun ξ : ℝ => conj (c i)
                * c j * ((g ξ : ℂ) * exp (2 * π * I * (x i - x j) * ξ))) := by
          ext ξ; ring
        rw [this]
        refine Integrable.const_mul ?_ _
      -- Key: Integrable.bdd_mul from Mathlib
      -- If f measurable+bounded and g integrable, then f*g integrable
        have hg_c : Integrable (fun ξ : ℝ => (g ξ : ℂ)) := hg_int.ofReal
        have exp_meas : AEStronglyMeasurable
            (fun ξ : ℝ => exp (2 * π * I * (x i - x j) * ξ)) :=
          (Complex.continuous_exp.comp
           (continuous_const.mul continuous_ofReal)).aestronglyMeasurable
        have exp_bdd : ∀ᵐ (ξ : ℝ) ∂(volume : Measure ℝ), ‖exp (2 * π * I * (x i - x j) * ξ)‖ ≤ 1 :=
          ae_of_all _ (fun ξ => by
            rw [Complex.norm_exp]
            have : (2 * π * I * (x i - x j) * ↑ξ).re = 0 := by
              simp [mul_re, I_re, I_im, ofReal_re, ofReal_im]
            rw [this, Real.exp_zero])
        exact hg_c.mul_bdd exp_meas exp_bdd
      -- Rearranged form of h_term_int for sum-integral swap
      have h_term_int' : ∀ (i j : Fin n),
          Integrable (fun ξ : ℝ => (starRingEnd ℂ)
           (c i) * c j * (↑(g ξ) * exp (2 * π * I * ↑(x i - x j) * ↑ξ))) := by
        intro i j
        have eq : (fun ξ : ℝ => (starRingEnd ℂ)
         (c i) * c j * (↑(g ξ) * exp (2 * π * I * ↑(x i - x j) * ↑ξ))) =
                (fun ξ : ℝ => ↑(g ξ) * ((starRingEnd ℂ)
                 (c i) * c j * exp (2 * π * I * (↑(x i) - ↑(x j)) * ↑ξ))) := by
          ext (ξ : ℝ); simp only [ofReal_sub]; ring
        rw [eq]
        exact h_term_int i j
      -- expand f using hf_inv
      simp_rw [hf_inv]
      -- Swap sum and integral: ∑ᵢⱼ cᵢcⱼ ∫ g·exp = ∫ g·(∑ᵢⱼ cᵢcⱼ·exp)
      calc ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * ∫ (ξ : ℝ),
       ↑(g ξ) * exp (2 * π * I * ↑(x i - x j) * ↑ξ)
          -- Step 1: Pull constants into integrals: c * ∫ f = ∫ c * f
          = ∑ i, ∑ j, ∫ (ξ : ℝ), (starRingEnd ℂ) (c i) * c j * (↑(g ξ)
           * exp (2 * π * I * ↑(x i - x j) * ↑ξ)) := by
            congr 1; ext i; congr 1; ext j
            exact (integral_const_mul _ _).symm
      -- Step 2: Apply integral_finset_sum for j-sum
        _ = ∑ i, ∫ (ξ : ℝ), ∑ j, (starRingEnd ℂ) (c i) * c j * (↑(g ξ)
         * exp (2 * π * I * ↑(x i - x j) * ↑ξ)) := by
            congr 1; ext i
            exact (integral_finset_sum Finset.univ (fun j _ => h_term_int' i j)).symm
      -- Step 3: Apply integral_finset_sum for i-sum
        _ = ∫ (ξ : ℝ), ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (↑(g ξ)
         * exp (2 * π * I * ↑(x i - x j) * ↑ξ)) :=
            (integral_finset_sum Finset.univ (by
              intro i _
              exact integrable_finset_sum _ (fun j _ => h_term_int' i j))).symm
      -- Step 4: Factor out g ξ from the sum (use ofReal_sub to match RHS coercion structure)
        _ = ∫ (ξ : ℝ), ↑(g ξ) * ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * exp (2 * π * I * (↑(x i)
         - ↑(x j)) * ↑ξ) := by
            congr 1; ext ξ
            rw [Finset.mul_sum]; congr 1; ext i
            rw [Finset.mul_sum]; congr 1; ext j
            simp only [ofReal_sub]; ring
    rw [h_ident]
    simp_rw [bochner_trig_identity x c]
    -- Specify (ξ : ℝ) in the integral to avoid ℂ-type inference and justify integrability
    -- Bound the trig polynomial pointwise by a constant so we can apply `integral_re`.
    let S := (∑ k, ‖c k‖)
    have h_bound : ∀ ξ : ℝ, normSq (∑ k, c k * exp (-2 * π * I * x k * ξ)) ≤ S ^ 2 := by
      intro ξ
      have h1 :
          ‖(∑ k, c k * exp (-2 * π * I * x k * ξ))‖
            ≤ ∑ k, ‖c k * exp (-2 * π * I * x k * ξ)‖ := by
        simpa using (norm_sum_le (s := Finset.univ)
          (f := fun k : Fin n => c k * exp (-2 * π * I * x k * ξ)))
      -- Simplify: ‖c * exp(I*x)‖ = ‖c‖ * ‖exp(I*x)‖ = ‖c‖ * 1
      have h2 : ∀ k, ‖c k * exp (-2 * π * I * x k * ξ)‖ = ‖c k‖ := by
        intro k
        rw [norm_mul, Complex.norm_exp]
        have : (-2 * π * I * x k * ξ).re = 0 := by simp [mul_re, I_re, I_im, ofReal_re, ofReal_im]
        rw [this, Real.exp_zero, mul_one]
      simp only [h2] at h1
      -- Now h1 : ‖(∑ k, ...)‖ ≤ ∑ k, ‖c k‖ = S
      rw [normSq_eq_norm_sq]
      calc ‖(∑ k, c k * exp (-2 * π * I * x k * ξ))‖^2
          ≤ (∑ k, ‖c k‖)^2 := by gcongr
        _ = S^2 := by rfl
    -- The integrand is real and non-negative
    have integrand_nonneg : ∀ ξ, 0 ≤ (g ξ : ℝ) *
     normSq (∑ k, c k * exp (-2 * π * I * x k * ξ)) := by
      intro ξ
      exact mul_nonneg (hg_nonneg ξ) (normSq_nonneg _)
    -- After h_ident and bochner_trig_identity, goal is: 0 ≤ (∫ ...).re
    -- Show integrand equals ofReal, then use integral_ofReal
    have eq_ofReal : ∀ ξ, (g ξ : ℂ) * ↑(normSq (∑ k, c k * exp (-2 * π * I * x k * ξ))) =
        ↑(g ξ * normSq (∑ k, c k * exp (-2 * π * I * x k * ξ))) := by
      intro ξ
      simp only [ofReal_mul]
    simp_rw [eq_ofReal]
    -- Goal: 0 ≤ (∫ ξ, ↑(g ξ * normSq ...)).re
    suffices ∫ (ξ : ℝ), g ξ * normSq (∑ k, c k * exp (-2 * π * I * x k * ξ)) ≥ 0 by
      let f_real : ℝ → ℝ := fun ξ => g ξ * normSq (∑ k, c k * exp (-2 * π * I * x k * ξ))
      let f_complex : ℝ → ℂ := fun ξ => ↑(f_real ξ)
      have h_eq : (∫ ξ, f_complex ξ).re = ∫ ξ, f_real ξ := by
        have h1 : ∫ ξ, f_complex ξ = ↑(∫ ξ, f_real ξ) := integral_ofReal
        rw [h1]
        rw [ofReal_re]
      rw [h_eq]
      exact this
    exact integral_nonneg integrand_nonneg

/-- Specialized Bochner for Toeplitz:

When f has a positive Fourier transform given by a symbol function,
and both the Fourier identity and inversion hold, f is positive-definite. -/
theorem pos_def_from_positive_symbol {f : ℝ → ℂ} {symbol : ℝ → ℝ}
    (h_symbol_pos : ∀ ξ, 0 < symbol ξ)
    (h_symbol_int : Integrable symbol)
    (hf_inv : ∀ t, f t = ∫ ξ, (symbol ξ : ℂ) * exp (2 * π * I * t * ξ)) :
    IsPositiveDefinite f :=
  pos_def_of_fourier_nonneg_integrable hf_inv (fun ξ => le_of_lt (h_symbol_pos ξ)) h_symbol_int

/-! ## Converse Direction -/

/-! ## Helper Structures for Bochner Converse -/

/-- Trigonometric polynomials as finite linear combinations of characters. -/
abbrev TrigPoly := ℝ →₀ ℂ

namespace TrigPoly

/-- Evaluate a trigonometric polynomial at a point t ∈ ℝ.
    For P = Σ_ξ c_ξ δ_ξ, we have P.eval(t) = Σ_ξ c_ξ exp(2πitξ). -/
noncomputable def eval (P : TrigPoly) (t : ℝ) : ℂ :=
  P.sum (fun ξ c => c * Complex.exp (2 * Real.pi * I * (t : ℂ) * (ξ : ℂ)))

/-- Trigonometric polynomials are continuous in t. -/
lemma continuous_eval (P : TrigPoly) : Continuous P.eval := by
  unfold eval Finsupp.sum
  refine continuous_finset_sum _ (fun ξ _ => ?_)
  continuity

/-- Evaluation is linear in P. -/
@[simp] lemma eval_add (P Q : TrigPoly) (t : ℝ) : (P + Q).eval t = P.eval t + Q.eval t := by
  unfold eval
  rw [Finsupp.sum_add_index']
  · intro; simp
  · intro a b₁ b₂; ring

/-- Evaluation respects scalar multiplication. -/
@[simp] lemma eval_smul (c : ℂ) (P : TrigPoly) (t : ℝ) : (c • P).eval t = c * P.eval t := by
  unfold eval Finsupp.sum
  by_cases hc : c = 0
  · simp [hc]
  · simp only [Finsupp.smul_apply, smul_eq_mul]
    rw [Finsupp.support_smul_eq hc]
    conv_lhs => arg 2; ext; rw [mul_assoc]
    rw [← Finset.mul_sum]

/-- Evaluation at t is a linear map from TrigPoly to ℂ. -/
noncomputable def evalLinear (t : ℝ) : TrigPoly →ₗ[ℂ] ℂ where
  toFun := fun P => P.eval t
  map_add' := fun P Q => eval_add P Q t
  map_smul' := fun c P => eval_smul c P t

end TrigPoly

namespace TrigPoly

/-- The embedding of a trigonometric polynomial into the space of continuous maps ℝ → ℂ. -/
noncomputable def toContinuousMap (P : TrigPoly) : ContinuousMap ℝ ℂ :=
  ⟨P.eval, P.continuous_eval⟩

/-- The embedding as a `LinearMap` over `ℂ`. -/
noncomputable def toContinuousMapLinear : TrigPoly →ₗ[ℂ] ContinuousMap ℝ ℂ where
  toFun := toContinuousMap
  map_add' := fun P Q => by
    ext t
    exact eval_add P Q t
  map_smul' := fun c P => by
    ext t
    exact eval_smul c P t

end TrigPoly

/-- The positive functional induced by a positive-definite function on trigonometric polynomials.
    For P = Σ_ξ c_ξ δ_ξ, we define Λ(P) = Σ_{ξ₁,ξ₂} conj(c_{ξ₁})·c_{ξ₂}·f(ξ₁ - ξ₂). -/
noncomputable def posFunctional (f : ℝ → ℂ) (P : TrigPoly) : ℂ :=
  P.sum (fun ξ₁ c₁ => P.sum (fun ξ₂ c₂ => conj c₁ * c₂ * f (ξ₁ - ξ₂)))

/-- Sesquilinear form associated to a function `f` on trigonometric polynomials. -/
noncomputable def sesquilinearForm (f : ℝ → ℂ) (P Q : TrigPoly) : ℂ :=
  ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ Q.support, conj (P ξ₁) * Q ξ₂ * f (ξ₁ - ξ₂)

/-- The diagonal of the sesquilinear form recovers `posFunctional`. -/
lemma sesquilinearForm_diag {f : ℝ → ℂ} (P : TrigPoly) :
    sesquilinearForm f P P = posFunctional f P := by
  dsimp [sesquilinearForm, posFunctional]
  rfl

/-- Hermitian symmetry (conjugate symmetry) of the sesquilinear form when `f` is -/
lemma sesquilinearForm_hermitian {f : ℝ → ℂ} (hf : IsPositiveDefinite f) (P Q : TrigPoly) :
    conj (sesquilinearForm f P Q) = sesquilinearForm f Q P := by
  unfold sesquilinearForm
  -- Move conjugation inside the sums and across products
  rw [map_sum]
  simp_rw [map_sum, map_mul, conj_conj]
  -- Replace `conj (f (ξ₁ - ξ₂))` with `f (ξ₂ - ξ₁)` using Hermitian symmetry
  simp_rw [← hf.1, neg_sub]
  -- Swap summation order and rearrange factors to match `sesquilinearForm f Q P`.
  -- Finish the remaining associativity/commutativity of the integrand using `ring`.
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl (fun x _ =>
    Finset.sum_congr rfl (fun x_1 _ => by ring))

/-- The positive functional is non-negative for positive-definite f. -/
lemma posFunctional_nonneg {f : ℝ → ℂ} (hf : IsPositiveDefinite f) (P : TrigPoly) :
    0 ≤ (posFunctional f P).re := by
  -- This follows directly from the positive-definite property!
  unfold posFunctional Finsupp.sum
  -- Convert the Finsupp sum to an indexed sum over Fin n
  classical
  let n := P.support.card
  let h_equiv := P.support.equivFin
  let x : Fin n → ℝ := fun i => h_equiv.symm i
  let c : Fin n → ℂ := fun i => P (x i)
  -- The sum over P.support equals the sum over Fin n via the equivalence
  have : ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ P.support, conj (P ξ₁) * P ξ₂ * f (ξ₁ - ξ₂) =
         ∑ i : Fin n, ∑ j : Fin n, conj (c i) * c j * f (x i - x j) := by
    -- Convert to sum over the subtype P.support, then reindex via the equivalence
    trans (∑ ξ₁ : P.support, ∑ ξ₂ : P.support, conj (P ξ₁.val) * P ξ₂.val * f (ξ₁.val - ξ₂.val))
    · -- The sums are equal: ∑ ∈ P.support = ∑ : P.support with coercions
      conv_lhs => rw [← Finset.sum_coe_sort P.support]
      conv_lhs => arg 2; ext; rw [← Finset.sum_coe_sort P.support]
    · -- Now reindex using h_equiv for both outer and inner sums
      erw [Fintype.sum_equiv h_equiv]
      intro a
      simp only [x, c, Equiv.symm_apply_apply]
      erw [Fintype.sum_equiv h_equiv]
      simp only [Equiv.symm_apply_apply]
      intro; trivial  -- Discharge the side condition
  rw [this]
  exact hf.2 n x c

/-- The norm of the positive functional is controlled by f(0). -/
lemma posFunctional_bound {f : ℝ → ℂ} (hf : IsPositiveDefinite f) (P : TrigPoly) :
    ‖posFunctional f P‖ ≤ (f 0).re * (P.support.sum (fun ξ => ‖P ξ‖)) ^ 2 := by
  -- Bound each matrix entry by f(0) (from positive-definiteness), then estimate the
  -- double sum by the ℓ¹-norm of the coefficients.
  -- This bound is correct but loose - ℓ² would be tighter.
  unfold posFunctional Finsupp.sum
  -- Norm of a sum ≤ sum of norms (apply triangle inequality twice)
  have h1 : ‖∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ P.support, conj (P ξ₁) * P ξ₂ * f (ξ₁ - ξ₂)‖ ≤
    ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ P.support, ‖conj (P ξ₁) * P ξ₂ * f (ξ₁ - ξ₂)‖ := by
    calc ‖∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ P.support, conj (P ξ₁) * P ξ₂ * f (ξ₁ - ξ₂)‖
        ≤ ∑ ξ₁ ∈ P.support, ‖∑ ξ₂ ∈ P.support, conj (P ξ₁) * P ξ₂ * f (ξ₁ - ξ₂)‖ := norm_sum_le _ _
      _ ≤ ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ P.support, ‖conj (P ξ₁) * P ξ₂ * f (ξ₁ - ξ₂)‖ := by
        apply Finset.sum_le_sum; intro _ _; apply norm_sum_le
  calc
    ‖∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ P.support, conj (P ξ₁) * P ξ₂ * f (ξ₁ - ξ₂)‖
        ≤ ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ P.support, ‖conj (P ξ₁) * P ξ₂ * f (ξ₁ - ξ₂)‖ := h1
    _ = ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ P.support, ‖P ξ₁‖ * ‖P ξ₂‖ * ‖f (ξ₁ - ξ₂)‖ := by
      simp_rw [norm_mul, Complex.norm_conj]
    _ ≤ ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ P.support, ‖P ξ₁‖ * ‖P ξ₂‖ * (f 0).re := by
      gcongr
      exact hf.norm_le_zero _
    _ = ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ P.support, (f 0).re * ‖P ξ₁‖ * ‖P ξ₂‖ := by
      congr 1
      ext ξ₁
      congr 1
      ext ξ₂
      ring
    _ = ∑ ξ₁ ∈ P.support, (f 0).re * ‖P ξ₁‖ * ∑ ξ₂ ∈ P.support, ‖P ξ₂‖ := by
      refine Finset.sum_congr rfl (fun ξ₁ _ => by
      -- pull the inner constant out of the inner sum
        have : ∑ ξ₂ ∈ P.support, (f 0).re *
         ‖P ξ₁‖ * ‖P ξ₂‖ = (f 0).re * ‖P ξ₁‖ * ∑ ξ₂ ∈ P.support, ‖P ξ₂‖ := by
          rw [Finset.mul_sum]
        rw [this])
    _ = (f 0).re * (∑ ξ ∈ P.support, ‖P ξ‖) * (∑ ξ₂ ∈ P.support, ‖P ξ₂‖) := by
      let S := ∑ ξ₂ ∈ P.support, ‖P ξ₂‖
      -- Pull out the constant factors and use the definition of `S` to finish.
      have h_eq1 : (fun ξ => (f 0).re * ‖P ξ‖ * S) = fun ξ => (f 0).re * S * ‖P ξ‖ := by
        ext; ring
      calc
        ∑ ξ₁ ∈ P.support, (f 0).re * ‖P ξ₁‖ * S
            = ∑ ξ₁ ∈ P.support, (f 0).re * S * ‖P ξ₁‖ := by simp [h_eq1]
        _ = let aS := (f 0).re * S; ∑ ξ₁ ∈ P.support, aS * ‖P ξ₁‖ := by simp
        _ = let aS := (f 0).re * S; aS * (∑ ξ₁ ∈ P.support, ‖P ξ₁‖) := by
          -- use `Finset.mul_sum` which matches `a * ∑ f = ∑ a * f`
          simp [Finset.mul_sum]
        _ = (f 0).re * S * S := by simp [S]
    _ = (f 0).re * (∑ ξ ∈ P.support, ‖P ξ‖) ^ 2 := by
      rw [sq]
      ring

  /-- Bound for the mixed sesquilinear form in terms of ℓ¹ norms of coefficients. -/
  lemma sesquilinearForm_bound {f : ℝ → ℂ} (hf : IsPositiveDefinite f) (P Q : TrigPoly) :
      ‖sesquilinearForm f P Q‖ ≤ (f 0).re * (P.support.sum (fun ξ => ‖P ξ‖)) *
       (Q.support.sum (fun ξ => ‖Q ξ‖)) := by
    unfold sesquilinearForm
    -- Triangle inequality applied twice over the double sum
    have h1 : ‖∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ Q.support, conj (P ξ₁) * Q ξ₂ * f (ξ₁ - ξ₂)‖ ≤
      ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ Q.support, ‖conj (P ξ₁) * Q ξ₂ * f (ξ₁ - ξ₂)‖ := by
      calc ‖∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ Q.support, conj (P ξ₁) * Q ξ₂ * f (ξ₁ - ξ₂)‖
          ≤ ∑ ξ₁ ∈ P.support, ‖∑ ξ₂ ∈ Q.support, conj (P ξ₁) *
           Q ξ₂ * f (ξ₁ - ξ₂)‖ := norm_sum_le _ _
        _ ≤ ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ Q.support, ‖conj (P ξ₁) * Q ξ₂ * f (ξ₁ - ξ₂)‖ := by
          apply Finset.sum_le_sum; intro _ _; apply norm_sum_le
    calc
      ‖∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ Q.support, conj (P ξ₁) * Q ξ₂ * f (ξ₁ - ξ₂)‖
          ≤ ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ Q.support, ‖conj (P ξ₁) * Q ξ₂ * f (ξ₁ - ξ₂)‖ := h1
      _ = ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ Q.support, ‖P ξ₁‖ * ‖Q ξ₂‖ * ‖f (ξ₁ - ξ₂)‖ := by
        simp_rw [norm_mul, Complex.norm_conj]
      _ ≤ ∑ ξ₁ ∈ P.support, ∑ ξ₂ ∈ Q.support, ‖P ξ₁‖ * ‖Q ξ₂‖ * (f 0).re := by
        gcongr
        exact hf.norm_le_zero _
      _ = ((f 0).re * ∑ ξ₁ ∈ P.support, ‖P ξ₁‖) * ∑ ξ₂ ∈ Q.support, ‖Q ξ₂‖ := by
        rw [Finset.mul_sum, Finset.sum_comm]
        congr 1; ext ξ₂
        simp [Finset.mul_sum, mul_comm, mul_assoc]

/-! ## Helper Lemmas for the Converse Direction -/

/-- Helper aliases: divisibility via `mod = 0` for nat and int. -/
theorem nat_dvd_iff_mod_eq_zero {m n : ℕ} : m ∣ n ↔ n % m = 0 :=
  Nat.dvd_iff_mod_eq_zero

theorem int_dvd_iff_mod_eq_zero {m n : ℤ} : m ∣ n ↔ n % m = 0 :=
  Int.dvd_iff_emod_eq_zero

/-- For real numbers, a is a multiple of 2π iff a/(2π) is an integer. -/
theorem real_multiple_of_2pi_iff_div_is_int (a : ℝ) :
    (∃ k : ℤ, a = k * (2 * π)) ↔ (∃ k : ℤ, a / (2 * π) = k) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    use k
    have h_denom : (2 * π : ℝ) ≠ 0 := by
      linarith [Real.pi_gt_three]
    calc
      a / (2 * π) = (k * (2 * π)) / (2 * π) := by rw [hk]
      _ = k := by field_simp [h_denom]
  · intro h
    obtain ⟨k, hk⟩ := h
    use k
    have h_denom : (2 * π : ℝ) ≠ 0 := by
      linarith [Real.pi_gt_three]
    calc
      a = (a / (2 * π)) * (2 * π) := by field_simp [h_denom]
      _ = ↑k * (2 * π) := by rw [hk];


/-- Trigonometric polynomials separate points on any interval. -/
lemma trigPoly_separates_points (a b : ℝ) (hab : a ≠ b) :
    ∃ (P : TrigPoly), P.eval a ≠ P.eval b := by
  classical
  -- choose a frequency so (a-b)*ξ = -1/2
  let ξ : ℝ := 1 / (2 * (b - a))
  -- use the one-term trig polynomial: single frequency ξ with coefficient 1
  use Finsupp.single ξ 1
  unfold TrigPoly.eval
  change (Finsupp.single ξ 1).sum
   (fun ξ c => c * Complex.exp (2 * Real.pi * I * (a : ℂ) * (ξ : ℂ))) ≠
       (Finsupp.single ξ 1).sum (fun ξ c => c * Complex.exp (2 * Real.pi * I * (b : ℂ) * (ξ : ℂ)))
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  simp only [one_mul]
  intro hEq
  -- equality of exponentials gives an integer phase relation
  have ⟨k, hk⟩ := (exp_eq_exp_iff_exists_int).1 hEq
  -- cancel the nonzero factor 2πi
  have hnonzero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2pi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hpi
    simpa [mul_assoc] using mul_ne_zero h2pi Complex.I_ne_zero
  have hk' : (a : ℂ) * (ξ : ℂ) = (b : ℂ) * (ξ : ℂ) + (k : ℂ) := by
    -- apply division by (2πi) and simplify; `field_simp` uses `hnonzero`
    have hk_div := congrArg (fun z => z / (2 * (Real.pi : ℂ) * Complex.I)) hk
    field_simp [hnonzero] at hk_div
    simpa [mul_comm] using hk_div
  -- convert to a cleaner complex equality for (a-b)*ξ
  have hk_complex : ((a - b : ℝ) : ℂ) * (ξ : ℂ) = (k : ℂ) := by
    calc
      ((a - b : ℝ) : ℂ) * (ξ : ℂ)
          = (a : ℂ) * (ξ : ℂ) - (b : ℂ) * (ξ : ℂ) := by simp [sub_mul]
      _ = ((b : ℂ) * (ξ : ℂ) + (k : ℂ)) - (b : ℂ) * (ξ : ℂ) := by rw [hk']
      _ = (k : ℂ) := by simp
  -- take real parts to get (a-b)*ξ = k
  have hk_real : (a - b) * ξ = (k : ℝ) := by
    have hRe := congrArg Complex.re hk_complex
    simp [Complex.ofReal_re] at hRe
    exact hRe
  -- compute (a-b)*ξ = -1/2 explicitly; prove b-a ≠ 0 first
  have hb : b - a ≠ 0 := by
    intro h
    have : a = b := by linarith [h]
    exact hab this
  have hval : (a - b) * ξ = (-1 : ℝ) / 2 := by
    dsimp [ξ]
    field_simp [hb]
    ring
  -- so (k : ℝ) = -1/2, impossible for integer k: reduce to a mod-2 contradiction
  have hkcast : (k : ℝ) = (-1 : ℝ) / 2 := by linarith [hk_real, hval]
  have hk2_real : (2 : ℝ) * (k : ℝ) = (-1 : ℝ) := by linarith [hkcast]
  have hkZ : (2 * k : ℤ) = (-1 : ℤ) := by
    exact_mod_cast hk2_real
  have hmod : (2 * k) % 2 = 0 := by simp
  have hneg1mod : (-1 : ℤ) % 2 = 1 := by norm_num
  have hneg1mod_zero : (-1 : ℤ) % 2 = 0 := by simpa [hkZ] using hmod
  have : (1 : ℤ) = 0 := by simpa [hneg1mod] using hneg1mod_zero
  have : (1 : ℤ) ≠ 0 := by norm_num
  contradiction

/-- The constant function 1 is a trigonometric polynomial (zero frequency). -/
lemma trigPoly_one : ∃ P : TrigPoly, ∀ t : ℝ, P.eval t = 1 := by
  use Finsupp.single 0 1
  intro t
  unfold TrigPoly.eval
  rw [Finsupp.sum_single_index (by simp)]
  simp [Complex.exp_zero]

-- Note: eval_add and eval_smul are already proven in the TrigPoly namespace above

/-- Trigonometric polynomials are closed under conjugation.
    Key insight: conj(exp(2πitξ)) = exp(2πit(-ξ)) -/
lemma trigPoly_conj (P : TrigPoly) : ∃ Q : TrigPoly, ∀ t : ℝ, Q.eval t = conj (P.eval t) := by
  induction P using Finsupp.induction with
  | zero =>
    use 0
    intro t
    simp [TrigPoly.eval]
  | single_add a b P ha hb ih =>
    rcases ih with ⟨Qp, hQp⟩
    use Qp + Finsupp.single (-a) (conj b)
    intro t
    -- Chain of equalities showing Q.eval t = conj((single a b + P).eval t)
    calc (Qp + Finsupp.single (-a) (conj b)).eval t
        = Qp.eval t + TrigPoly.eval (Finsupp.single (-a) (conj b)) t := by rw [TrigPoly.eval_add]
      _ = conj (TrigPoly.eval P t) + TrigPoly.eval (Finsupp.single (-a) (conj b)) t := by rw [hQp]
      _ = conj (TrigPoly.eval P t) + conj (TrigPoly.eval (Finsupp.single a b) t) := by
          congr 1
          -- Show that eval(single(-a, conj(b))) = conj(eval(single(a, b)))
          simp only [TrigPoly.eval]
          rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
          · rw [map_mul, ← Complex.exp_conj]
            simp only [conj_I, conj_ofReal, map_ofNat, map_mul]
            congr 1
            simp only [Complex.ofReal_neg, mul_neg, neg_mul]
          · simp
          · simp
      _ = conj (TrigPoly.eval P t + TrigPoly.eval (Finsupp.single a b) t) := by rw [← map_add]
      _ = conj (TrigPoly.eval (P + Finsupp.single a b) t) := by rw [← TrigPoly.eval_add]
      _ = conj (TrigPoly.eval (Finsupp.single a b + P) t) := by rw [add_comm]

/-- The set of TrigPoly evaluations as continuous functions ℝ → ℂ. -/
def trigPolySet : Set C(ℝ, ℂ) :=
  {f | ∃ P : TrigPoly, f = ⟨P.eval, TrigPoly.continuous_eval P⟩}

/-- Helper: restrict a TrigPoly to a compact set K as a continuous map. -/
noncomputable def trigPolyOnK (K : Set ℝ) (P : TrigPoly) : C(K, ℂ) :=
  ⟨fun x : K => P.eval x.val,
   (TrigPoly.continuous_eval P).comp continuous_subtype_val⟩

/-- The pointwise product of two TrigPoly evaluations.
    The product (Σᵢ pᵢ e^{iaᵢt})(Σⱼ qⱼ e^{ibⱼt}) = Σᵢⱼ pᵢqⱼ e^{i(aᵢ+bⱼ)t}
    is another finite sum, hence a TrigPoly. -/
lemma trigPoly_mul_is_trigPoly (P Q : TrigPoly) :
    ∃ R : TrigPoly, ∀ t, P.eval t * Q.eval t = R.eval t := by
  -- Construct R as the Finsupp with coefficients at frequencies a + b
  -- R(a+b) = Σ_{i,j: aᵢ+bⱼ=a+b} P(aᵢ) * Q(bⱼ)
  let R : TrigPoly := Finsupp.sum P fun a p =>
    Finsupp.sum Q fun b q => Finsupp.single (a + b) (p * q)
  use R
  intro t
  unfold TrigPoly.eval
  simp only [Finsupp.sum]
  -- LHS: expand product of sums
  rw [Finset.sum_mul_sum]
  -- Simplify each term: (P a * exp(2πita)) * (Q b * exp(2πitb)) = P a * Q b * exp(2πit(a+b))
  have h_prod : ∀ a b,
    (P a * Complex.exp (2 * Real.pi * I * (t : ℂ) * (a : ℂ))) *
    (Q b * Complex.exp (2 * Real.pi * I * (t : ℂ) * (b : ℂ))) =
    (P a * Q b) * Complex.exp (2 * Real.pi * I * (t : ℂ) * ((a + b) : ℂ)) := by
    intro a b
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  simp only [h_prod]
  clear h_prod
  -- Now RHS: unfold R and apply Finsupp.sum_sum_index
  -- R = Finsupp.sum P (fun a p => Finsupp.sum Q (fun b q => Finsupp.single (a+b) (p*q)))
  -- We need: LHS = RHS where RHS = R.sum (fun ξ c => c * exp(2πitξ))

  -- The RHS is a nested Finsupp.sum, so we use sum_sum_index to flatten it
  show ∑ a ∈ P.support, ∑ b ∈ Q.support, (P a * Q b)
   * Complex.exp (2 * Real.pi * I * (t : ℂ) * ((a + b) : ℂ)) =
       (Finsupp.sum P fun a p => Finsupp.sum Q fun b q => Finsupp.single (a + b) (p * q)).sum
         (fun ξ c => c * Complex.exp (2 * Real.pi * I * (t : ℂ) * (ξ : ℂ)))
  rw [Finsupp.sum_sum_index]
  · -- After first rewrite, we have a sum over P.support
    apply Finset.sum_congr rfl
    intro a ha
    simp only [] -- Beta reduce
    rw [Finsupp.sum_sum_index]
    · apply Finset.sum_congr rfl
      intro b hb
      simp only [] -- Beta reduce again
      rw [Finsupp.sum_single_index]
      · -- Show: P a * Q b * exp(...(a)... + ...(b)...) = P a * Q b * exp(...(a+b)...)
        congr 1
        push_cast
        ring
      · simp
    · intro c; simp
    · intro c1 c2
      simp only [add_mul]
      intro; trivial
  · intro c; simp
  · intro c1 c2
    simp only [add_mul]
    intro; trivial

/-- The StarSubalgebra of C(ℝ, ℂ) whose carrier is exactly trigPolySet.
    This is cleaner than Algebra.adjoin.starClosure for extraction purposes. -/
noncomputable def trigPolyStarSubalgebra : StarSubalgebra ℂ C(ℝ, ℂ) where
  carrier := trigPolySet
  zero_mem' := by
    refine ⟨0, ?_⟩
    ext t
    simp [TrigPoly.eval]
  one_mem' := by
    refine ⟨Finsupp.single 0 1, ?_⟩
    ext t
    simp [TrigPoly.eval, Finsupp.sum_single_index]
  add_mem' := by
    rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩
    refine ⟨P + Q, ?_⟩
    ext t
    simp [TrigPoly.eval_add]
  mul_mem' := by
    rintro f g ⟨P, rfl⟩ ⟨Q, rfl⟩
    obtain ⟨R, hR⟩ := trigPoly_mul_is_trigPoly P Q
    refine ⟨R, ?_⟩
    ext t
    simp [hR]
  algebraMap_mem' := by
    intro c
    refine ⟨Finsupp.single 0 c, ?_⟩
    ext t
    simp [TrigPoly.eval, Finsupp.sum_single_index]
  star_mem' := by
    rintro f ⟨P, rfl⟩
    obtain ⟨Q, hQ⟩ := trigPoly_conj P
    refine ⟨Q, ?_⟩
    ext t
    -- star on C(ℝ, ℂ) is pointwise conjugation
    show conj (P.eval t) = Q.eval t
    rw [hQ]

/-- The trigonometric polynomial StarSubalgebra separates points. -/
lemma trigPolyStarSubalgebra_separates_points :
    trigPolyStarSubalgebra.toSubalgebra.SeparatesPoints := by
  intro x y hxy
  obtain ⟨P, hP⟩ := trigPoly_separates_points x y hxy
  refine ⟨P.eval, ?_, hP⟩
  refine ⟨⟨P.eval, TrigPoly.continuous_eval P⟩, ⟨P, rfl⟩, rfl⟩

/-! ## L² Inner Product and Fourier Coefficients -/

/-- L² inner product of two complex-valued functions on a measurable set S.
    ⟨f, g⟩ = ∫_S f(x)·conj(g(x)) dx -/
noncomputable def l2InnerProduct (S : Set ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ x in S, f x * conj (g x)

/-- Fourier coefficient of a function g at frequency ξ on set S.
    c_ξ = ⟨g, exp(2πiξ·)⟩ = ∫_S g(x)·exp(-2πiξx) dx -/
noncomputable def fourierCoeff (S : Set ℝ) (g : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  l2InnerProduct S g (fun x => exp (2 * π * I * ξ * x))

/-- Build a TrigPoly from a finite set of Fourier coefficients.
    Given a finite set of frequencies and their coefficients, construct the TrigPoly. -/
noncomputable def trigPolyFromCoeffs (coeffs : ℝ →₀ ℂ) : TrigPoly := coeffs

/-- The Fourier partial sum of a function up to frequency N. -/
noncomputable def fourierPartialSum (S : Set ℝ) (g : ℝ → ℂ) (N : ℕ) : TrigPoly :=
  -- Build finsupp with support {-N, ..., N} as integers cast to reals
  (Finset.Ico (-N : ℤ) (N + 1)).sum fun n =>
    Finsupp.single (n : ℝ) (fourierCoeff S g n)

/-- Trigonometric polynomials are dense in C(K, ℂ) for any compact K ⊆ ℝ. -/
lemma trigPoly_dense_on_compact (K : Set ℝ) (hK : IsCompact K) :
    ∀ g : C(K, ℂ), ∀ ε > 0, ∃ P : TrigPoly,
      ∀ x : K, ‖g x - P.eval x.val‖ < ε := by
  intro g ε hε
  -- Use Stone-Weierstrass: restrict trigPolyStarSubalgebra to K
  -- The restriction map C(ℝ, ℂ) → C(K, ℂ) is f ↦ f ∘ Subtype.val
  let restrict_on_K : C(ℝ, ℂ) →⋆ₐ[ℂ] C(K, ℂ) :=
    ContinuousMap.compStarAlgHom' ℂ ℂ ⟨Subtype.val, continuous_subtype_val⟩
  -- AK is the image of trigPolyStarSubalgebra under restriction to K
  let AK : StarSubalgebra ℂ C(K, ℂ) :=
    StarSubalgebra.map restrict_on_K trigPolyStarSubalgebra
  -- AK separates points on K (inherited from trigPolyStarSubalgebra)
  have hAK_sep : AK.SeparatesPoints := by
    intro x y hxy
    have hval : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    obtain ⟨P, hP⟩ := trigPoly_separates_points x.val y.val hval
    refine ⟨fun z => P.eval z.val, ?_, hP⟩
    -- Need to show: ∃ a ∈ AK, (fun z => P.eval z.val) = a
    -- AK is the image of trigPolyStarSubalgebra under restrict_on_K
    use trigPolyOnK K P
    constructor
    · -- Show trigPolyOnK K P ∈ AK
      use ⟨P.eval, TrigPoly.continuous_eval P⟩
      exact ⟨⟨P, rfl⟩, rfl⟩
    · -- Show trigPolyOnK K P = fun z => P.eval z.val
      rfl
  -- Apply Stone-Weierstrass for star subalgebras
  -- Make CompactSpace instance available from IsCompact K
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hAK_dense : AK.topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints AK hAK_sep
  -- Since AK is dense (closure = ⊤), we can approximate g by elements of AK
  -- Use density to get an element within ε/2 (or just ε) of g
  have : g ∈ (⊤ : StarSubalgebra ℂ C(K, ℂ)) := trivial
  rw [← hAK_dense] at this
  -- g is in the closure, so there exists h ∈ AK with dist(g, h) < ε
  obtain ⟨h, hh_in_AK, hh_close⟩ := Metric.mem_closure_iff.mp this ε hε
  -- h ∈ AK means h is the restriction of some f ∈ trigPolyStarSubalgebra
  obtain ⟨f, hf_in_trig, rfl⟩ := hh_in_AK
  -- f ∈ trigPolyStarSubalgebra means f.carrier ∈ trigPolySet, so ∃ P with f = P.eval
  obtain ⟨P, rfl⟩ := hf_in_trig
  refine ⟨P, ?_⟩
  intro x
  -- Pointwise bound from sup metric: dist(g, restrict_on_K(...)) < ε
  have hx : dist (g x) (restrict_on_K ⟨P.eval, TrigPoly.continuous_eval P⟩ x) < ε :=
    lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist x) hh_close
  -- Turn dist into norm
  simpa [restrict_on_K, dist_eq_norm] using hx

/-- The functional on trig polynomials induced by a positive-definite function f.
    For P = ∑ c_ξ e^{iξt}, we define Λ(P) = ∑ c_ξ f(ξ).
    This is the key functional for Bochner's theorem. -/
noncomputable def ΛTrig (f : ℝ → ℂ) (P : TrigPoly) : ℂ :=
  ∑ ξ ∈ P.support, (P ξ) * f ξ

/-- ΛTrig is linear: Λ(P + Q) = Λ(P) + Λ(Q).
    Proof: The sum over (P+Q).support equals the sum over P.support + sum over Q.support
    using the distributivity (P+Q)(ξ) * f(ξ) = P(ξ)*f(ξ) + Q(ξ)*f(ξ). -/
lemma ΛTrig_add (f : ℝ → ℂ) (P Q : TrigPoly) :
    ΛTrig f (P + Q) = ΛTrig f P + ΛTrig f Q := by
  unfold ΛTrig
  -- Key: (P + Q).support ⊆ P.support ∪ Q.support
  -- Extend all sums to the union and use (P+Q)(ξ) = P(ξ) + Q(ξ)
  classical
  let S := P.support ∪ Q.support
  have h_subset : (P + Q).support ⊆ S := by
    intro ξ hξ
    by_contra h
    -- h : ¬(ξ ∈ P.support ∨ ξ ∈ Q.support)
    -- Therefore ξ ∉ P.support and ξ ∉ Q.support
    rw [Finset.mem_union, not_or] at h
    have hP : P ξ = 0 := Finsupp.notMem_support_iff.mp h.1
    have hQ : Q ξ = 0 := Finsupp.notMem_support_iff.mp h.2
    -- But hξ says (P + Q) ξ ≠ 0, contradiction
    rw [Finsupp.mem_support_iff] at hξ
    simp [Finsupp.add_apply, hP, hQ] at hξ
  calc ∑ ξ ∈ (P + Q).support, (P + Q) ξ * f ξ
      = ∑ ξ ∈ S, (P + Q) ξ * f ξ := by
        apply Finset.sum_subset h_subset
        intro ξ _ hξ
        simp [Finsupp.notMem_support_iff.mp hξ]
    _ = ∑ ξ ∈ S, (P ξ + Q ξ) * f ξ := by simp
    _ = ∑ ξ ∈ S, (P ξ * f ξ + Q ξ * f ξ) := by simp [add_mul]
    _ = ∑ ξ ∈ S, P ξ * f ξ + ∑ ξ ∈ S, Q ξ * f ξ := Finset.sum_add_distrib
    _ = ∑ ξ ∈ P.support, P ξ * f ξ + ∑ ξ ∈ Q.support, Q ξ * f ξ := by
        congr 1
        · symm; apply Finset.sum_subset Finset.subset_union_left
          intro ξ _ hξ; simp [Finsupp.notMem_support_iff.mp hξ]
        · symm; apply Finset.sum_subset Finset.subset_union_right
          intro ξ _ hξ; simp [Finsupp.notMem_support_iff.mp hξ]

/-- ΛTrig is homogeneous: Λ(c·P) = c·Λ(P).
    Proof: ∑ ξ, (c·P)(ξ) * f(ξ) = ∑ ξ, c * P(ξ) * f(ξ) = c * ∑ ξ, P(ξ) * f(ξ). -/
lemma ΛTrig_smul (f : ℝ → ℂ) (c : ℂ) (P : TrigPoly) :
    ΛTrig f (c • P) = c * ΛTrig f P := by
  unfold ΛTrig
  -- Support of c • P is contained in support of P
  classical
  have h_support : (c • P).support ⊆ P.support := Finsupp.support_smul
  calc ∑ ξ ∈ (c • P).support, (c • P) ξ * f ξ
      = ∑ ξ ∈ P.support, (c • P) ξ * f ξ := by
        apply Finset.sum_subset h_support
        intro ξ _ hξ
        simp [Finsupp.notMem_support_iff.mp hξ]
    _ = ∑ ξ ∈ P.support, (c * P ξ) * f ξ := by simp [Finsupp.smul_apply]
    _ = ∑ ξ ∈ P.support, c * (P ξ * f ξ) := by simp [mul_assoc]
    _ = c * ∑ ξ ∈ P.support, P ξ * f ξ := by rw [← Finset.mul_sum]

/-! ## Bochner's Theorem for the Circle Group 𝕋 = ℝ/ℤ -/

/-- The circle group 𝕋 = ℝ/ℤ, represented as AddCircle 1. -/
abbrev 𝕋 := AddCircle (1 : ℝ)

/-- A positive-definite function on 𝕋 (periodic with period 1).
    This is the setup for Herglotz theorem. -/
structure PositiveDefiniteOn𝕋 where
  f : 𝕋 → ℂ
  continuous : Continuous f
  pos_def : IsPositiveDefinite (f ∘ QuotientAddGroup.mk)

/-! ### Inner Product on U(1) = 𝕋 -/

/-- Inner product on C(𝕋, ℂ) with respect to Haar measure.
    ⟨f, g⟩_𝕋 = ∫_𝕋 f(x) · conj(g(x)) dx -/
noncomputable def innerProduct𝕋 (f g : C(𝕋, ℂ)) : ℂ :=
  ∫ x : 𝕋, f x * conj (g x)

/-- The inner product is Hermitian: ⟨f, g⟩ = conj(⟨g, f⟩).
    Proof: conj(∫ f·conj(g)) = ∫ conj(f·conj(g)) = ∫ conj(f)·g = ∫ g·conj(f) -/
lemma innerProduct𝕋_conj_symm (f g : C(𝕋, ℂ)) :
    conj (innerProduct𝕋 f g) = innerProduct𝕋 g f := by
  unfold innerProduct𝕋
  rw [← integral_conj]
  congr 1
  ext x
  simp only [Pi.conj_apply, map_mul, conj_conj]
  ring

/-- The inner product is positive semi-definite: ⟨f, f⟩ has non-negative real part.
    Proof: ∫ f·conj(f) = ∫ |f|² ≥ 0 -/
lemma innerProduct𝕋_self_nonneg (f : C(𝕋, ℂ)) :
    0 ≤ (innerProduct𝕋 f f).re := by
  unfold innerProduct𝕋
  have h_eq : ∀ x, f x * conj (f x) = (Complex.normSq (f x) : ℂ) := fun x => Complex.mul_conj (f x)
  simp_rw [h_eq]
  -- The integral of normSq (real and ≥ 0) cast to ℂ equals ofReal of the real integral
  have h_integral : ∫ x : 𝕋, (Complex.normSq (f x) : ℂ) = ↑(∫ x : 𝕋, Complex.normSq (f x)) :=
    integral_ofReal
  rw [h_integral, Complex.ofReal_re]
  apply MeasureTheory.integral_nonneg
  intro x
  exact Complex.normSq_nonneg (f x)

/-- The inner product is additive in the second argument. -/
lemma innerProduct𝕋_add_right (f g h : C(𝕋, ℂ)) :
    innerProduct𝕋 f (g + h) = innerProduct𝕋 f g + innerProduct𝕋 f h := by
  unfold innerProduct𝕋
  simp only [ContinuousMap.add_apply, map_add, mul_add]
  -- Continuous functions on compact 𝕋 are integrable
  have cont_fg : Continuous (fun x => f x * conj (g x)) := by fun_prop
  have cont_fh : Continuous (fun x => f x * conj (h x)) := by fun_prop
  have hfg : Integrable (fun x => f x * conj (g x)) :=
    cont_fg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfh : Integrable (fun x => f x * conj (h x)) :=
    cont_fh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact integral_add hfg hfh

/-- The inner product is additive in the first argument. -/
lemma innerProduct𝕋_add_left (f g h : C(𝕋, ℂ)) :
    innerProduct𝕋 (f + g) h = innerProduct𝕋 f h + innerProduct𝕋 g h := by
  unfold innerProduct𝕋
  simp only [ContinuousMap.add_apply, add_mul]
  have cont_fh : Continuous (fun x => f x * conj (h x)) := by fun_prop
  have cont_gh : Continuous (fun x => g x * conj (h x)) := by fun_prop
  have hfh : Integrable (fun x => f x * conj (h x)) :=
    cont_fh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgh : Integrable (fun x => g x * conj (h x)) :=
    cont_gh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact integral_add hfh hgh

/-- Scalar multiplication in the second argument (conjugate-linear).
    ⟨f, c·g⟩ = conj(c) · ⟨f, g⟩ -/
lemma innerProduct𝕋_smul_right (f g : C(𝕋, ℂ)) (c : ℂ) :
    innerProduct𝕋 f (c • g) = conj c * innerProduct𝕋 f g := by
  unfold innerProduct𝕋
  simp only [ContinuousMap.smul_apply, smul_eq_mul, map_mul]
  have h : ∀ x, f x * (conj c * conj (g x)) = conj c * (f x * conj (g x)) := fun x => by ring
  simp_rw [h]
  -- Pull constant out of integral: ∫ c * f = c * ∫ f
  rw [← smul_eq_mul, ← integral_smul]
  rfl

/-- Scalar multiplication in the first argument (linear).
    ⟨c·f, g⟩ = c · ⟨f, g⟩ -/
lemma innerProduct𝕋_smul_left (f g : C(𝕋, ℂ)) (c : ℂ) :
    innerProduct𝕋 (c • f) g = c * innerProduct𝕋 f g := by
  unfold innerProduct𝕋
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  have h : ∀ x, c * f x * conj (g x) = c * (f x * conj (g x)) := fun x => by ring
  simp_rw [h]
  rw [← smul_eq_mul, ← integral_smul]
  rfl

/-! ### Parseval's Theorem on 𝕋 -/

/-! ### Bochner's Theorem (Herglotz) for 𝕋 -/

/-! ### Connecting TrigPoly to the Circle Group -/

/-- LAURENT POLYNOMIALS AS TRIGONOMETRIC POLYNOMIALS -/
abbrev TrigPolyℤ := Finsupp ℤ ℂ

/-- Convert a TrigPolyℤ to a continuous function on 𝕋 = AddCircle 1.
    For P = ∑ cₙ δₙ, this gives x ↦ ∑ cₙ fourier n x on the circle. -/
noncomputable def TrigPolyℤ.toCircle (P : TrigPolyℤ) : C(𝕋, ℂ) where
  toFun := fun t => ∑ n ∈ P.support, P n * fourier n t
  continuous_toFun := by
    -- Sum of finitely many continuous functions is continuous
    refine continuous_finset_sum _ (fun n _ => ?_)
    exact Continuous.mul continuous_const (fourier n).continuous

lemma TrigPolyℤ.toCircle_eval (P : TrigPolyℤ) (x : ℝ) :
    P.toCircle (x : 𝕋) = ∑ n ∈ P.support, P n * fourier n (x : 𝕋) := rfl

/-- The functional on integer-indexed trig polynomials. -/
noncomputable def ΛTrigℤ (f : ℝ → ℂ) (P : TrigPolyℤ) : ℂ :=
  ∑ n ∈ P.support, P n * f n

/-- ΛTrigℤ is linear in the first argument. -/
lemma ΛTrigℤ_add (f : ℝ → ℂ) (P Q : TrigPolyℤ) :
    ΛTrigℤ f (P + Q) = ΛTrigℤ f P + ΛTrigℤ f Q := by
  unfold ΛTrigℤ
  classical
  let S := P.support ∪ Q.support
  have h_subset : (P + Q).support ⊆ S := by
    intro n hn
    by_contra h
    rw [Finset.mem_union, not_or] at h
    have hP : P n = 0 := Finsupp.notMem_support_iff.mp h.1
    have hQ : Q n = 0 := Finsupp.notMem_support_iff.mp h.2
    rw [Finsupp.mem_support_iff] at hn
    simp [Finsupp.add_apply, hP, hQ] at hn
  calc ∑ n ∈ (P + Q).support, (P + Q) n * f n
      = ∑ n ∈ S, (P + Q) n * f n := by
        apply Finset.sum_subset h_subset
        intro n _ hn; simp [Finsupp.notMem_support_iff.mp hn]
    _ = ∑ n ∈ S, (P n + Q n) * f n := by simp
    _ = ∑ n ∈ S, (P n * f n + Q n * f n) := by simp [add_mul]
    _ = ∑ n ∈ S, P n * f n + ∑ n ∈ S, Q n * f n := Finset.sum_add_distrib
    _ = ∑ n ∈ P.support, P n * f n + ∑ n ∈ Q.support, Q n * f n := by
        congr 1
        · symm; apply Finset.sum_subset Finset.subset_union_left
          intro n _ hn; simp [Finsupp.notMem_support_iff.mp hn]
        · symm; apply Finset.sum_subset Finset.subset_union_right
          intro n _ hn; simp [Finsupp.notMem_support_iff.mp hn]

/-- ΛTrigℤ is homogeneous. -/
lemma ΛTrigℤ_smul (f : ℝ → ℂ) (c : ℂ) (P : TrigPolyℤ) :
    ΛTrigℤ f (c • P) = c * ΛTrigℤ f P := by
  unfold ΛTrigℤ
  classical
  have h_support : (c • P).support ⊆ P.support := Finsupp.support_smul
  calc ∑ n ∈ (c • P).support, (c • P) n * f n
      = ∑ n ∈ P.support, (c • P) n * f n := by
        apply Finset.sum_subset h_support
        intro n _ hn; simp [Finsupp.notMem_support_iff.mp hn]
    _ = ∑ n ∈ P.support, (c * P n) * f n := by simp [Finsupp.smul_apply]
    _ = ∑ n ∈ P.support, c * (P n * f n) := by simp [mul_assoc]
    _ = c * ∑ n ∈ P.support, P n * f n := by rw [← Finset.mul_sum]

/-- The image of TrigPolyℤ.toCircle is exactly the span of Mathlib's fourier functions.
    This is the key density result: trig polynomials are dense in C(𝕋, ℂ). -/
theorem trigPolyℤ_span_eq_fourier_span :
    Submodule.span ℂ (Set.range TrigPolyℤ.toCircle) =
    Submodule.span ℂ (Set.range (fun n : ℤ => (fourier n : C(𝕋, ℂ)))) := by
  apply le_antisymm
  -- (≤) Every TrigPolyℤ.toCircle P is in span of fourier functions
  · rw [Submodule.span_le]
    rintro _ ⟨P, rfl⟩
    -- P.toCircle as a ContinuousMap equals ∑ n ∈ P.support, P n • fourier n
    -- First, show this as an equality of continuous maps
    have h_eq : P.toCircle = ∑ n ∈ P.support, P n • (fourier n : C(𝕋, ℂ)) := by
      ext t
      simp [TrigPolyℤ.toCircle, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
            Pi.smul_apply, Finset.sum_apply]
    rw [h_eq]
    -- Now it's literally a finite sum in the span
    exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ (P n) (Submodule.subset_span ⟨n, rfl⟩)
  -- (≥) Every fourier n is in span of TrigPolyℤ.toCircle
  · rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    -- (fun n => fourier n) n = fourier n = TrigPolyℤ.toCircle (Finsupp.single n 1)
    change (fourier n : C(𝕋, ℂ)) ∈ _
    have h : (fourier n : C(𝕋, ℂ)) = TrigPolyℤ.toCircle (Finsupp.single n 1) := by
      ext t
      simp only [TrigPolyℤ.toCircle, ContinuousMap.coe_mk]
      rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
          Finsupp.single_eq_same, one_mul]
    rw [h]
    exact Submodule.subset_span ⟨Finsupp.single n 1, rfl⟩

/-- Trig polynomials (with integer frequencies) are dense in C(𝕋, ℂ).
    This uses Mathlib's span_fourier_closure_eq_top. -/
theorem trigPolyℤ_dense :
    (Submodule.span ℂ (Set.range TrigPolyℤ.toCircle)).topologicalClosure = ⊤ := by
  rw [trigPolyℤ_span_eq_fourier_span]
  haveI : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
  exact span_fourier_closure_eq_top

/-! ### The Functional on C(𝕋) via Extension -/

/-! ### Linearity of `TrigPolyℤ.toCircle` -/

lemma TrigPolyℤ.toCircle_add (P Q : TrigPolyℤ) :
    (P + Q).toCircle = P.toCircle + Q.toCircle := by
  classical
  ext t
  -- same support-union trick as ΛTrigℤ_add
  let S := P.support ∪ Q.support
  have h_subset : (P + Q).support ⊆ S := by
    intro n hn
    by_contra h
    rw [Finset.mem_union, not_or] at h
    have hP : P n = 0 := Finsupp.notMem_support_iff.mp h.1
    have hQ : Q n = 0 := Finsupp.notMem_support_iff.mp h.2
    rw [Finsupp.mem_support_iff] at hn
    simp [Finsupp.add_apply, hP, hQ] at hn
  -- unfold pointwise value of toCircle
  simp [TrigPolyℤ.toCircle]
  -- now we are in ℂ with finite sums
  calc
    ∑ n ∈ (P + Q).support, (P n + Q n) * (fourier n t)
        = ∑ n ∈ S, (P n + Q n) * (fourier n t) := by
            apply Finset.sum_subset h_subset
            intro n _ hn
            -- terms vanish if n ∉ (P+Q).support
            have : (P + Q) n = 0 := Finsupp.notMem_support_iff.mp hn
            simp [Finsupp.add_apply] at this
            simp [this]
    _ = ∑ n ∈ S, (P n * fourier n t + Q n * fourier n t) := by
            simp [add_mul]
    _ = (∑ n ∈ S, P n * fourier n t) + (∑ n ∈ S, Q n * fourier n t) := by
            simpa [Finset.sum_add_distrib]
    _ = (∑ n ∈ P.support, P n * fourier n t) + (∑ n ∈ Q.support, Q n * fourier n t) := by
            congr 1
            · symm
              apply Finset.sum_subset Finset.subset_union_left
              intro n _ hn
              simp [Finsupp.notMem_support_iff.mp hn]
            · symm
              apply Finset.sum_subset Finset.subset_union_right
              intro n _ hn
              simp [Finsupp.notMem_support_iff.mp hn]

lemma TrigPolyℤ.toCircle_smul (c : ℂ) (P : TrigPolyℤ) :
    (c • P).toCircle = c • P.toCircle := by
  classical
  ext t
  have h_support : (c • P).support ⊆ P.support := Finsupp.support_smul
  -- unfold pointwise values
  simp [TrigPolyℤ.toCircle]
  calc
    ∑ n ∈ (c • P).support, (c * P n) * (fourier n t)
        = ∑ n ∈ P.support, (c * P n) * (fourier n t) := by
            apply Finset.sum_subset h_support
            intro n _ hn
            have : (c • P) n = 0 := Finsupp.notMem_support_iff.mp hn
            simp [Finsupp.smul_apply] at this
            simp [this]
    _ = ∑ n ∈ P.support, c * (P n * fourier n t) := by
            simp [mul_assoc]
    _ = c * ∑ n ∈ P.support, (P n * fourier n t) := by
            simpa [Finset.mul_sum]

lemma TrigPolyℤ.toCircle_single_zero (c : ℂ) (θ : 𝕋) :
    TrigPolyℤ.toCircle (Finsupp.single 0 c) θ = c := by
  unfold TrigPolyℤ.toCircle
  simp only [ContinuousMap.coe_mk]
  by_cases h_ne : c = 0
  · simp [h_ne]
  · rw [Finsupp.support_single_ne_zero _ h_ne, Finset.sum_singleton,
      Finsupp.single_eq_same]
    -- fourier 0 = exp(0) = 1
    simp only [fourier, Int.cast_zero, zero_smul]
    norm_num

/-- Since `toCircle` is ℂ-linear, the span of its range equals the range itself. -/
lemma trigPolyℤ_toCircle_span_eq_range :
    (Submodule.span ℂ (Set.range TrigPolyℤ.toCircle) : Set (C(𝕋, ℂ))) =
      Set.range TrigPolyℤ.toCircle := by
  apply Set.Subset.antisymm
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
        exact hx
    | zero =>
        refine ⟨0, ?_⟩
        ext t
        simp [TrigPolyℤ.toCircle]
    | add y₁ y₂ _ _ ih₁ ih₂ =>
        obtain ⟨P₁, rfl⟩ := ih₁
        obtain ⟨P₂, rfl⟩ := ih₂
        refine ⟨P₁ + P₂, ?_⟩
        simpa [TrigPolyℤ.toCircle_add]
    | smul c y _ ih =>
        obtain ⟨P, rfl⟩ := ih
        refine ⟨c • P, ?_⟩
        simpa [TrigPolyℤ.toCircle_smul]
  · intro y ⟨P, hP⟩
    rw [← hP]
    exact Submodule.subset_span ⟨P, rfl⟩

/-- ΛTrigℤ is positive on |P|² functions: For any trig poly P, Λ(|P|²) ≥ 0. -/
lemma ΛTrigℤ_nonneg_on_normSq (f : ℝ → ℂ) (hf_pos : IsPositiveDefinite f) (P : TrigPolyℤ) :
    0 ≤ (∑ m ∈ P.support, ∑ n ∈ P.support, conj (P m) * P n * f (m - n)).re := by
  classical
  -- This is EXACTLY the positive-definite condition!
  -- Strategy: Reindex the Finset sum to a Fin sum, then apply hf_pos.2

  -- Step 1: Handle empty support case
  by_cases h_empty : P.support = ∅
  · simp [h_empty]
  -- Step 2: Get the bijection between support and Fin (card)
  let N := P.support.card
  let enum := P.support.equivFin
  -- Step 3: Define the functions needed for IsPositiveDefinite
  let x : Fin N → ℝ := fun i => ((enum.symm i).val : ℤ)
  let c : Fin N → ℂ := fun i => P (enum.symm i).val
  -- Step 4: Show the sums are equal by reindexing
  have h_eq : (∑ m ∈ P.support, ∑ n ∈ P.support, conj (P m) * P n * f (m - n)).re
            = (∑ i : Fin N, ∑ j : Fin N, conj (c i) * c j * f (x i - x j)).re := by
    congr 1
    -- Convert Finset sum to subtype sum, then reindex using enum
    trans (∑ m : P.support, ∑ n : P.support, conj (P m.val) * P n.val * f (m.val - n.val))
    · -- The sums are equal: ∑ ∈ P.support = ∑ : P.support with coercions
      conv_lhs => rw [← Finset.sum_coe_sort P.support]
      conv_lhs => arg 2; ext; rw [← Finset.sum_coe_sort P.support]
    · -- Now reindex using enum for both outer and inner sums
      erw [Fintype.sum_equiv enum]
      intro a
      simp only [x, c, Equiv.symm_apply_apply]
      erw [Fintype.sum_equiv enum]
      simp only [Equiv.symm_apply_apply]
      intro; trivial
  -- Step 5: Apply positive-definiteness
  rw [h_eq]
  exact hf_pos.2 N x c

/-- Nonnegativity in the (n,m) order: conj(P n) * P m * f(m-n). -/
lemma ΛTrigℤ_nonneg_on_normSq_nm (f : ℝ → ℂ) (hf : IsPositiveDefinite f) (P : TrigPolyℤ) :
    0 ≤ (∑ n ∈ P.support, ∑ m ∈ P.support,
          (starRingEnd ℂ) (P n) * P m * f (↑m - ↑n)).re := by
  classical
  by_cases h_empty : P.support = ∅
  · simp [h_empty]
  let N := P.support.card
  let enum : (↥P.support) ≃ Fin N := P.support.equivFin
  let x0 : Fin N → ℝ := fun i => (↑(↑(enum.symm i)) : ℝ)   -- base points in ℝ
  let x  : Fin N → ℝ := fun i => -(x0 i)                  -- negate to flip differences
  let c  : Fin N → ℂ := fun i => P (↑(enum.symm i))
  -- Reindex Finset double-sum to Fin double-sum
  have h_eq :
      (∑ n ∈ P.support, ∑ m ∈ P.support,
          (starRingEnd ℂ) (P n) * P m * f (↑m - ↑n)).re
        =
      (∑ i : Fin N, ∑ j : Fin N,
          (starRingEnd ℂ) (c i) * c j * f (x i - x j)).re := by
    -- Same reindexing pattern you already used elsewhere:
    --  Finset.sum ↔ sum over subtype ↔ sum_equiv enum
    congr 1
    -- outer
    trans (∑ n : P.support, ∑ m : P.support,
            (starRingEnd ℂ) (P (n : ℤ)) * P (m : ℤ) * f ((m : ℤ) - (n : ℤ)))
    · conv_lhs => rw [← Finset.sum_coe_sort P.support]
      conv_lhs => arg 2; ext; rw [← Finset.sum_coe_sort P.support]
    ·-- push to Fin using enum.symm (IMPORTANT: direction!)
      erw [Fintype.sum_equiv enum.symm]
      intro i
      erw [Fintype.sum_equiv enum.symm]
      intro j
      -- now simplify the mapped pieces
      -- key identity: x i - x j = (x0 j) - (x0 i)
      have hx : x i - x j = x0 j - x0 i := by
      -- x = -x0
        simp [x, x0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      -- and x0 j - x0 i = ↑m - ↑n after coercions
      simp only [c, x, x0, hx, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- Apply positive-definiteness on Fin, then rewrite back
  have : 0 ≤ (∑ i : Fin N, ∑ j : Fin N,
              (starRingEnd ℂ) (c i) * c j * f (x i - x j)).re :=
    hf.2 N x c
  simpa [h_eq] using this

/-- For a positive-definite function, f(0) is real and nonnegative. -/
lemma f_zero_real_nonneg (f : ℝ → ℂ) (hf : IsPositiveDefinite f) :
    f 0 = (f 0).re ∧ 0 ≤ (f 0).re := by
  constructor
  · -- f(0) is real: f(0) = conj(f(0))
    have h_conj : conj (f 0) = f 0 := by
      have := hf.1 0
      simp at this
      exact this.symm
    exact (Complex.conj_eq_iff_re.mp h_conj).symm
  · -- f(0) ≥ 0: apply positive-definiteness with n=1, x₁=0, c₁=1
    have h_pos := hf.2 1 (fun _ => 0) (fun _ => 1)
    simp at h_pos
    exact h_pos

/-- The constant polynomial 1 (coefficient 1 at index 0, zero elsewhere). -/
noncomputable def TrigPolyℤ.const_one : TrigPolyℤ :=
  Finsupp.single 0 1

/-- Λ applied to the constant polynomial 1 equals f(0). -/
lemma ΛTrigℤ_const_one (f : ℝ → ℂ) :
    ΛTrigℤ f TrigPolyℤ.const_one = f 0 := by
  unfold ΛTrigℤ TrigPolyℤ.const_one
  rw [Finsupp.support_single_ne_zero _ (one_ne_zero)]
  rw [Finset.sum_singleton]
  rw [Finsupp.single_eq_same]
  -- goal: (1 : ℂ) * f ↑0 = f 0
  simpa using (by simp)

/-- NORM-SQUARED AS LAURENT AUTOCORRELATION -/
noncomputable def TrigPolyℤ.normSq (P : TrigPolyℤ) : TrigPolyℤ := by
  classical
  let S : Finset ℤ := P.support
  let supp : Finset ℤ := (S.product S).image (fun mn : ℤ × ℤ => mn.1 - mn.2)
  -- underlying coefficient function
  let g : ℤ → ℂ :=
    fun k => Finset.sum S (fun n => (starRingEnd ℂ) (P n) * P (n + k))
  -- key: outside `supp`, g k = 0
  have g_eq_zero_of_not_mem : ∀ k, k ∉ supp → g k = 0 := by
    intro k hk
    -- show every summand is zero because n+k ∉ support
    have hshift : ∀ n ∈ S, n + k ∉ S := by
      intro n hn hnk
      have hmem : (n + k, n) ∈ S.product S :=
        Finset.mem_product.mpr ⟨hnk, hn⟩
      have hdif : (n + k) - n ∈ supp := by
        refine Finset.mem_image.mpr ?_
        refine ⟨(n + k, n), hmem, by simp⟩
      have hk' : (n + k) - n = k := by
        simpa using (add_sub_cancel_left n k)
      have : k ∈ supp := by simpa [hk'] using hdif
      exact hk this
    have hPk : ∀ n ∈ S, P (n + k) = 0 := by
      intro n hn
      -- deprecated name fix:
      exact (Finsupp.notMem_support_iff.mp (hshift n hn))
    -- now g k is sum of zeros
    refine Finset.sum_eq_zero ?_
    intro n hn
    simp [g, hPk n hn]
  -- support of g is contained in `supp`, hence finite
  have hfinite : (Set.Finite {k : ℤ | g k ≠ 0}) := by
    refine (supp.finite_toSet.subset ?_)
    intro k hk
    by_contra hks
    have : g k = 0 := g_eq_zero_of_not_mem k hks
    exact hk this
  -- build the finsupp from the function + finite support
  exact Finsupp.ofSupportFinite g hfinite

/-- The double sum in ΛTrigℤ_nonneg_on_normSq equals Λ applied to normSq polynomial. -/
lemma ΛTrigℤ_normSq_eq_double_sum (f : ℝ → ℂ) (P : TrigPolyℤ) :
    ΛTrigℤ f (TrigPolyℤ.normSq P) =
      ∑ n ∈ P.support, ∑ m ∈ P.support,
        (starRingEnd ℂ) (P n) * P m * f (m - n) := by
  classical
  unfold ΛTrigℤ TrigPolyℤ.normSq
  set T := (TrigPolyℤ.normSq P).support
  set S := P.support
  set supp := (S.product S).image (fun mn : ℤ × ℤ => mn.1 - mn.2)
  let g : ℤ → ℂ := fun k => Finset.sum S (fun n => (starRingEnd ℂ) (P n) * P (n + k))
  have g_eq_zero_of_not_mem : ∀ k, k ∉ supp → g k = 0 := by
    intro k hk
    have hshift : ∀ n ∈ S, n + k ∉ S := by
      intro n hn hnk
      have hmem : (n + k, n) ∈ S.product S := Finset.mem_product.mpr ⟨hnk, hn⟩
      have hdif : (n + k) - n ∈ supp := by
        refine Finset.mem_image.mpr ?_
        refine ⟨(n + k, n), hmem, by simp⟩
      have hk' : (n + k) - n = k := by simpa using (add_sub_cancel_left n k)
      have : k ∈ supp := by simpa [hk'] using hdif
      exact hk this
    have hPk : ∀ n ∈ S, P (n + k) = 0 := by
      intro n hn
      exact (Finsupp.notMem_support_iff.mp (hshift n hn))
    refine Finset.sum_eq_zero ?_
    intro n hn
    simp [g, hPk n hn]
  have hsub : T ⊆ supp := by
    intro k hkT
    have hk0 : (TrigPolyℤ.normSq P) k ≠ 0 := (Finsupp.mem_support_iff.mp hkT)
    by_contra hks
    have hg : g k = 0 := g_eq_zero_of_not_mem k hks
    have : (TrigPolyℤ.normSq P) k = 0 := by simpa [TrigPolyℤ.normSq, g, hg]
    exact hk0 this
  have hzero : ∀ k ∈ supp, k ∉ T → g k * f k = 0 := by
    intro k hkSupp hkNotT
    have : (TrigPolyℤ.normSq P) k = 0 := (Finsupp.notMem_support_iff.mp hkNotT)
    have : g k = 0 := by simpa [TrigPolyℤ.normSq, g] using this
    simp [this]
  have this : ∑ k ∈ T, g k * f (k : ℝ) = ∑ k ∈ supp, g k * f (k : ℝ) :=
    Finset.sum_subset hsub hzero
  -- First: rewrite the LHS Λ-sum into the (T, g) form
  have hLHS :
      (∑ k ∈ (TrigPolyℤ.normSq P).support, (TrigPolyℤ.normSq P) k * f (k : ℝ))
        =
      ∑ k ∈ T, g k * f (k : ℝ) := by
    -- unfold T so RHS binder becomes `(normSq P).support`
    dsimp [T]
    -- now binders match definitionally; only need to show values match
    refine Finset.sum_congr rfl ?_
    intro k hk
    -- show (normSq P) k = g k
    unfold TrigPolyℤ.normSq
    simp only [Finsupp.ofSupportFinite_coe]
    rfl
  -- now rewrite goal using hLHS
  -- First, fold TrigPolyℤ.normSq back up so rw can match
  change (∑ k ∈ (TrigPolyℤ.normSq P).support, (TrigPolyℤ.normSq P) k * f (k : ℝ)) = _
  rw [hLHS]
  rw [this]   -- now goal is the sum over `supp`
  -- unfold g and S without simp (avoids recursion loops)
  dsimp only [g, S]
  -- distribute multiplication into the inner sum: (∑ n, a n) * b = ∑ n, a n * b
  conv_lhs => arg 2; intro k; rw [Finset.sum_mul]
  -- reassociate inside: (a * b) * c = a * b * c
  conv_lhs => arg 2; intro k; arg 2; intro n; rw [mul_assoc]
  -- Now: LHS = ∑ k ∈ supp, ∑ n ∈ P.support, conj(P n) * (P(n+k) * f k)
  --      RHS = ∑ m ∈ P.support, ∑ n ∈ P.support, conj(P m) * P n * f(m-n)
  -- Strategy: swap summation order on LHS, then reindex using m = n + k
  -- Step 1: Swap summation order
  rw [Finset.sum_comm]
  -- Now: LHS = ∑ n ∈ P.support, ∑ k ∈ supp, conj(P n) * (P(n+k) * f k)
  -- Step 2: For each fixed n, reindex the inner sum using m = n + k
  refine Finset.sum_congr rfl ?_
  intro n hn
  -- Now n ∈ S = P.support is available as hypothesis hn
  -- Goal: ∑ k ∈ supp, conj(P n) * (P(n+k) * f k) = ∑ m ∈ P.support, conj(P n) * P m * f(m-n)
  -- Eliminate terms where P(n+k) = 0 (i.e., n+k ∉ P.support)
  have sum_restrict : ∑ k ∈ supp, (starRingEnd ℂ) (P n) * (P (n + k) * f ↑k) =
      ∑ k ∈ supp.filter (fun k => n + k ∈ P.support),
        (starRingEnd ℂ) (P n) * (P (n + k) * f ↑k) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk_supp hk_not_filter
    simp only [Finset.mem_filter, not_and] at hk_not_filter
    have hnk : n + k ∉ P.support := hk_not_filter hk_supp
    have : P (n + k) = 0 := Finsupp.notMem_support_iff.mp hnk
    simp [this]
  rw [sum_restrict]
  -- Now reindex the filtered sum by m := n + k.
  -- Domain: F = { k ∈ supp | n+k ∈ S }
  -- Codomain: S
  set F : Finset ℤ := supp.filter (fun k => n + k ∈ S)
  -- rewrite binder to use F
  have : (∑ k ∈ supp.filter (fun k => n + k ∈ S),
            (starRingEnd ℂ) (P n) * (P (n + k) * f (k : ℝ)))
        =
        ∑ k ∈ F, (starRingEnd ℂ) (P n) * (P (n + k) * f (k : ℝ)) := by
    rfl
  rw [this]
  -- helper: for any m∈S, (m - n) ∈ supp (because supp is image of S×S under subtraction)
  have hm_sub_mem_supp : ∀ {m : ℤ}, m ∈ S → m - n ∈ supp := by
    intro m hm
    refine Finset.mem_image.mpr ?_
    refine ⟨(m, n), ?_, by simp⟩
    exact Finset.mem_product.mpr ⟨hm, hn⟩
  -- Now do the bijection between S and F using i(m)=m-n and j(k)=n+k.
  -- After reindexing, the inner sum becomes exactly ∑ m∈S conj(P n)*P m*f(m-n).
  have hnS : n ∈ S := hn
  -- handy simp lemmas for ℤ arithmetic
  have h_add_sub : ∀ m : ℤ, n + (m - n) = m := by
    intro m
    -- (m - n) + n = m, then commute
    simpa [add_comm, add_left_comm, add_assoc] using (sub_add_cancel m n)
  have h_sub_add : ∀ k : ℤ, (n + k) - n = k := by
    intro k
    simpa [add_assoc] using (add_sub_cancel_left n k)
  -- cast lemma: ↑(m-n) = ↑m - ↑n
  have h_cast_sub : ∀ m : ℤ, ((m - n : ℤ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    intro m
    norm_cast
  -- do the reindexing: map k ∈ F to m = n+k ∈ S
  refine Finset.sum_bij
      (fun k hk => n + k) ?_ ?_ ?_ ?_
  · -- (1) membership: k∈F → (n+k)∈S
    intro k hk
    -- k ∈ F means k ∈ supp ∧ n + k ∈ S
    exact (Finset.mem_filter.mp hk).2
  · -- (2) injectivity: (n+k₁)=(n+k₂) → k₁=k₂
    intro k₁ hk₁ k₂ hk₂ hab
    -- hab : n + k₁ = n + k₂
    have := congrArg (fun t : ℤ => t - n) hab
    simp only [add_sub_cancel_left] at this
    exact this
  · -- (3) surjectivity onto S
    intro m hm
    -- need to show ∃ k ∈ F, n + k = m
    -- let k := m - n
    have hk_in_supp : m - n ∈ supp := hm_sub_mem_supp hm
    refine ⟨m - n, ?_, h_add_sub m⟩
    -- show m - n ∈ F
    refine Finset.mem_filter.mpr ⟨hk_in_supp, ?_⟩
    rw [h_add_sub m]
    exact hm
  · -- (4) summand preservation
    intro k hk
    -- First simplify the mapped index ((fun k hk ↦ n+k) k hk) ↦ n+k
    -- Then handle the ℝ-cast subtraction.
    have hR : ((n + k : ℤ) : ℝ) - (n : ℝ) = (k : ℝ) := by
      -- cast (n+k) = cast n + cast k, then (a+b)-a = b
      simpa [Int.cast_add] using (add_sub_cancel_left (n : ℝ) (k : ℝ))
    -- Now everything matches
    -- `simp` will turn P ((fun...) k hk) into P (n+k) and the f-argument into f(((n+k):ℝ)-(n:ℝ))
    -- then we rewrite that to f(k).
    simp [hR, mul_assoc, mul_left_comm, mul_comm]

/-- Λ is nonnegative on norm-squared polynomials. -/
lemma ΛTrigℤ_normSq_nonneg (f : ℝ → ℂ) (hf : IsPositiveDefinite f) (P : TrigPolyℤ) :
    0 ≤ (ΛTrigℤ f (TrigPolyℤ.normSq P)).re := by
  rw [ΛTrigℤ_normSq_eq_double_sum]
  exact ΛTrigℤ_nonneg_on_normSq_nm f hf P

/-- Conjugate symmetry of the double sum when `f` is Hermitian
    (`f (-x) = conj (f x)`), i.e. `conj(B(P,Q)) = B(Q,P)`. -/
lemma double_sum_conj_symm (f : ℝ → ℂ) (hf : IsPositiveDefinite f) (P Q : TrigPolyℤ) :
    conj (∑ m ∈ P.support, ∑ n ∈ Q.support,
            conj (P m) * Q n * f ((m : ℝ) - (n : ℝ))) =
      ∑ m ∈ Q.support, ∑ n ∈ P.support,
            conj (Q m) * P n * f ((m : ℝ) - (n : ℝ)) := by
  classical
  -- Hermitian symmetry in the useful direction: conj (f x) = f (-x)
  have hf' : ∀ x : ℝ, conj (f x) = f (-x) := by
    intro x
    simpa using (hf.1 x).symm
  -- Step 1: push conj through the sums *by hand* to control the shape
  -- and rewrite conj(f(m-n)) using hf'
  have h1 :
      conj (∑ m ∈ P.support, ∑ n ∈ Q.support,
              conj (P m) * Q n * f ((m : ℝ) - (n : ℝ)))
        =
      ∑ m ∈ P.support, ∑ n ∈ Q.support,
        P m * conj (Q n) * f ((n : ℝ) - (m : ℝ)) := by
    -- push conj inside both sums
    simp [map_sum]  -- only map_sum, no giant simp set
    -- now you're at elementwise goal; do it under binders:
    refine Finset.sum_congr rfl ?_
    intro m hm
    refine Finset.sum_congr rfl ?_
    intro n hn
    -- compute conj of product
    -- conj(conj(P m) * Q n * f(m-n)) = P m * conj(Q n) * conj(f(m-n))
    -- then use hf' to turn conj(f(..)) into f(-(m-n)) = f(n-m)
    have hneg : -(((m : ℤ) : ℝ) - ((n : ℤ) : ℝ)) = ((n : ℤ) : ℝ) - ((m : ℤ) : ℝ) := by
      ring
    -- do the rewrites with rw (not simp)
    -- `simp` is safe here because it's tiny + local
    simp [mul_assoc, mul_left_comm, mul_comm, hf', hneg]
  -- Step 2: swap the order of summation
  -- (this is the genuine swap between different supports)
  have h2 :
      (∑ m ∈ P.support, ∑ n ∈ Q.support,
          P m * conj (Q n) * f ((n : ℝ) - (m : ℝ)))
        =
      (∑ n ∈ Q.support, ∑ m ∈ P.support,
          P m * conj (Q n) * f ((n : ℝ) - (m : ℝ))) := by
    exact Finset.sum_comm (s := P.support) (t := Q.support)
      (f := fun m n => P m * conj (Q n) * f ((n : ℝ) - (m : ℝ)))
  -- Step 3: rewrite integrand to match target (just commute factors + rename binders)
  have h3 :
      (∑ n ∈ Q.support, ∑ m ∈ P.support,
          P m * conj (Q n) * f ((n : ℝ) - (m : ℝ)))
        =
      (∑ m ∈ Q.support, ∑ n ∈ P.support,
          conj (Q m) * P n * f ((m : ℝ) - (n : ℝ))) := by
    -- same finsets, just binder names + commutativity
    refine Finset.sum_congr rfl ?_
    intro m hm
    refine Finset.sum_congr rfl ?_
    intro n hn
    -- commute factors
    ring_nf
  -- finish
  calc
    conj (∑ m ∈ P.support, ∑ n ∈ Q.support,
            conj (P m) * Q n * f ((m : ℝ) - (n : ℝ)))
        =
      ∑ m ∈ P.support, ∑ n ∈ Q.support,
        P m * conj (Q n) * f ((n : ℝ) - (m : ℝ)) := h1
    _ =
      ∑ n ∈ Q.support, ∑ m ∈ P.support,
        P m * conj (Q n) * f ((n : ℝ) - (m : ℝ)) := h2
    _ =
      ∑ m ∈ Q.support, ∑ n ∈ P.support,
        conj (Q m) * P n * f ((m : ℝ) - (n : ℝ)) := h3


/-- The support of const_one is the singleton {0}. -/
lemma const_one_support : TrigPolyℤ.const_one.support = ({0} : Finset ℤ) := by
  unfold TrigPolyℤ.const_one
  simpa using (Finsupp.support_single_ne_zero (0 : ℤ) (one_ne_zero : (1 : ℂ) ≠ 0))

/-- INVARIANCE LEMMA 2 (corrected): Pairing with constant = applying Λ with flipped input.
    This is the identity you can actually get from Hermitian symmetry:
      ⟨P, 1⟩ = conj (Λ (f ∘ neg) P). -/
lemma double_sum_const_one
    (f : ℝ → ℂ) (hf : IsPositiveDefinite f) (P : TrigPolyℤ) :
    ∑ m ∈ P.support, ∑ n ∈ TrigPolyℤ.const_one.support,
      conj (P m) * TrigPolyℤ.const_one n * f (m - n) =
    conj (ΛTrigℤ (fun x => f (-x)) P) := by
  classical
  -- Step 1: const_one has support {0}
  rw [const_one_support]
  -- Step 2: collapse the inner sum over {0}
  simp only [Finset.sum_singleton]
  -- Step 3: const_one(0) = 1
  unfold TrigPolyℤ.const_one
  simp
  -- Now LHS is: ∑ m∈P.support, conj(P m) * f (m:ℝ)
  -- Helper: conj (f (-x)) = f x (from hf.1)
  have hconj : ∀ x : ℝ, conj (f (-x)) = f x := by
    intro x
    -- hf.1 x : f (-x) = conj (f x)
    -- conj both sides
    simpa using congrArg conj (hf.1 x)
  -- Expand the RHS conjugate of Λ and rewrite using hconj
  unfold ΛTrigℤ
  -- push `conj` through the finite sum
  simp [map_sum, mul_assoc, hconj]
  -- Your simp got you down to the `1 0` nuisance; now kill it *without* cancellation lemmas.
  refine Finset.sum_congr rfl ?_
  intro x hx
  -- Replace the mysterious `1 0` with what it really is: the coefficient of const_one at 0
  change (starRingEnd ℂ) (P x) * (TrigPolyℤ.const_one (0 : ℤ) * f (x : ℝ))
      = (starRingEnd ℂ) (P x) * f (x : ℝ)
  -- Rewrite the inner coefficient first, WITHOUT touching the outer multiplier.
  have hinner : TrigPolyℤ.const_one (0 : ℤ) * f (x : ℝ) = f (x : ℝ) := by
    unfold TrigPolyℤ.const_one
    -- Now goal is: (Finsupp.single 0 1) 0 * f ↑x = f ↑x
    -- Rewrite (Finsupp.single 0 1) 0 = 1, then one_mul.
    rw [Finsupp.single_eq_same]
    simpa
  -- Now rewrite using hinner; no cancellation, no disjunction.
  simpa [hinner, mul_assoc]


/-- INVARIANCE LEMMA 3: Expansion of |P + tQ|² for real t. -/
lemma double_sum_sum_expansion (f : ℝ → ℂ) (hf : IsPositiveDefinite f)
    (P Q : TrigPolyℤ) (t : ℝ) :
    (∑ m ∈ (P + t • Q).support, ∑ n ∈ (P + t • Q).support,
        conj ((P + t • Q) m) * (P + t • Q) n * f (m - n)).re =
      (∑ m ∈ P.support, ∑ n ∈ P.support, conj (P m) * P n * f (m - n)).re +
      2 * t * (∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * Q n * f (m - n)).re +
      t ^ 2 * (∑ m ∈ Q.support, ∑ n ∈ Q.support, conj (Q m) * Q n * f (m - n)).re := by
  classical
  -- Work over the union support so we can expand algebraically without fiddling the binder later.
  let S : Finset ℤ := P.support ∪ Q.support
  have h_supp : (P + t • Q).support ⊆ S := by
    intro k hk
    simp only [S, Finset.mem_union]
    by_contra hnot
    push_neg at hnot
    have hP : P k = 0 := Finsupp.notMem_support_iff.mp hnot.1
    have hQ : Q k = 0 := Finsupp.notMem_support_iff.mp hnot.2
    have : (P + t • Q) k = 0 := by
      simp only [Finsupp.add_apply, Finsupp.smul_apply, hP, hQ, smul_zero, add_zero]
    exact Finsupp.notMem_support_iff.mpr this hk
  -- Replace the sum over (P+tQ).support by sum over S (extra terms are zero).
  have h_expand :
      ∑ m ∈ (P + t • Q).support, ∑ n ∈ (P + t • Q).support,
          conj ((P + t • Q) m) * (P + t • Q) n * f (m - n)
        =
      ∑ m ∈ S, ∑ n ∈ S,
          conj ((P + t • Q) m) * (P + t • Q) n * f (m - n) := by
    let F : ℤ → ℤ → ℂ :=
      fun m n => conj ((P + t • Q) m) * (P + t • Q) n * f (m - n)
    -- Extend inner sum: support → S
    have h_inner :
        ∀ m : ℤ,
          (∑ n ∈ (P + t • Q).support, F m n) = ∑ n ∈ S, F m n := by
      intro m
      refine Finset.sum_subset h_supp ?_
      intro n hnS hnnot_supp
      have hn0 : (P + t • Q) n = 0 := Finsupp.notMem_support_iff.mp hnnot_supp
      have hn0' : P n + (t : ℂ) * Q n = 0 := by
      -- expand (P + t•Q) n
        simpa [Finsupp.add_apply, Finsupp.smul_apply] using hn0
      -- kills the whole integrand
      dsimp [F]
      -- now the goal contains P n + t*Q n, so rw hits
      rw [hn0']
      simp [mul_assoc]
    -- Extend outer sum: support → S
    have h_outer :
        (∑ m ∈ (P + t • Q).support, ∑ n ∈ S, F m n) =
          ∑ m ∈ S, ∑ n ∈ S, F m n := by
      refine Finset.sum_subset h_supp ?_
      intro m hmS hmnot_supp
      have hm0 : (P + t • Q) m = 0 := Finsupp.notMem_support_iff.mp hmnot_supp
      have hm0' : P m + (t : ℂ) * Q m = 0 := by
        simpa [Finsupp.add_apply, Finsupp.smul_apply] using hm0
      -- inner sum is identically 0 if m outside support
      have : (∑ n ∈ S, F m n) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro n hn
        dsimp [F]
        rw [hm0']
        simp [mul_assoc]
      simpa [this]
    -- Assemble (and RETURN it!)
    -- First: replace inner sum for each m
    -- Then: extend outer sum
    calc
      ∑ m ∈ (P + t • Q).support, ∑ n ∈ (P + t • Q).support, F m n
          =
      ∑ m ∈ (P + t • Q).support, ∑ n ∈ S, F m n := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        simpa using (h_inner m)
      _ =
      ∑ m ∈ S, ∑ n ∈ S, F m n := by
        simpa using h_outer
  -- Now do the algebra expansion INSIDE the complex sum (no `.re` yet).
  have h_product :
      ∀ m n : ℤ,
        conj ((P + t • Q) m) * (P + t • Q) n
          =
        conj (P m) * P n
          + (t : ℂ) * (conj (P m) * Q n)
          + (t : ℂ) * (conj (Q m) * P n)
          + (t : ℂ)^2 * (conj (Q m) * Q n) := by
    intro m n
    simp [Finsupp.add_apply, Finsupp.smul_apply, mul_add, add_mul, add_assoc, add_left_comm,
      add_comm, mul_assoc, mul_left_comm, mul_comm, map_add, map_mul, conj_ofReal]
    -- After simp, `ring` handles the distributivity.
    ring
  have h_productF :
      ∀ m n : ℤ,
        conj ((P + t • Q) m) * (P + t • Q) n * f (m - n)
          =
        (conj (P m) * P n * f (m - n))
          + (t : ℂ) * (conj (P m) * Q n * f (m - n))
          + (t : ℂ) * (conj (Q m) * P n * f (m - n))
          + (t : ℂ)^2 * (conj (Q m) * Q n * f (m - n)) := by
    intro m n
    simp [Finsupp.add_apply, Finsupp.smul_apply, mul_add, add_mul,
      mul_assoc, mul_left_comm, mul_comm, map_add, map_mul, conj_ofReal]
    ring_nf
  -- Define the four "big blocks" (still over S×S).
  have h_sum_over_S :
      ∑ m ∈ S, ∑ n ∈ S,
          conj ((P + t • Q) m) * (P + t • Q) n * f (m - n)
        =
      (∑ m ∈ S, ∑ n ∈ S, conj (P m) * P n * f (m - n))
        + (t : ℂ) * (∑ m ∈ S, ∑ n ∈ S, conj (P m) * Q n * f (m - n))
        + (t : ℂ) * (∑ m ∈ S, ∑ n ∈ S, conj (Q m) * P n * f (m - n))
        + (t : ℂ)^2 * (∑ m ∈ S, ∑ n ∈ S, conj (Q m) * Q n * f (m - n)) := by
    calc
      ∑ m ∈ S, ∑ n ∈ S,
          conj ((P + t • Q) m) * (P + t • Q) n * f (m - n)
          =
      ∑ m ∈ S, ∑ n ∈ S,
        ((conj (P m) * P n * f (m - n))
          + (t : ℂ) * (conj (P m) * Q n * f (m - n))
          + (t : ℂ) * (conj (Q m) * P n * f (m - n))
          + (t : ℂ)^2 * (conj (Q m) * Q n * f (m - n))) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        refine Finset.sum_congr rfl ?_
        intro n hn
        simpa using (h_productF m n)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
  -- Now restrict each block from S×S down to the "true" supports.
  have hPP :
      (∑ m ∈ S, ∑ n ∈ S, conj (P m) * P n * f (m - n))
        =
      (∑ m ∈ P.support, ∑ n ∈ P.support, conj (P m) * P n * f (m - n)) := by
    -- same "sum_subset + vanish" pattern as you wrote, but at ℂ-level
    trans (∑ m ∈ P.support, ∑ n ∈ S, conj (P m) * P n * f (m - n))
    · symm
      refine Finset.sum_subset (Finset.subset_union_left (s₁ := P.support) (s₂ := Q.support)) ?_
      intro m hmS hmnot
      have hPm : P m = 0 := Finsupp.notMem_support_iff.mp hmnot
      simp [hPm]
    · refine Finset.sum_congr rfl ?_
      intro m hm
      symm
      refine Finset.sum_subset (Finset.subset_union_left (s₁ := P.support) (s₂ := Q.support)) ?_
      intro n hnS hnnot
      have hPn : P n = 0 := Finsupp.notMem_support_iff.mp hnnot
      simp [hPn]
  have hPQ :
      (∑ m ∈ S, ∑ n ∈ S, conj (P m) * Q n * f (m - n))
        =
      (∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * Q n * f (m - n)) := by
    trans (∑ m ∈ P.support, ∑ n ∈ S, conj (P m) * Q n * f (m - n))
    · symm
      refine Finset.sum_subset (Finset.subset_union_left (s₁ := P.support) (s₂ := Q.support)) ?_
      intro m hmS hmnot
      have hPm : P m = 0 := Finsupp.notMem_support_iff.mp hmnot
      simp [hPm]
    · refine Finset.sum_congr rfl ?_
      intro m hm
      symm
      refine Finset.sum_subset (Finset.subset_union_right (s₁ := P.support) (s₂ := Q.support)) ?_
      intro n hnS hnnot
      have hQn : Q n = 0 := Finsupp.notMem_support_iff.mp hnnot
      simp [hQn]
  have hQP :
      (∑ m ∈ S, ∑ n ∈ S, conj (Q m) * P n * f (m - n))
        =
      (∑ m ∈ Q.support, ∑ n ∈ P.support, conj (Q m) * P n * f (m - n)) := by
    trans (∑ m ∈ Q.support, ∑ n ∈ S, conj (Q m) * P n * f (m - n))
    · symm
      refine Finset.sum_subset (Finset.subset_union_right (s₁ := P.support) (s₂ := Q.support)) ?_
      intro m hmS hmnot
      have hQm : Q m = 0 := Finsupp.notMem_support_iff.mp hmnot
      simp [hQm]
    · refine Finset.sum_congr rfl ?_
      intro m hm
      symm
      refine Finset.sum_subset (Finset.subset_union_left (s₁ := P.support) (s₂ := Q.support)) ?_
      intro n hnS hnnot
      have hPn : P n = 0 := Finsupp.notMem_support_iff.mp hnnot
      simp [hPn]
  have hQQ :
      (∑ m ∈ S, ∑ n ∈ S, conj (Q m) * Q n * f (m - n))
        =
      (∑ m ∈ Q.support, ∑ n ∈ Q.support, conj (Q m) * Q n * f (m - n)) := by
    trans (∑ m ∈ Q.support, ∑ n ∈ S, conj (Q m) * Q n * f (m - n))
    · symm
      refine Finset.sum_subset (Finset.subset_union_right (s₁ := P.support) (s₂ := Q.support)) ?_
      intro m hmS hmnot
      have hQm : Q m = 0 := Finsupp.notMem_support_iff.mp hmnot
      simp [hQm]
    · refine Finset.sum_congr rfl ?_
      intro m hm
      symm
      refine Finset.sum_subset (Finset.subset_union_right (s₁ := P.support) (s₂ := Q.support)) ?_
      intro n hnS hnnot
      have hQn : Q n = 0 := Finsupp.notMem_support_iff.mp hnnot
      simp [hQn]
  -- Hermitian symmetry gives: Re(QP) = Re(PQ)
  have h_mixed_re :
      (∑ m ∈ Q.support, ∑ n ∈ P.support, conj (Q m) * P n * f (m - n)).re
        =
      (∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * Q n * f (m - n)).re := by
    have hsymm := double_sum_conj_symm (f := f) hf P Q
    have this := congrArg Complex.re hsymm
    rw [Complex.conj_re] at this
    exact this.symm
  -- First extend the sum from (P + t • Q).support to S
  have h_extend : (∑ m ∈ (P + t • Q).support, ∑ n ∈ (P + t • Q).support,
            conj ((P + t • Q) m) * (P + t • Q) n * f (m - n))
        =
      (∑ m ∈ S, ∑ n ∈ S,
            conj ((P + t • Q) m) * (P + t • Q) n * f (m - n)) := by
    rw [h_expand]
  -- Then expand into the four blocks
  have h_expand_blocks : (∑ m ∈ S, ∑ n ∈ S,
            conj ((P + t • Q) m) * (P + t • Q) n * f (m - n))
        =
      (∑ m ∈ P.support, ∑ n ∈ P.support, conj (P m) * P n * f (m - n))
        + (t : ℂ) * (∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * Q n * f (m - n))
        + (t : ℂ) * (∑ m ∈ Q.support, ∑ n ∈ P.support, conj (Q m) * P n * f (m - n))
        + (t : ℂ)^2 * (∑ m ∈ Q.support, ∑ n ∈ Q.support, conj (Q m) * Q n * f (m - n)) := by
    simpa [hPP, hPQ, hQP, hQQ] using
      (h_sum_over_S.trans (by
      -- rewrite each block
        simp [hPP, hPQ, hQP, hQQ]))
  rw [h_extend, h_expand_blocks]
  -- take real parts
  -- name the three blocks to keep simp from going feral
  set PP : ℂ := ∑ m ∈ P.support, ∑ n ∈ P.support, conj (P m) * P n * f (m - n)
  set PQ : ℂ := ∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * Q n * f (m - n)
  set QP : ℂ := ∑ m ∈ Q.support, ∑ n ∈ P.support, conj (Q m) * P n * f (m - n)
  set QQ : ℂ := ∑ m ∈ Q.support, ∑ n ∈ Q.support, conj (Q m) * Q n * f (m - n)
  -- Use linearity of `.re` and the fact `t` is real:
  have ht_re : ((t : ℂ).re) = t := by simp
  have ht_im : ((t : ℂ).im) = 0 := by simp
  -- Key: DON'T expand PP/PQ/QP/QQ, only simplify scalar complex algebra
  -- The goal is (PP + (t:ℂ)*PQ + (t:ℂ)*QP + (t:ℂ)^2*QQ).re = PP.re + 2*t*PQ.re + t^2*QQ.re
  -- Use re(a+b)=re a + re b, re((t:ℂ)*z)=t*z.re, re((t:ℂ)^2*z)=t^2*z.re
  simp [Complex.add_re, Complex.mul_re, ht_re, ht_im, pow_two, h_mixed_re]
  ring

/-- Cauchy-Schwarz for Q = const_one. -/
-- THE GAUGE STRUCTURE: Define the sesquilinear form ⟨P, Q⟩_f
-- This is invariant under opposite U(1) phase rotations: ⟨e^{-iθ}P, e^{iθ}Q⟩ = ⟨P, Q⟩
noncomputable def sesquilinear_form (f : ℝ → ℂ) (P Q : TrigPolyℤ) : ℂ :=
  ∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * Q n * f (m - n)

/-- U(1) CHARACTER ACTION on trigonometric polynomials. -/
noncomputable def u_action (u : ℂ) (hu : u ≠ 0) (P : TrigPolyℤ) : TrigPolyℤ where
  toFun n := u ^ (n : ℤ) * P n
  support := P.support
  mem_support_toFun := by
    intro n
    -- Key: u^n ≠ 0 when u ≠ 0 (zpow of nonzero is nonzero)
    have hu_zpow : u ^ (n : ℤ) ≠ 0 := zpow_ne_zero n hu
    simp only [Finsupp.mem_support_iff, ne_eq, mul_eq_zero, hu_zpow, false_or]

/-- The sesquilinear form is conjugate-linear in the first argument. -/
lemma sesquilinear_form_conj_linear_fst (f : ℝ → ℂ) (P Q : TrigPolyℤ) (c : ℂ) :
    sesquilinear_form f (c • P) Q = conj c * sesquilinear_form f P Q := by
  unfold sesquilinear_form
  -- Key: (c • P).support ⊆ P.support, and terms vanish outside P.support
  calc ∑ m ∈ (c • P).support, ∑ n ∈ Q.support, conj ((c • P) m) * Q n * f (m - n)
      = ∑ m ∈ P.support, ∑ n ∈ Q.support, conj ((c • P) m) * Q n * f (m - n) := by
        refine Finset.sum_subset Finsupp.support_smul ?_
        intro m hm_P hm_cP
        have : (c • P) m = 0 := Finsupp.notMem_support_iff.mp hm_cP
        simp [this]
    _ = ∑ m ∈ P.support, ∑ n ∈ Q.support, conj (c * P m) * Q n * f (m - n) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        refine Finset.sum_congr rfl ?_
        intro n hn
        simp only [Finsupp.smul_apply, smul_eq_mul]
    _ = ∑ m ∈ P.support, ∑ n ∈ Q.support, (conj c * conj (P m)) * Q n * f (m - n) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        refine Finset.sum_congr rfl ?_
        intro n hn
        simp only [map_mul]
    _ = conj c * ∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * Q n * f (m - n) := by
        simp only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

-- Sesquilinearity: The form is linear in second argument
lemma sesquilinear_form_linear_snd (f : ℝ → ℂ) (P Q : TrigPolyℤ) (c : ℂ) :
    sesquilinear_form f P (c • Q) = c * sesquilinear_form f P Q := by
  unfold sesquilinear_form
  -- Same pattern as conjugate-linear case, but NO conjugation on c
  calc ∑ m ∈ P.support, ∑ n ∈ (c • Q).support, conj (P m) * (c • Q) n * f (m - n)
      = ∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * (c • Q) n * f (m - n) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        refine Finset.sum_subset Finsupp.support_smul ?_
        intro n hn_Q hn_cQ
        have : (c • Q) n = 0 := Finsupp.notMem_support_iff.mp hn_cQ
        simp [this]
    _ = ∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * (c * Q n) * f (m - n) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        refine Finset.sum_congr rfl ?_
        intro n hn
        simp only [Finsupp.smul_apply, smul_eq_mul]
    _ = c * ∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * Q n * f (m - n) := by
        simp only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Phase insertion under U(1) action on the sesquilinear form. -/
lemma sesquilinear_form_u_action_insert_phase (f : ℝ → ℂ) (P : TrigPolyℤ) (u : ℂ) (hu : ‖u‖ = 1) :
    sesquilinear_form f (u_action u (norm_ne_zero_iff.mp (hu.symm ▸ one_ne_zero)) P)
      (u_action u (norm_ne_zero_iff.mp (hu.symm ▸ one_ne_zero)) P) =
    ∑ m ∈ P.support, ∑ n ∈ P.support,
      u ^ ((n : ℤ) - (m : ℤ)) * conj (P m) * P n * f (m - n) := by
  set hu_ne := norm_ne_zero_iff.mp (hu.symm ▸ one_ne_zero) with hu_ne_def
  unfold sesquilinear_form u_action
  simp only [Finsupp.coe_mk]
  -- Key fact: when ‖u‖ = 1, conj(u^k) = u^{-k}
  have h_conj_zpow : ∀ k : ℤ, (starRingEnd ℂ) (u ^ k) = u ^ (-k) := by
    intro k
    -- First show conj(u) = u⁻¹ when ‖u‖ = 1
    have h_inv : (starRingEnd ℂ) u = u⁻¹ := by
      -- Since ‖u‖ = 1, we have conj(u) * u = 1, so conj(u) = u⁻¹
      have h_norm : (starRingEnd ℂ) u * u = 1 := by
        rw [mul_comm]
        calc u * (starRingEnd ℂ) u
            = Complex.normSq u := Complex.mul_conj u
          _ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by exact_mod_cast Complex.normSq_eq_norm_sq u
          _ = ((1 : ℝ) : ℂ) := by simp [hu]
          _ = (1 : ℂ) := by norm_cast
      have conj_ne : (starRingEnd ℂ) u ≠ 0
       := map_ne_zero_iff (starRingEnd ℂ) (RingHom.injective _) |>.mpr hu_ne
      have h_temp := (mul_eq_one_iff_inv_eq₀ conj_ne).mp h_norm
      -- h_temp : ((starRingEnd ℂ) u)⁻¹ = u, so (starRingEnd ℂ) u = u⁻¹
      exact inv_eq_iff_eq_inv.mp h_temp
    -- Now prove the zpow version by cases
    cases k with
    | ofNat n =>
      calc (starRingEnd ℂ) (u ^ (n : ℤ))
          = (starRingEnd ℂ) (u ^ n) := by simp [zpow_natCast]
        _ = ((starRingEnd ℂ) u) ^ n := by exact map_pow (starRingEnd ℂ) u n
        _ = (u⁻¹) ^ n := by rw [h_inv]
        _ = (u ^ n)⁻¹ := inv_pow u n
        _ = u ^ (-(n : ℤ)) := by simp [zpow_neg, zpow_natCast]
    | negSucc n =>
      calc (starRingEnd ℂ) (u ^ Int.negSucc n)
          = (starRingEnd ℂ) ((u ^ (n + 1 : ℕ))⁻¹) := by
            simp [zpow_negSucc]
        _ = ((starRingEnd ℂ) (u ^ (n + 1 : ℕ)))⁻¹ :=
            map_inv₀ (starRingEnd ℂ) (u ^ (n + 1 : ℕ))
        _ = (((starRingEnd ℂ) u) ^ (n + 1 : ℕ))⁻¹ := by
            simp [map_pow]
        _ = ((u⁻¹) ^ (n + 1 : ℕ))⁻¹ := by
            simp [h_inv]
        _ = u ^ (n + 1 : ℕ) := by
            simp [inv_pow, inv_inv]
        _ = u ^ ((n + 1 : ℕ) : ℤ) := by
            exact (zpow_natCast u (n + 1)).symm
        _ = u ^ (- Int.negSucc n) := by
            simp [Int.neg_negSucc]
  -- Expand and simplify the integrand pointwise
  calc ∑ m ∈ P.support, ∑ n ∈ P.support,
          conj (u ^ (m : ℤ) * P m) * (u ^ (n : ℤ) * P n) * f (m - n)
      = ∑ m ∈ P.support, ∑ n ∈ P.support,
          (conj (u ^ (m : ℤ)) * conj (P m)) * (u ^ (n : ℤ) * P n) * f (m - n) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        refine Finset.sum_congr rfl ?_
        intro n hn
        rw [map_mul]
    _ = ∑ m ∈ P.support, ∑ n ∈ P.support,
          u ^ (-(m : ℤ)) * u ^ (n : ℤ) * conj (P m) * P n * f (m - n) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        refine Finset.sum_congr rfl ?_
        intro n hn
        rw [h_conj_zpow]
        ring
    _ = ∑ m ∈ P.support, ∑ n ∈ P.support,
          u ^ ((n : ℤ) - (m : ℤ)) * conj (P m) * P n * f (m - n) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        refine Finset.sum_congr rfl ?_
        intro n hn
      -- Combine u^(-m) * u^n = u^(n-m) using zpow_add₀
        have hphase : u ^ (-(m : ℤ)) * u ^ (n : ℤ) = u ^ ((n : ℤ) - (m : ℤ)) := by
          have h_add := zpow_add₀ hu_ne (-(m : ℤ)) (n : ℤ)
          calc u ^ (-(m : ℤ)) * u ^ (n : ℤ)
              = u ^ ((-(m : ℤ)) + (n : ℤ)) := h_add.symm
            _ = u ^ ((n : ℤ) + (-(m : ℤ))) := by rw [add_comm]
            _ = u ^ ((n : ℤ) - (m : ℤ)) := by simp [sub_eq_add_neg]
      -- Also need: (u^m)⁻¹ = u^(-m)
        have hm_inv : (u ^ (m : ℤ))⁻¹ = u ^ (-(m : ℤ)) := by simp [zpow_neg]
      -- Now do the algebra
        calc u ^ (-(m : ℤ)) * u ^ (n : ℤ) * (starRingEnd ℂ) (P m) * P n * f (↑m - ↑n)
            = (u ^ (-(m : ℤ)) * u ^ (n : ℤ)) * ((starRingEnd ℂ) (P m) * P n * f (↑m - ↑n)) := by
              ring
          _ = u ^ ((n : ℤ) - (m : ℤ)) * ((starRingEnd ℂ) (P m) * P n * f (↑m - ↑n)) := by
              rw [hphase]
          _ = u ^ ((n : ℤ) - (m : ℤ)) * (starRingEnd ℂ) (P m) * P n * f (↑m - ↑n) := by
              ring
lemma sesquilinear_form_conj (f : ℝ → ℂ) (hf : IsPositiveDefinite f) (P Q : TrigPolyℤ) :
    sesquilinear_form f Q P = conj (sesquilinear_form f P Q) := by
  unfold sesquilinear_form
  -- Swap indices m ↔ n and use Hermitian symmetry f(-x) = conj(f(x))
  calc ∑ m ∈ Q.support, ∑ n ∈ P.support, conj (Q m) * P n * f (m - n)
      = ∑ n ∈ P.support, ∑ m ∈ Q.support, conj (Q m) * P n * f (m - n) := by
        rw [Finset.sum_comm]
    _ = ∑ n ∈ P.support, ∑ m ∈ Q.support, conj (Q m) * P n * f (-(n - m)) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        refine Finset.sum_congr rfl ?_
        intro m hm
        congr 1
        ring_nf
    _ = ∑ n ∈ P.support, ∑ m ∈ Q.support, conj (Q m) * P n * conj (f (n - m)) := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [hf.1]  -- f(-x) = conj(f(x))
    _ = conj (∑ n ∈ P.support, ∑ m ∈ Q.support, conj (P n) * Q m * f (n - m)) := by
        simp only [map_sum, map_mul, conj_conj]
        refine Finset.sum_congr rfl ?_
        intro n hn
        refine Finset.sum_congr rfl ?_
        intro m hm
        ring

-- Additivity in the second argument
lemma sesquilinear_form_add_right (f : ℝ → ℂ) (P Q R : TrigPolyℤ) :
    sesquilinear_form f P (Q + R) =
      sesquilinear_form f P Q + sesquilinear_form f P R := by
  classical
  unfold sesquilinear_form
  let S : Finset ℤ := Q.support ∪ R.support
  have h_subset : (Q + R).support ⊆ S := by
    intro n hn
    by_contra h
    have h' : n ∉ Q.support ∧ n ∉ R.support := by
      simpa [S, Finset.mem_union] using h
    have hQ : Q n = 0 := Finsupp.notMem_support_iff.mp h'.1
    have hR : R n = 0 := Finsupp.notMem_support_iff.mp h'.2
    have : (Q + R) n = 0 := by simp [Finsupp.add_apply, hQ, hR]
    exact (Finsupp.mem_support_iff.mp hn) this
  -- Upgrade inner sum from (Q+R).support to S
  have h_inner :
      (∑ m ∈ P.support, ∑ n ∈ (Q + R).support, conj (P m) * (Q + R) n * f (m - n)) =
      (∑ m ∈ P.support, ∑ n ∈ S,           conj (P m) * (Q + R) n * f (m - n)) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    -- use sum_subset with s=(Q+R).support ⊆ S, so we get sum over support = sum over S
    apply Finset.sum_subset h_subset
    intro n hnS hnnot
    have h0 : (Q + R) n = 0 := Finsupp.notMem_support_iff.mp hnnot
    simp [h0]
  -- Now expand (Q+R) n and split sums
  calc
    (∑ m ∈ P.support, ∑ n ∈ (Q + R).support, conj (P m) * (Q + R) n * f (m - n))
        =
      (∑ m ∈ P.support, ∑ n ∈ S, conj (P m) * (Q + R) n * f (m - n)) := h_inner
    _ =
      (∑ m ∈ P.support, ∑ n ∈ S,
          (conj (P m) * Q n * f (m - n) + conj (P m) * R n * f (m - n))) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        refine Finset.sum_congr rfl ?_
        intro n hn
        simp [Finsupp.add_apply, mul_add, add_mul, mul_assoc]
    _ =
      (∑ m ∈ P.support,
          ((∑ n ∈ S, conj (P m) * Q n * f (m - n)) +
           (∑ n ∈ S, conj (P m) * R n * f (m - n)))) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        exact Finset.sum_add_distrib
    _ =
      (∑ m ∈ P.support, ∑ n ∈ S, conj (P m) * Q n * f (m - n)) +
      (∑ m ∈ P.support, ∑ n ∈ S, conj (P m) * R n * f (m - n)) := by
        simpa [Finset.sum_add_distrib]
    _ =
      (∑ m ∈ P.support, ∑ n ∈ Q.support, conj (P m) * Q n * f (m - n)) +
      (∑ m ∈ P.support, ∑ n ∈ R.support, conj (P m) * R n * f (m - n)) := by
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro m hm
          -- Here: want sum over
          -- S = sum over Q.support, so use sum_subset on Q.support ⊆ S, then symm
          symm
          apply Finset.sum_subset (by simpa [S] using Finset.subset_union_left : Q.support ⊆ S)
          intro n hnS hnnot
          have h0 : Q n = 0 := Finsupp.notMem_support_iff.mp hnnot
          simp [h0]
        · refine Finset.sum_congr rfl ?_
          intro m hm
          symm
          apply Finset.sum_subset (by simpa [S] using Finset.subset_union_right : R.support ⊆ S)
          intro n hnS hnnot
          have h0 : R n = 0 := Finsupp.notMem_support_iff.mp hnnot
          simp [h0]

-- Additivity in the first argument (conjugate-linear)
lemma sesquilinear_form_add_left (f : ℝ → ℂ) (P Q R : TrigPolyℤ) :
    sesquilinear_form f (P + Q) R =
      sesquilinear_form f P R + sesquilinear_form f Q R := by
  classical
  unfold sesquilinear_form
  let S : Finset ℤ := P.support ∪ Q.support
  have h_subset : (P + Q).support ⊆ S := by
    intro m hm
    by_contra h
    have h' : m ∉ P.support ∧ m ∉ Q.support := by
      simpa [S, Finset.mem_union] using h
    have hP : P m = 0 := Finsupp.notMem_support_iff.mp h'.1
    have hQ : Q m = 0 := Finsupp.notMem_support_iff.mp h'.2
    have : (P + Q) m = 0 := by simp [Finsupp.add_apply, hP, hQ]
    exact (Finsupp.mem_support_iff.mp hm) this
  calc
    (∑ m ∈ (P + Q).support, ∑ n ∈ R.support, conj ((P + Q) m) * R n * f (m - n))
        =
      (∑ m ∈ S, ∑ n ∈ R.support, conj ((P + Q) m) * R n * f (m - n)) := by
      -- Upgrade outer sum from (P+Q).support to S
        refine Finset.sum_subset h_subset ?_
        intro m hmS hmnot
        have h0 : (P + Q) m = 0 := Finsupp.notMem_support_iff.mp hmnot
        simp [h0]
    _ =
      (∑ m ∈ S, ∑ n ∈ R.support,
          (conj (P m) * R n * f (m - n) + conj (Q m) * R n * f (m - n))) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        refine Finset.sum_congr rfl ?_
        intro n hn
      -- conj((P+Q)m)=conj(Pm+Qm)=conj(Pm)+conj(Qm)
        simp [Finsupp.add_apply, map_add, add_mul, mul_add, mul_assoc]
    _ =
      (∑ m ∈ S,
          ((∑ n ∈ R.support, conj (P m) * R n * f (m - n)) +
           (∑ n ∈ R.support, conj (Q m) * R n * f (m - n)))) := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        exact Finset.sum_add_distrib
    _ =
      (∑ m ∈ S, ∑ n ∈ R.support, conj (P m) * R n * f (m - n)) +
      (∑ m ∈ S, ∑ n ∈ R.support, conj (Q m) * R n * f (m - n)) := by
        simpa [Finset.sum_add_distrib]
    _ =
      (∑ m ∈ P.support, ∑ n ∈ R.support, conj (P m) * R n * f (m - n)) +
      (∑ m ∈ Q.support, ∑ n ∈ R.support, conj (Q m) * R n * f (m - n)) := by
        congr 1
        · -- sum over S equals sum over P.support
          symm
          apply Finset.sum_subset (by simpa [S] using Finset.subset_union_left : P.support ⊆ S)
          intro m hmS hmnot
          have h0 : P m = 0 := Finsupp.notMem_support_iff.mp hmnot
          simp [h0]
        · symm
          apply Finset.sum_subset (by simpa [S] using Finset.subset_union_right : Q.support ⊆ S)
          intro m hmS hmnot
          have h0 : Q m = 0 := Finsupp.notMem_support_iff.mp hmnot
          simp [h0]

-- Expansion of the sesquilinear form for P + zQ (z ∈ ℂ is the gauge parameter)
lemma sesquilinear_form_expansion (f : ℝ → ℂ) (P Q : TrigPolyℤ) (z : ℂ) :
    sesquilinear_form f (P + z • Q) (P + z • Q) =
    sesquilinear_form f P P +
    z * sesquilinear_form f P Q +
    conj z * sesquilinear_form f Q P +
    Complex.normSq z * sesquilinear_form f Q Q := by
  classical
  -- Use bilinearity: ⟨P + zQ, P + zQ⟩ expands into 4 terms
  calc sesquilinear_form f (P + z • Q) (P + z • Q)
      = sesquilinear_form f (P + z • Q) P + sesquilinear_form f (P + z • Q) (z • Q) := by
      -- additivity in the second argument
        exact sesquilinear_form_add_right (f := f) (P := (P + z • Q)) (Q := P) (R := (z • Q))
    _ = (sesquilinear_form f P P + sesquilinear_form f (z • Q) P) +
        (sesquilinear_form f P (z • Q) + sesquilinear_form f (z • Q) (z • Q)) := by
      -- additivity in the first argument, applied to each summand
        rw [sesquilinear_form_add_left (f := f) (P := P) (Q := (z • Q)) (R := P)]
        rw [sesquilinear_form_add_left (f := f) (P := P) (Q := (z • Q)) (R := (z • Q))]
    _ = sesquilinear_form f P P +
        (conj z * sesquilinear_form f Q P) +
        (z * sesquilinear_form f P Q) +
        (conj z * z * sesquilinear_form f Q Q) := by
        rw [sesquilinear_form_conj_linear_fst, sesquilinear_form_linear_snd,
            sesquilinear_form_conj_linear_fst, sesquilinear_form_linear_snd]
        ring
    _ = _ := by
        rw [← Complex.normSq_eq_conj_mul_self]
        ring
/-
A clean, robust “affine nonneg ⇒ slope = 0” lemma.
No fragile `field_simp` goals about `a + (-a ± b)`.

Key trick: pick t = -(a+1)/b (works for either sign of b as long as b ≠ 0),
then the affine expression becomes -1.
-/
lemma linear_nonneg_all_real {a b : ℝ} (h : ∀ t : ℝ, 0 ≤ a + b * t) : b = 0 := by
  by_contra hb0
  have hb : b ≠ 0 := hb0
  -- pick t in Lean's preferred normal form
  set t : ℝ := (-1 - a) / b
  have hbad : 0 ≤ a + b * t := h t
  have hab : a + b * t = (-1 : ℝ) := by
    -- expand t and cancel b
    subst t
    field_simp [hb]
    ring
  have : (0 : ℝ) ≤ (-1 : ℝ) := by
    -- rewrite the inequality using hab
    simpa [hab] using hbad
  linarith


/-- COMPLEX CAUCHY–SCHWARZ via gauge optimization (cleaned). -/
lemma cauchy_schwarz_complex (f : ℝ → ℂ) (hf : IsPositiveDefinite f) (P Q : TrigPolyℤ) :
    Complex.normSq (sesquilinear_form f P Q) ≤
    (sesquilinear_form f P P).re * (sesquilinear_form f Q Q).re := by
  classical
  -- global positivity you already have
  have h_pos (R : TrigPolyℤ) : 0 ≤ (sesquilinear_form f R R).re := by
    simpa [sesquilinear_form] using ΛTrigℤ_nonneg_on_normSq f hf R
  -- abbreviations
  set PP : ℂ := sesquilinear_form f P P
  set PQ : ℂ := sesquilinear_form f P Q
  set QP : ℂ := sesquilinear_form f Q P
  set QQ : ℂ := sesquilinear_form f Q Q
  have hQP_conj : QP = conj PQ := by
    simpa [QP, PQ] using (sesquilinear_form_conj f hf P Q)
  have hQQ_real : conj QQ = QQ := by
    -- hermitian on (Q,Q)
    simpa [QQ] using (sesquilinear_form_conj f hf Q Q).symm
  have hQQ_im : QQ.im = 0 := by
    exact Complex.conj_eq_iff_im.mp hQQ_real
  have hQQ_eq_ofReal : QQ = (QQ.re : ℂ) := by
    apply Complex.ext <;> simp [hQQ_im]
  have hQQ_nonneg : 0 ≤ QQ.re := by
    have : 0 ≤ (sesquilinear_form f Q Q).re := by
      simpa [sesquilinear_form] using ΛTrigℤ_nonneg_on_normSq f hf Q
    simpa [QQ] using this
  -- split degenerate vs nondegenerate ⟨Q,Q⟩
  by_cases hQQ0 : QQ = 0
  · -- Degenerate: show PQ = 0, then goal is 0 ≤ _ * 0.
    have hQQre0 : QQ.re = 0 := by simpa [hQQ0] using congrArg Complex.re hQQ0
    -- 1) real part of PQ is 0
    have hRe : PQ.re = 0 := by
      -- affine function in t because QQ = 0
      have hlin : ∀ t : ℝ,
          0 ≤ (sesquilinear_form f (P + (t:ℂ) • Q) (P + (t:ℂ) • Q)).re := by
        intro t; simpa using h_pos (P + (t:ℂ) • Q)
      have hexp : ∀ t : ℝ,
          (sesquilinear_form f (P + (t:ℂ) • Q) (P + (t:ℂ) • Q)).re
            = PP.re + t * (PQ.re * 2) := by
        intro t
        have h := congrArg Complex.re
          (sesquilinear_form_expansion (f := f) (P := P) (Q := Q) (z := (t:ℂ)))
      -- Step 1: kill QQ-term using hQQ0, and rewrite QP = conj PQ
      -- Step 2: convert (conj PQ).re to PQ.re
      -- Step 3: ring_nf to turn t*PQ.re + t*PQ.re into t*(PQ.re*2)
      -- IMPORTANT: simp ONLY, not simp.
        have h' : (sesquilinear_form f (P + (t:ℂ) • Q) (P + (t:ℂ) • Q)).re
            = PP.re + t * PQ.re + t * (conj PQ).re + t * t * QQ.re := by
          -- this keeps the exact structure from the expansion, but in your abbreviations
          simpa [PP, PQ, QP, QQ, hQP_conj] using h
      -- now finish
      -- QQ = 0 → QQ.re = 0, and (conj PQ).re = PQ.re
      -- then ring_nf
      -- (use simp only to avoid recursion)
        have : (sesquilinear_form f (P + (t:ℂ) • Q) (P + (t:ℂ) • Q)).re
            = PP.re + t * PQ.re + t * PQ.re := by
          -- QQ.re = 0 from QQ=0
          have hQQre : QQ.re = 0 := by simpa [hQQ0] using congrArg Complex.re hQQ0
          -- rewrite
          simpa [h', hQQre] using h'
      -- normalize t*PQ.re + t*PQ.re
      -- ring_nf is the cleanest here
        simpa [mul_assoc] using (by
          -- let ring_nf do the assoc/comm cleanup
          -- it works because everything is in ℝ here
          have := this
          -- ring_nf wants a goal, so:
          -- (PP.re + t*PQ.re + t*PQ.re) = (PP.re + t*(PQ.re*2))
          -- let it rip:
          ring_nf at this ⊢
          exact this)
      -- slope must be 0
      have hslope : (PQ.re * 2) = 0 :=
        linear_nonneg_all_real (a := PP.re) (b := PQ.re * 2) (by
          intro t
          have : 0 ≤ PP.re + t * (PQ.re * 2) := by
            rw [← hexp t]
            exact hlin t
          -- match their expected `0 ≤ a + b*t` normal form
          simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_comm, add_left_comm] using this)
      linarith [hslope]
    -- 2) imaginary part of PQ is 0 by repeating with Q' = I•Q
    have hIm : PQ.im = 0 := by
      set Q' : TrigPolyℤ := (Complex.I:ℂ) • Q
      have hQQ' : sesquilinear_form f Q' Q' = 0 := by
      -- expand ⟨iQ, iQ⟩ using conjugate-linearity in first slot + linearity in second
      -- and then use QQ=0
        have h1 :
            sesquilinear_form f ((Complex.I:ℂ) • Q) ((Complex.I:ℂ) • Q)
              = conj (Complex.I:ℂ) * sesquilinear_form f Q ((Complex.I:ℂ) • Q) := by
          -- your lemma name may differ; this matches what you used earlier in the previous draft:
          simpa using
          (sesquilinear_form_conj_linear_fst (f :=
           f) (P := Q) (Q := (Complex.I:ℂ) • Q) (c := (Complex.I:ℂ)))
        have h2 :
            sesquilinear_form f Q ((Complex.I:ℂ) • Q)
              = (Complex.I:ℂ) * sesquilinear_form f Q Q := by
          simpa using (sesquilinear_form_linear_snd (f := f) (P := Q) (Q := Q) (c := (Complex.I:ℂ)))
      -- combine and kill QQ
      -- note: QQ is your abbreviation for ⟨Q,Q⟩
      -- so rewrite with [QQ]
        calc
          sesquilinear_form f Q' Q'
              = sesquilinear_form f ((Complex.I:ℂ) • Q) ((Complex.I:ℂ) • Q) := by rfl
          _ = conj (Complex.I:ℂ) * ((Complex.I:ℂ) * sesquilinear_form f Q Q) := by
                simpa [h1, h2, mul_assoc]
          _ = conj (Complex.I:ℂ) * ((Complex.I:ℂ) * QQ) := by simp [QQ]
          _ = 0 := by
                -- conj I * I = 1, then QQ=0
                -- keep simp small:
                have : conj (Complex.I:ℂ) * (Complex.I:ℂ) = (1:ℂ) := by simp
                simpa [this, hQQ0, mul_assoc]
      -- Apply the “real-part-zero” argument to PQ' := ⟨P,Q'⟩
      have hRe' : (sesquilinear_form f P Q').re = 0 := by
      -- same affine slope trick with Q'
        have hlin' : ∀ t : ℝ,
            0 ≤ (sesquilinear_form f (P + (t:ℂ) • Q') (P + (t:ℂ) • Q')).re := by
          intro t; simpa using h_pos (P + (t:ℂ) • Q')
        have hQP' : sesquilinear_form f Q' P = conj (sesquilinear_form f P Q') := by
          -- same lemma you already have, just applied to (P,Q')
          simpa using (sesquilinear_form_conj f hf P Q')
        have hexp' : ∀ t : ℝ,
            (sesquilinear_form f (P + (t:ℂ) • Q') (P + (t:ℂ) • Q')).re
              = PP.re + t *
               (sesquilinear_form f P Q').re + t *
                (sesquilinear_form f Q' P).re + t * t * (sesquilinear_form f Q' Q').re := by
          intro t
          have h := congrArg Complex.re
            (sesquilinear_form_expansion (f := f) (P := P) (Q := Q') (z := (t:ℂ)))
          simpa [PP] using h
        have hexp'' : ∀ t : ℝ,
            (sesquilinear_form f (P + (t:ℂ) • Q') (P + (t:ℂ) • Q')).re
              = PP.re + t * ((sesquilinear_form f P Q').re * 2) := by
          intro t
          have h1 := hexp' t
          have hre : (sesquilinear_form f Q' P).re = (sesquilinear_form f P Q').re := by
            -- from hQP' and re(conj x)=re x
            simpa [hQP', Complex.conj_re]  -- or simp [hQP']
          have hQQ're : (sesquilinear_form f Q' Q').re = 0 := by
            simpa [hQQ'] using congrArg Complex.re hQQ'
          -- now rewrite and ring_nf
          -- (PP.re + t*A + t*A + t*t*0) = (PP.re + t*(A*2))
          -- do it in ℝ:
          -- use `simp [hre]` then `ring_nf`
          have : (sesquilinear_form f (P + (t:ℂ) • Q') (P + (t:ℂ) • Q')).re
              = PP.re + t * (sesquilinear_form f P Q').re + t * (sesquilinear_form f P Q').re := by
            simpa [hre, hQQ're] using h1
          -- normalize
          simpa using (by
            ring_nf at this ⊢
            exact this)
        have hslope' : ((sesquilinear_form f P Q').re * 2) = 0 :=
          linear_nonneg_all_real (a := PP.re) (b := (sesquilinear_form f P Q').re * 2) (by
            intro t
            have : 0 ≤ PP.re + t * ((sesquilinear_form f P Q').re * 2) := by
              rw [← hexp'' t]
              exact hlin' t
            simpa [mul_assoc, mul_left_comm,
             mul_comm, add_assoc, add_comm, add_left_comm] using this)
        linarith [hslope']
      -- relate ⟨P, iQ⟩ to i * ⟨P,Q⟩ and take real parts
      have hPiQ : sesquilinear_form f P Q' = (Complex.I:ℂ) * PQ := by
        simpa [Q', PQ] using
          (sesquilinear_form_linear_snd (f := f) (P := P) (Q := Q) (c := (Complex.I:ℂ)))
      -- re(I * (a+bi)) = -b
      have : (sesquilinear_form f P Q').re = -PQ.im := by
      -- `simp` knows I.re=0, I.im=1 and expands mul_re
        simp [hPiQ, Complex.mul_re]
      linarith
    have hPQ0 : PQ = 0 := by
      apply Complex.ext <;> simp [hRe, hIm]
    -- finish degenerate case
    -- RHS has factor QQ.re = 0, LHS is normSq 0 = 0
    simpa [PP, PQ, QQ, hPQ0, hQQre0]
  · -- Nondegenerate case: do the gauge choice z = -QP/QQ
    have hQQ_ne : QQ ≠ 0 := hQQ0
    have hQQ_pos : 0 < QQ.re := by
      -- QQ is real and nonneg; if re=0 then QQ=0 contradict hQQ_ne
      have : QQ.re ≠ 0 := by
        intro h0
        have : QQ = 0 := by
          apply Complex.ext <;> simp [h0, hQQ_im]
        exact hQQ_ne this
      exact lt_of_le_of_ne hQQ_nonneg (Ne.symm this)
    have hQQre_ne : QQ.re ≠ 0 := ne_of_gt hQQ_pos
    -- define z and compute its conjugate cleanly
    set z : ℂ := -QP / QQ
    have hz_as : z = -(conj PQ) / QQ := by
      show -QP / QQ = -(conj PQ) / QQ
      rw [hQP_conj]
    have hconjz_as : conj z = -PQ / QQ := by
      rw [hz_as]
      simp only [map_neg, map_div₀, star_def]
      rw [hQQ_real]
      simp only [Complex.conj_conj]
    -- positivity at the minimizing gauge
    have h0 : 0 ≤ (sesquilinear_form f (P + z • Q) (P + z • Q)).re := by
      simpa using h_pos (P + z • Q)
    -- expand
    have h0exp := sesquilinear_form_expansion (f := f) (P := P) (Q := Q) (z := z)
    have h0' :
        0 ≤ (PP + z * PQ + conj z * QP + Complex.normSq z * QQ).re := by
      -- rewrite h0 using the expansion
      rw [h0exp] at h0
      simpa [PP, PQ, QP, QQ] using h0
    -- Now do the algebra at the level of real parts, using QQ = ofReal QQ.re
    have hQQ_conj : conj QQ = QQ := hQQ_real
    have hQQ_conj' : (starRingEnd ℂ) QQ = QQ := hQQ_conj
    -- and freeze it as a rewrite lemma
    have inv_conjQQ : ((starRingEnd ℂ) QQ)⁻¹ = QQ⁻¹ := by
      simpa [hQQ_conj']
    have h_mixed :
        (z * PQ + conj z * QP).re = -2 * (Complex.normSq PQ) / QQ.re := by
      -- rewrite everything with hz_as, hconjz_as, QP=conj PQ, QQ=ofReal r
      have hQQ' : QQ = (QQ.re : ℂ) := hQQ_eq_ofReal
      -- conj PQ * PQ is the (real) normSq as a complex
      have hn : (conj PQ * PQ) = (Complex.normSq PQ : ℂ) := by
      -- `Complex.normSq_eq_conj_mul_self` is the theorem `normSq w = conj w * w`
      -- We want the converse: conj PQ * PQ = normSq PQ
        have := @Complex.normSq_eq_conj_mul_self PQ
        simpa [Complex.normSq] using this.symm
      -- First simplify the algebraic expression
      have h_alg : z * PQ + conj z * QP = -(conj PQ * PQ) / QQ + -(conj PQ * PQ) / QQ := by
        show z * PQ + (starRingEnd ℂ) z * QP = _
        rw [hQP_conj]
        show z * PQ + (starRingEnd ℂ) z * ((starRingEnd ℂ) PQ) = _
        rw [hz_as]
        show -(starRingEnd ℂ)
         PQ / QQ * PQ + (starRingEnd ℂ) (-(starRingEnd ℂ) PQ / QQ) * (starRingEnd ℂ) PQ = _
        simp only [map_neg, map_div₀, star_def, Complex.conj_conj, hQQ_real]
        ring
      -- This is 2 times the same thing
      have h_two : -(conj PQ * PQ) / QQ + -(conj PQ * PQ) / QQ = -(2:ℂ) * (conj PQ * PQ) / QQ := by
        ring
      -- Use normSq
      have h_ns : -(2:ℂ) * (conj PQ * PQ) / QQ = -(2:ℂ) * (Complex.normSq PQ : ℂ) / QQ := by
        rw [hn]
      -- Extract real part
      calc
        (z * PQ + conj z * QP).re
            = (-(conj PQ * PQ) / QQ + -(conj PQ * PQ) / QQ).re := by rw [h_alg]
        _ = (-(2:ℂ) * (conj PQ * PQ) / QQ).re := by rw [h_two]
        _ = (-(2:ℂ) * (Complex.normSq PQ : ℂ) / QQ).re := by rw [h_ns]
        _ = -2 * (Complex.normSq PQ) / QQ.re := by
              rw [hQQ']
              simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg,
                         Complex.ofReal_ofNat, Complex.mul_re, Complex.div_re,
                         Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_div, sub_zero,
                         Complex.normSq_ofReal, Complex.neg_re, Complex.ofReal_ofNat]
              norm_num
              field_simp [hQQre_ne]
    have h_last :
        (Complex.normSq z * QQ).re = (Complex.normSq PQ) / QQ.re := by
      have hQQ' : QQ = (QQ.re : ℂ) := hQQ_eq_ofReal
      -- normSq z = normSq PQ / normSq QQ, and normSq QQ = (QQ.re)^2 since QQ is real
      have h_normSq_z : Complex.normSq z = Complex.normSq PQ / Complex.normSq QQ := by
        simp only [z, Complex.normSq_div, Complex.normSq_neg]
        rw [hQP_conj]
        simp only [star_def, Complex.normSq_conj]
      have h_normSq_QQ : Complex.normSq QQ = (QQ.re)^2 := by
      -- QQ.im = 0 makes normSq = re^2
        rw [Complex.normSq_apply, hQQ_im]
        ring
      -- finish: substitute and simplify
      calc
        (Complex.normSq z * QQ).re
            = Complex.normSq z * QQ.re := by
                rw [hQQ']
                simp only [Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re,
                           Complex.ofReal_im, mul_zero, sub_zero]
        _ = (Complex.normSq PQ / Complex.normSq QQ) * QQ.re := by rw [h_normSq_z]
        _ = (Complex.normSq PQ / (QQ.re ^ 2)) * QQ.re := by rw [h_normSq_QQ]
        _ = Complex.normSq PQ / QQ.re := by field_simp [hQQre_ne]
    -- combine: 0 ≤ PP.re - normSq(PQ)/QQ.re
    have h_core : 0 ≤ PP.re - (Complex.normSq PQ) / QQ.re := by
      have hsum : 0 ≤ PP.re + (z * PQ + conj z * QP).re + (Complex.normSq z * QQ).re := by
      -- this should be a straightforward re-association of h0'
      -- (if it's already exactly that, just `exact h0'`)
        simpa [Complex.add_re, add_assoc, add_left_comm, add_comm] using h0'
      -- now substitute
      -- Manually rewrite using the equalities
      rw [h_mixed, h_last] at hsum
      -- Now hsum is: 0 ≤ PP.re + (-2 * normSq PQ / QQ.re) + (normSq PQ / QQ.re)
      -- Simplify: -2x + x = -x
      have : PP.re + -2 * Complex.normSq PQ / QQ.re + Complex.normSq PQ / QQ.re =
             PP.re - Complex.normSq PQ / QQ.re := by ring
      linarith
    have h_sub : (Complex.normSq PQ) / QQ.re ≤ PP.re := by
      exact (sub_nonneg).1 h_core
    -- multiply by QQ.re > 0
    have h_mul : QQ.re * ((Complex.normSq PQ) / QQ.re) ≤ QQ.re * PP.re :=
      mul_le_mul_of_nonneg_left h_sub (le_of_lt hQQ_pos)
    have h_cancel : QQ.re * ((Complex.normSq PQ) / QQ.re) = Complex.normSq PQ := by
      field_simp [hQQre_ne]
    -- final
    have : Complex.normSq PQ ≤ PP.re * QQ.re := by
      -- rewrite h_mul and commute
      have : Complex.normSq PQ ≤ QQ.re * PP.re := by simpa [h_cancel] using h_mul
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    simpa [PP, PQ, QQ] using this

/-! ## ROADMAP TO BOCHNER'S THEOREM -/

/-! ### Bridge Lemmas: Connecting General CS to const_one Specialization -/

/-- NormSq is invariant under conjugation. -/
lemma normSq_conj (z : ℂ) : Complex.normSq (conj z) = Complex.normSq z := by
  simp [Complex.normSq, Complex.conj_re, Complex.conj_im]

lemma cast_sub_eq_neg_cast_sub (m n : ℤ) :
    ((n - m : ℤ) : ℝ) = -((m - n : ℤ) : ℝ) := by
  have : (n - m : ℤ) = -(m - n) := by abel
  calc
    ((n - m : ℤ) : ℝ) = ((-(m - n) : ℤ) : ℝ) := congrArg (fun z : ℤ => (z : ℝ)) this
    _ = -((m - n : ℤ) : ℝ) := by simpa using (Int.cast_neg (m - n))

/-- Correct diagonal bridge: Λ(normSq P) matches the diagonal sesquilinear form
    but with `f` precomposed by negation. -/
lemma ΛTrigℤ_normSq_re_eq_sesq_neg_diag_re (f : ℝ → ℂ) (P : TrigPolyℤ) :
    (ΛTrigℤ f (TrigPolyℤ.normSq P)).re =
      (sesquilinear_form (fun x => f (-x)) P P).re := by
  classical
  -- Start from your proved double-sum identity and take real parts
  have h :=
    congrArg Complex.re (ΛTrigℤ_normSq_eq_double_sum (f := f) (P := P))
  -- h :
  -- (Λ ...).re = (∑ n∈S, ∑ m∈S, conj(P n) * P m * f (m - n)).re

  -- Swap the binders on the RHS of h (this only swaps, does NOT change the body)
  have hswap :
      (∑ n ∈ P.support, ∑ m ∈ P.support,
          conj (P n) * P m * f (m - n)).re
        =
      (∑ m ∈ P.support, ∑ n ∈ P.support,
          conj (P m) * P n * f (n - m)).re := by
    -- do it at the ℂ level, then take `.re`
    have hs :
        (∑ n ∈ P.support, ∑ m ∈ P.support,
            conj (P n) * P m * f (m - n))
          =
        (∑ m ∈ P.support, ∑ n ∈ P.support,
            conj (P m) * P n * f (n - m)) := by
      -- `rw [Finset.sum_comm]` swaps binders and (definitionally) swaps the variable names
      -- if you write the RHS in the swapped variable names.
      -- So we just *tell* Lean the swapped-form explicitly:
      rw [Finset.sum_comm]
    exact congrArg Complex.re hs
  -- Combine
  have h' :
      (ΛTrigℤ f (TrigPolyℤ.normSq P)).re =
        (∑ m ∈ P.support, ∑ n ∈ P.support,
            conj (P m) * P n * f (n - m)).re := by
    exact Eq.trans h hswap
  -- Now convert the RHS into sesquilinear_form (f∘neg) by rewriting f(n-m) = (f∘neg)(m-n).
  -- Unfold sesquilinear_form and do termwise rewrite.
  -- No simp: use sum_congr and rw.
  unfold sesquilinear_form
  -- goal becomes: RHS = (∑ m∈S, ∑ n∈S, conj(P m)*P n*(fun x => f(-x)) (m-n)).re
  refine Eq.trans h' ?_
  -- enough to show the complex sums are equal
  apply congrArg Complex.re
  refine Finset.sum_congr rfl ?_
  intro m hm
  refine Finset.sum_congr rfl ?_
  intro n hn
  -- inside: intro m hm; intro n hn; goal about summands
  have hcast_sub (a b : ℤ) : ((a - b : ℤ) : ℝ) = (a : ℝ) - (b : ℝ) := by
    simpa using (Int.cast_sub a b : ((a - b : ℤ) : ℝ) = (a : ℝ) - (b : ℝ))
  have hneg_real : ((n - m : ℤ) : ℝ) = -((m - n : ℤ) : ℝ) := by
    -- uses your existing lemma; just flip orientation
    simpa using (cast_sub_eq_neg_cast_sub m n).symm
  -- Now prove the term equality by rewriting f-arguments via hcast_sub and hneg_real
  calc
    conj (P m) * P n * f ((n : ℝ) - (m : ℝ))
        = conj (P m) * P n * f (((n - m : ℤ) : ℝ)) := by
            -- turn (↑n - ↑m) into ↑(n-m)
            rw [← hcast_sub n m]
    _ = conj (P m) * P n * f (-(((m - n : ℤ) : ℝ))) := by
            rw [hneg_real]
    _ = conj (P m) * P n * (fun x => f (-x)) ((m : ℝ) - (n : ℝ)) := by
            -- turn ↑(m-n) into (↑m-↑n), then it's definitional
            rw [← hcast_sub m n]

/-- Evaluate the sesquilinear form on `const_one` against itself. -/
lemma sesquilinear_form_const_one_const_one_sum_level (f : ℝ → ℂ) :
    (∑ m ∈ ({0} : Finset ℤ), ∑ n ∈ ({0} : Finset ℤ),
        (starRingEnd ℂ) (TrigPolyℤ.const_one m) * TrigPolyℤ.const_one n * f (↑m - ↑n))
      = f 0 := by
  -- Evaluate the sums over singletons
  rw [Finset.sum_singleton, Finset.sum_singleton]
  -- Simplify m = 0, n = 0
  simp only [Int.cast_zero, sub_self]
  -- const_one 0 = 1 (as a complex number)
  have h : TrigPolyℤ.const_one 0 = (1 : ℂ) := by
    rw [TrigPolyℤ.const_one]
    exact Finsupp.single_eq_same
  rw [h]
  -- star (1 : ℂ) = 1
  simp [starRingEnd_apply, star_one, one_mul]

/-- Cauchy-Schwarz specialized to Q = const_one -/
lemma cauchy_schwarz_const_one (f : ℝ → ℂ) (hf : IsPositiveDefinite f) (P : TrigPolyℤ) :
    Complex.normSq (sesquilinear_form f P TrigPolyℤ.const_one) ≤
    (sesquilinear_form f P P).re *
     (sesquilinear_form f TrigPolyℤ.const_one TrigPolyℤ.const_one).re :=
  cauchy_schwarz_complex f hf P TrigPolyℤ.const_one

/-- Cauchy–Schwarz for the positive functional Λ, in sesquilinear form. -/
lemma cauchy_schwarz_for_Λ
  (f : ℝ → ℂ) (hf : IsPositiveDefinite f) (P Q : TrigPolyℤ) :
    Complex.normSq (sesquilinear_form (fun x => f (-x)) P Q) ≤
      (ΛTrigℤ f (TrigPolyℤ.normSq Q)).re * (ΛTrigℤ f (TrigPolyℤ.normSq P)).re := by
  classical
  -- 1) `fneg` is positive definite if `f` is (use the built-in symmetry in your def)
  have hfneg : IsPositiveDefinite (fun x => f (-x)) := by
    refine ⟨?_, ?_⟩
    · intro x
      -- g(-x)=f(x), conj(g x)=conj(f(-x)) and hf.1 gives f x = conj (f (-x))
      simpa using (hf.1 (-x))
    · intro n x c
      -- Start from hf positivity on the same x,c
      -- have h := hf.2 n x c
      -- simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (hf.2 n (fun i => - x i) c)
  -- 2) Complex CS for the sesquilinear form with `fneg`
  have hCS :=
    cauchy_schwarz_complex (f := (fun x => f (-x))) (hf := hfneg) (P := P) (Q := Q)
  -- 3) Rewrite both diagonal terms via your bridge lemma
  have hPP :
      (sesquilinear_form (fun x => f (-x)) P P).re =
        (ΛTrigℤ f (TrigPolyℤ.normSq P)).re := by
    simpa using (ΛTrigℤ_normSq_re_eq_sesq_neg_diag_re (f := f) (P := P)).symm
  have hQQ :
      (sesquilinear_form (fun x => f (-x)) Q Q).re =
        (ΛTrigℤ f (TrigPolyℤ.normSq Q)).re := by
    simpa using (ΛTrigℤ_normSq_re_eq_sesq_neg_diag_re (f := f) (P := Q)).symm
  -- 4) Finish: substitute and commute the product
  simpa [hPP, hQQ, mul_comm, mul_left_comm, mul_assoc] using hCS


/-- For any element in the span, we can find a trig poly that maps to something close to it.
    Key: the span has dense closure = ⊤, so we can approximate any g. -/
lemma approx_by_trigpoly (g : C(𝕋, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : TrigPolyℤ, ‖g - P.toCircle‖ < ε := by
  -- Use density: closure = ⊤
  have h_dense : (Submodule.span ℂ (Set.range TrigPolyℤ.toCircle)).topologicalClosure = ⊤ :=
    trigPolyℤ_dense
  -- Key: closure = ⊤ means the span is
  -- dense (Mathlib: Submodule.dense_iff_topologicalClosure_eq_top)
  have h_span_dense : Dense (Submodule.span ℂ (Set.range TrigPolyℤ.toCircle) : Set (C(𝕋, ℂ))) := by
    rwa [Submodule.dense_iff_topologicalClosure_eq_top]
  -- Use Dense.exists_dist_lt: in a metric space, density gives approximation
  have ⟨y, hy_span, hy_close⟩ := h_span_dense.exists_dist_lt g hε
  -- Key insight: span of range = range (since toCircle behaves linearly)
  rw [trigPolyℤ_toCircle_span_eq_range] at hy_span
  -- So y ∈ range, meaning y = P.toCircle for some P
  obtain ⟨P, hP⟩ := hy_span
  -- We have dist g y < ε, which equals ‖g - y‖ < ε in a normed space
  use P
  rw [← hP] at hy_close
  -- Convert dist to norm: dist x y = ‖x - y‖
  rwa [dist_eq_norm] at hy_close

/-! ### Extension of ΛTrigℤ via Profinite Analogy -/
lemma fourier_eval_rational_eq_character
    (n : ℕ) [NeZero n] (k : ℤ) (m : ZMod n) :
    fourier k (QuotientAddGroup.mk ((m.val : ℝ) / (n : ℝ)) : 𝕋) =
    character n (k : ZMod n) m := by
  classical
  unfold character
  -- Don't unfold fourier - we'll use fourier_coe_apply instead
  set r : ℝ := (m.val : ℝ) / (n : ℝ)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  set k0 : ℤ := ((k : ZMod n).val : ℤ)
  -- k ≡ k0 [ZMOD n]
  have hk_mod : (k : ℤ) ≡ k0 [ZMOD (n : ℤ)] := by
    have h0 : (k : ℤ) ≡ k % (n : ℤ) [ZMOD (n : ℤ)] := by
      simpa using (Int.mod_modEq k (n : ℤ)).symm
    have hmod_eq : k % (n : ℤ) = ((k : ZMod n).val : ℤ) := by
      simpa using (ZMod.val_intCast (n := n) k).symm
    simpa [k0, hmod_eq] using h0
  -- extract k = k0 + t*n
  have h_dvd : (n : ℤ) ∣ (k - k0) := by
    have : k0 - k = -(k - k0) := by ring
    rw [Int.modEq_iff_dvd] at hk_mod
    rw [this] at hk_mod
    exact Int.dvd_neg.mp hk_mod
  rcases h_dvd with ⟨t, ht⟩
  have hk_eq_int : k = k0 + t * (n : ℤ) := by linarith
  have hk_eq_real : (k : ℝ) = (k0 : ℝ) + (t : ℝ) * (n : ℝ) := by exact_mod_cast hk_eq_int
  -- Key: k*r = k0*r + t*m.val (multiply AFTER decomposition)
  have hnr : (n : ℝ) * r = (m.val : ℝ) := by
    simp only [r]
    field_simp
  have hkr : (k : ℝ) * r = (k0 : ℝ) * r + (t : ℝ) * (m.val : ℝ) := by
    calc (k : ℝ) * r = ((k0 : ℝ) + (t : ℝ) * (n : ℝ)) * r := by rw [hk_eq_real]
      _ = (k0 : ℝ) * r + (t : ℝ) * ((n : ℝ) * r) := by ring
      _ = (k0 : ℝ) * r + (t : ℝ) * (m.val : ℝ) := by rw [hnr]
  -- Kill periodic factor: exp(2πi * (t*m.val)) = 1
  set z : ℤ := t * (m.val : ℤ)
  have hz : (t : ℝ) * (m.val : ℝ) = (z : ℝ) := by simp [z]
  -- First scale hkr by the constants
  have hkr_scaled : (2 * π * Complex.I) * ((k : ℝ) * r : ℂ) =
                    (2 * π * Complex.I) * (((k0 : ℝ) * r + (t : ℝ) * (m.val : ℝ)) : ℂ) := by
    congr 1; exact_mod_cast hkr
  have hexp : Complex.exp (2 * π * Complex.I * ((k : ℝ) * r : ℂ)) =
              Complex.exp (2 * π * Complex.I * (((k0 : ℝ) * r) : ℂ)) := by
    calc Complex.exp (2 * π * Complex.I * ((k : ℝ) * r : ℂ))
        = Complex.exp ((2 * π * Complex.I) * (((k0 : ℝ) * r + (t : ℝ) * (m.val : ℝ)) : ℂ)) := by
            rw [hkr_scaled]
      _ = Complex.exp (2 * π * Complex.I * (((k0 : ℝ) * r) : ℂ) + 2 * π * Complex.I *
       (((t : ℝ) * (m.val : ℝ)) : ℂ)) := by
            congr 1; push_cast; ring
      _ = Complex.exp (2 * π * Complex.I * (((k0 : ℝ) * r) : ℂ)) *
          Complex.exp (2 * π * Complex.I * ((z : ℝ) : ℂ)) := by
            rw [Complex.exp_add]
            congr 2
            have : (2 * π * Complex.I * (((t : ℝ) * (m.val : ℝ)) : ℂ)) =
             (2 * π * Complex.I * ((z : ℝ) : ℂ)) := by
              congr 1; exact_mod_cast hz
            exact this
      _ = Complex.exp (2 * π * Complex.I * (((k0 : ℝ) * r) : ℂ)) * 1 := by
            congr 1
            calc Complex.exp (2 * π * Complex.I * ((z : ℝ) : ℂ))
                = Complex.exp ((z : ℂ) * (2 * π * Complex.I)) := by push_cast; ring_nf
              _ = 1 := Complex.exp_int_mul_two_pi_mul_I z
      _ = Complex.exp (2 * π * Complex.I * (((k0 : ℝ) * r) : ℂ)) := by ring_nf
  -- Use fourier_coe_apply to get exponential form
  rw [fourier_coe_apply (T := 1)]
  -- Show both sides equal, using hexp
  convert hexp using 2
  · simp only [k0, r]; field_simp; push_cast; ring
  · simp only [k0, r]; field_simp; push_cast; ring

/-- Helper: Eventually `k mod p^n ≠ 0` for `k ≠ 0`. -/
lemma eventually_ne_zero_mod_prime_power
    (p : ℕ) [Fact (Nat.Prime p)] (k : ℤ) (hk : k ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, (k : ZMod (p^n)) ≠ 0 := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := hp.pos
  have hp_one_lt : 1 < p := hp.one_lt
  refine ⟨k.natAbs + 1, ?_⟩
  intro n hn hkz
  -- From (k : ZMod (p^n)) = 0, get (p^n : ℤ) ∣ k
  have hdvd : (p^n : ℤ) ∣ k := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd k (p^n)).1 hkz
  -- Show k.natAbs < p^n using growth of p^m for p>1 and monotonicity in exponent
  have hlt_nat : k.natAbs < p^n := by
    -- First: k.natAbs < p^(k.natAbs+1)
    have h1 : k.natAbs < p^(k.natAbs + 1) := by
      -- For p > 1, we have m < p^m, so m < m+1 ≤ p^(m+1)
      calc k.natAbs < k.natAbs + 1 := Nat.lt_succ_self _
        _ ≤ p^(k.natAbs + 1) := (Nat.lt_pow_self hp_one_lt).le
    -- Then: p^(k.natAbs+1) ≤ p^n since n ≥ k.natAbs+1
    have hle : p^(k.natAbs + 1) ≤ p^n :=
      Nat.pow_le_pow_right hp_pos hn
    exact lt_of_lt_of_le h1 hle
  -- Turn the divisibility into a Nat divisibility p^n ∣ k.natAbs
  have hdvd_nat : p^n ∣ k.natAbs := by
    rcases hdvd with ⟨t, rfl⟩
    -- natAbs ((p^n : ℤ) * t) = (p^n) * natAbs t
    -- so p^n divides it
    refine ⟨t.natAbs, ?_⟩
    -- simplify natAbs of the product
    simp [Int.natAbs_mul]
  -- If p^n ∣ k.natAbs and k.natAbs < p^n, then k.natAbs = 0
  have hzero_abs : k.natAbs = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd_nat hlt_nat
  -- natAbs k = 0 ↔ k = 0, contradiction
  have : k = 0 := Int.natAbs_eq_zero.mp hzero_abs
  exact hk this

/-- Riemann sum at level p^n equals sum of characters -/
lemma riemann_sum_eq_character_sum
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero (p^n)] (k : ℤ) :
    ∑ m : ZMod (p^n), fourier k ((m.val : ℝ) / (p^n : ℝ) : 𝕋) =
    ∑ m : ZMod (p^n), character (p^n) (k : ZMod (p^n)) m := by
  classical
  congr 1 with m
  convert fourier_eval_rational_eq_character (p^n) k m using 1
  norm_cast

/-- Riemann sum equals zero when k ≢ 0 (mod p^n) -/
lemma riemann_sum_zero
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero (p^n)]
    (k : ℤ) (hk : (k : ZMod (p^n)) ≠ 0) :
    ∑ m : ZMod (p^n), fourier k ((m.val : ℝ) / (p^n : ℝ) : 𝕋) = 0 := by
  rw [riemann_sum_eq_character_sum]
  -- Now use your existing DFT result!
  exact sum_character_eq_zero_of_ne_zero p n (k : ZMod (p^n)) hk

/-- Direct proof: Integral of non-constant fourier is zero.
    This uses interval integration directly, avoiding circular dependencies. -/
lemma integral_fourier_eq_zero_of_ne_zero' (k : ℤ) (hk : k ≠ 0) :
    ∫ (x : 𝕋), fourier k x = 0 := by
  -- Bridge to interval integral: ∫_𝕋 f = ∫_0^1 f(t)
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have h_bridge : ∫ (x : 𝕋), fourier k x =
      ∫ t in (0:ℝ)..(1:ℝ), (fourier k : C(𝕋, ℂ)) ((t : ℝ) : 𝕋) := by
    have h := AddCircle.intervalIntegral_preimage 1 0 (fourier k : 𝕋 → ℂ)
    simp only [zero_add] at h
    exact h.symm
  rw [h_bridge]
  -- The integrand is e^{2πikt}
  have h_integrand : ∀ t : ℝ, (fourier k : C(𝕋, ℂ)) ((t : ℝ) : 𝕋) =
      Complex.exp (2 * π * Complex.I * k * t) := by
    intro t
    rw [fourier_coe_apply (T := 1)]
    congr 1
    push_cast
    ring
  simp_rw [h_integrand]
  -- Compute the integral directly
  -- ∫_0^1 e^{2πikt} dt = [e^{2πikt}/(2πik)]_0^1 = (e^{2πik} - 1)/(2πik) = 0
  set c : ℂ := 2 * π * Complex.I * k with hc_def
  have h_coeff_ne : c ≠ 0 := by
    rw [hc_def]
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero,
      I_ne_zero, Int.cast_eq_zero, hk, or_self, not_false_eq_true]
  -- Antiderivative: d/dt (e^{ct}/c) = e^{ct}
  have h_deriv : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (c * t) / c)
      (Complex.exp (c * x)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := hasDerivAt_id' x |>.ofReal_comp
    have h2 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
      convert h1.const_mul c using 1; ring
    have h3 : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ))) (Complex.exp (c * x) * c) x :=
      Complex.hasDerivAt_exp (c * x) |>.comp x h2
    have h4 : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)) / c)
        (Complex.exp (c * x) * c / c) x := h3.div_const c
    simp only [mul_div_assoc, div_self h_coeff_ne, mul_one] at h4
    exact h4
  -- Compute using fundamental theorem of calculus
  have h_int : ∫ t in (0:ℝ)..(1:ℝ), Complex.exp (c * t) = (Complex.exp c - 1) / c := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => h_deriv x)
        (Continuous.intervalIntegrable (by continuity) _ _)]
    have h1 : c * (1 : ℝ) = c := by simp
    have h0 : c * (0 : ℝ) = 0 := by simp
    rw [h1, h0, Complex.exp_zero]
    field_simp [h_coeff_ne]
  rw [h_int]
  -- e^{2πik} = 1 for integer k
  have h_exp_eq_one : Complex.exp c = 1 := by
    rw [hc_def]
    have : (2 : ℂ) * π * Complex.I * k = (k : ℂ) * (2 * π * Complex.I) := by ring
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [h_exp_eq_one]
  simp

lemma eventually_riemann_sum_fourier_eq_integral
    (p : ℕ) [Fact (Nat.Prime p)] (k : ℤ) :
    ∃ N : ℕ, ∀ n ≥ N, [NeZero (p^n)] →
      (1 / (p^n : ℂ)) * ∑ m : ZMod (p^n), fourier k ((m.val : ℝ) / (p^n : ℝ) : 𝕋)
        = ∫ x : 𝕋, fourier k x := by
  classical
  by_cases hk : k = 0
  · -- Case k = 0: fourier 0 = 1, sum = p^n, integral = 1
    subst hk
    refine ⟨0, ?_⟩
    intro n _hn _hneZero
    -- Goal: (1/p^n) * ∑ m, 1 = ∫ x, 1
    simp only [fourier_zero, ContinuousMap.coe_one, Pi.one_apply]
    -- Sum of 1's = cardinality = p^n
    have hcard : (∑ _m : ZMod (p^n), (1 : ℂ)) = (p^n : ℂ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card]
      simp
    -- Integral of 1 = 1 (Haar probability measure)
    haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
    -- For AddCircle 1, volume = 1 • haarAddCircle = haarAddCircle
    have h_vol_eq : (volume : Measure 𝕋) = AddCircle.haarAddCircle := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp only [ENNReal.ofReal_one, one_smul]
    have hint : ∫ (_x : 𝕋), (1 : ℂ) = 1 := by
      rw [MeasureTheory.integral_const, h_vol_eq, MeasureTheory.probReal_univ, one_smul]
    rw [hcard, hint]
    norm_cast
    have hp_ne : (p : ℂ) ^ n ≠ 0 := by
      apply pow_ne_zero
      norm_cast
      exact Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
    field_simp [hp_ne]
  · -- Case k ≠ 0: eventually k ≢ 0 (mod p^n)
    obtain ⟨N, hN⟩ := eventually_ne_zero_mod_prime_power p k hk
    refine ⟨N, ?_⟩
    intro n hn _hneZero
    have hkmod : (k : ZMod (p^n)) ≠ 0 := hN n hn
    -- Finite-level orthogonality
    have hsum0 : ∑ m : ZMod (p^n), fourier k ((m.val : ℝ) / (p^n : ℝ) : 𝕋) = 0 :=
      riemann_sum_zero p n k hkmod
    -- Goal is to show: (1/p^n) * 0 = ∫ (x : 𝕋), (fourier k) x
    -- Since the sum is 0, LHS = 0. RHS = 0 by integral_fourier_eq_zero_of_ne_zero'.
    rw [hsum0, mul_zero]
    exact (integral_fourier_eq_zero_of_ne_zero' k hk).symm

-- ✅ COHOMOLOGICAL INTEGRATION: Riemann sums on roots of unity → integral on S¹
lemma riemann_sum_converges_to_integral
    (f : C(𝕋, ℂ)) (p : ℕ) [Fact (Nat.Prime p)] :
    Filter.Tendsto
      (fun n => (1 / (p^n : ℂ)) * ∑ m : ZMod (p^n), f ((m.val : ℝ) / (p^n : ℝ) : 𝕋))
      Filter.atTop
      (nhds (∫ (x : 𝕋), f x)) := by
  classical
  -- Step 1: Bridge to [0,1) integral using AddCircle.intervalIntegral_preimage
  have h_bridge : ∫ (x : 𝕋), f x = ∫ t in (0:ℝ)..(1:ℝ), f (QuotientAddGroup.mk t) := by
    -- For 𝕋 = AddCircle 1, we use the bridge lemma with T=1 and t=0
    -- Pass T=1 explicitly
    have h : (∫ a in (0:ℝ)..(0:ℝ) + (1:ℝ), (f : 𝕋 → ℂ) a) = ∫ (b : 𝕋), f b :=
      AddCircle.intervalIntegral_preimage 1 0 (f : 𝕋 → ℂ)
    simp only [zero_add] at h
    exact h.symm
  rw [h_bridge]
  -- Define the periodic lift F : ℝ → ℂ
  let F : ℝ → ℂ := fun t => f (QuotientAddGroup.mk t)
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Step 2a: Uniform continuity of F on [0,1]
  have hF_cont : Continuous F := by
    exact f.continuous.comp (continuous_quotient_mk')
  have hF_uc : UniformContinuousOn F (Set.Icc (0:ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hF_cont.continuousOn
  -- Get δ from uniform continuity
  rw [Metric.uniformContinuousOn_iff] at hF_uc
  have hε2 : 0 < (ε / 2) := by nlinarith [hε]
  obtain ⟨δ, hδ_pos, hδ⟩ := hF_uc (ε/2) hε2
  -- Step 2b: Choose N so mesh 1/p^N < δ
  have h_mesh : ∃ N, ∀ n ≥ N, (1 : ℝ) / (p^n : ℝ) < δ := by
    -- p^n grows exponentially, so 1/p^n → 0
    have hp : 1 < (p : ℝ) := by
      have := Fact.out (p := Nat.Prime p)
      exact Nat.one_lt_cast.mpr (Nat.Prime.one_lt this)
    -- For any δ > 0, choose N so p^N > 1/δ, i.e., 1/p^N < δ
    have h_pow_unbdd : ∀ C : ℝ, ∃ N, C < (p : ℝ) ^ N := fun C =>
      pow_unbounded_of_one_lt C hp
    obtain ⟨N, hN⟩ := h_pow_unbdd (1/δ)
    use N
    intro n hn
    -- Goal: 1/p^n < δ
    -- We have: p^N > 1/δ (from hN), and p^n ≥ p^N (since n ≥ N)
    -- Therefore: 1/p^n ≤ 1/p^N < δ
    have hpN_pos : 0 < (p : ℝ)^N := pow_pos (by linarith : 0 < (p:ℝ)) N
    have hpn_pos : 0 < (p : ℝ)^n := pow_pos (by linarith : 0 < (p:ℝ)) n
    have hpow_le : (p : ℝ)^N ≤ (p : ℝ)^n := by
      norm_cast
      have hp_prime := Fact.out (p := Nat.Prime p)
      exact Nat.pow_le_pow_right (Nat.Prime.pos hp_prime) hn
    -- Direct proof using field arithmetic
    -- We need: 1/p^n < δ
    -- We have: 1/δ < p^N ≤ p^n
    -- So: 1 < δ·p^n, which implies 1/p^n < δ (dividing both sides by p^n > 0)
    have h1 : (1 : ℝ) < δ * (p^n : ℝ) := by
      calc (1 : ℝ) = (1/δ) * δ := by field_simp
        _ < (p : ℝ)^N * δ := by nlinarith [hN, hδ_pos]
        _ ≤ δ * (p : ℝ)^n := by nlinarith [hpow_le, hδ_pos]
    -- From 1 < δ·p^n, divide both sides by p^n > 0 to get 1/p^n < δ
    have : (1 : ℝ) < δ * (p^n : ℝ) := h1
    calc (1 : ℝ) / (p^n : ℝ)
        < (δ * (p^n : ℝ)) / (p^n : ℝ) := by apply div_lt_div_of_pos_right this hpn_pos
      _ = δ := by field_simp
  obtain ⟨N, hN_mesh⟩ := h_mesh
  use N
  intro n hn
  -- Step 2c: Bound the error using uniform continuity
  -- Key fact: mesh size is less than δ
  have h_mesh_bound : (1 : ℝ) / (p^n : ℝ) < δ := hN_mesh n hn
  -- Goal: dist (Riemann sum) (integral) < ε
  -- We'll show this by triangle inequality and uniform continuity
  -- First, relate the Riemann sum to F
  -- The sum ∑ m : ZMod (p^n), f ((m.val : ℝ) / (p^n : ℝ) : 𝕋) equals
  -- ∑ m : ZMod (p^n), F (m.val / p^n)
  have h_sum_eq : ∑ m : ZMod (p^n), f ((m.val : ℝ) / (p^n : ℝ) : 𝕋) =
                   ∑ m : ZMod (p^n), F (m.val / p^n) := by
    rfl
  -- Now we need to bound |∫₀¹ F - (1/p^n) ∑ F(m/p^n)|
  -- Strategy: On each interval [m/p^n, (m+1)/p^n), the difference |F(t) - F(m/p^n)| < ε/2
  -- by uniform continuity since the mesh < δ
  -- Convert to norm bound
  rw [dist_comm, Complex.dist_eq]
  -- We'll work with the fact that F is integrable and uniformly continuous
  -- The key is that on each cell [m/p^n, (m+1)/p^n], we have |F(t) - F(m/p^n)| < ε/2
  -- First establish that all the sample points are in [0,1]
  have h_sample_in : ∀ m : ZMod (p^n), (m.val : ℝ) / (p^n : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    intro m
    constructor
    · apply div_nonneg
      · exact Nat.cast_nonneg m.val
      · positivity
    · have h_val_lt : (m.val : ℝ) < (p^n : ℝ) := by
        norm_cast
        exact m.val_lt
      have h_pn_pos : 0 < (p^n : ℝ) := by
        have hp_prime := Fact.out (p := Nat.Prime p)
        have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.Prime.pos hp_prime)
        exact pow_pos hp_pos n
      have h_lt : (m.val : ℝ) / (p^n : ℝ) < 1 := by
        calc (m.val : ℝ) / (p^n : ℝ)
            < (p^n : ℝ) / (p^n : ℝ) := by apply div_lt_div_of_pos_right h_val_lt h_pn_pos
          _ = 1 := by field_simp [ne_of_gt h_pn_pos]
      exact le_of_lt h_lt
  set N := p^n with hN_def
  set u : ℕ → ℝ := fun i => (i : ℝ) / (N : ℝ) with hu_def
  -- Partition the integral using sum_integral_adjacent_intervals
  have h_partition : intervalIntegral F 0 1 volume =
      Finset.sum (Finset.range N) (fun i => intervalIntegral F (u i) (u (i + 1)) volume) := by
    have hu0 : u 0 = 0 := by simp only [u]; ring
    have huN : u N = 1 := by
      simp only [u, hN_def]
      have hp_pos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
      have hN_pos : (0 : ℝ) < p^n := pow_pos (Nat.cast_pos.mpr hp_pos) n
      field_simp
    rw [← hu0, ← huN]
    exact (intervalIntegral.sum_integral_adjacent_intervals fun k _hk =>
      hF_cont.continuousOn.intervalIntegrable).symm
  -- Convert ZMod sum to Finset.range sum
  -- ZMod N consists of elements with val ∈ {0, 1, ..., N-1}
  have hN_pos : 0 < N := by
    simp only [hN_def]
    exact pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) n
  have hN_ne : NeZero N := ⟨ne_of_gt hN_pos⟩
  have h_zmod_range :
      (∑ m : ZMod N, F ((m.val : ℝ) / (N : ℝ))) =
      Finset.sum (Finset.range N) (fun i => F ((i : ℝ) / (N : ℝ))) := by
    -- For N > 0, ZMod N = Fin N, and sum over Fin N = sum over range N
    -- Use Finset.sum_bij to establish the bijection
    apply Finset.sum_bij (fun (m : ZMod N) _ => m.val)
    -- 1. m.val ∈ range N
    case hi =>
      intro m _
      simp only [Finset.mem_range]
      exact ZMod.val_lt m
    -- 2. Function values are equal
    case h =>
      intro m _
      rfl
    -- 3. Injective on domain
    case i_inj =>
      intro m₁ _ m₂ _ h_eq
      exact ZMod.val_injective N h_eq
    -- 4. Surjective onto range N
    case i_surj =>
      intro i hi
      simp only [Finset.mem_range] at hi
      refine ⟨(i : ZMod N), Finset.mem_univ _, ?_⟩
      exact ZMod.val_natCast_of_lt hi
  have h_dist_eq : (1 / (N : ℂ)) * Finset.sum (Finset.range N) (fun i => F ((i : ℝ) / (N : ℝ))) =
      Finset.sum (Finset.range N) (fun i => (1 / (N : ℂ)) * F ((i : ℝ) / (N : ℝ))) := by
    rw [Finset.mul_sum]
  have calc_result : ‖Finset.sum (Finset.range N)
   (fun i => intervalIntegral F (u i) (u (i + 1)) volume) -
                       Finset.sum (Finset.range N)
                        (fun i => (1 / (N : ℂ)) * F ((i : ℝ) / (N : ℝ)))‖ < ε := by
    have h_norm_dist :
     ‖Finset.sum (Finset.range N) (fun i => intervalIntegral F (u i) (u (i + 1)) volume) -
           Finset.sum (Finset.range N) (fun i => (1 / (N : ℂ)) * F ((i : ℝ) / (N : ℝ)))‖ =
        dist (Finset.sum (Finset.range N) (fun i => intervalIntegral F (u i) (u (i + 1)) volume))
            (Finset.sum (Finset.range N) (fun i => (1 / (N : ℂ)) * F ((i : ℝ) / (N : ℝ)))) := by
      rw [← Complex.dist_eq]
    rw [h_norm_dist]
    -- Use triangle inequality for sums
    calc dist (Finset.sum (Finset.range N) (fun i => intervalIntegral F (u i) (u (i + 1)) volume))
            (Finset.sum (Finset.range N) (fun i => (1 / (N : ℂ)) * F ((i : ℝ) / (N : ℝ))))
      _ ≤ Finset.sum (Finset.range N) (fun i => dist (intervalIntegral F (u i) (u (i + 1)) volume)
                                        ((1 / (N : ℂ)) * F ((i : ℝ) / (N : ℝ)))) := by
          apply dist_sum_sum_le_of_le
          intro i hi
          rfl
      _ ≤ Finset.sum (Finset.range N) (fun _ => ε / 2 / N) := by
        apply Finset.sum_le_sum
        intro i hi
        have h_const_integral : (1 / (N : ℂ)) * F ((i : ℝ) / (N : ℝ)) =
            ∫ t in u i..u (i + 1), F ((i : ℝ) / (N : ℝ)) := by
          rw [intervalIntegral.integral_const]
          -- Cell length is (i+1)/N - i/N = 1/N
          have h_cell_len : u (i + 1) - u i = 1 / (N : ℝ) := by
            simp only [u]
            rw [div_sub_div_same]
            congr 1
            simp only [Nat.cast_add, Nat.cast_one]
            ring
          rw [h_cell_len]
          -- Convert smul to mul for complex numbers
          -- The scalar multiplication ℝ • ℂ is defined as (r : ℂ) * z
          -- Goal: (1/N : ℂ) * F(i/N) = ((1/N : ℝ) : ℂ) • F(i/N)
          -- For r : ℝ and z : ℂ, r • z = (r : ℂ) * z by Complex.real_smul
          simp only [one_div]
          rw [Complex.real_smul]
          congr 1
          -- Need: (N : ℂ)⁻¹ = ((N : ℝ)⁻¹ : ℂ)
          rw [Complex.ofReal_inv, Complex.ofReal_natCast]
      -- Step 2: Convert to norm of integral difference
        rw [h_const_integral, Complex.dist_eq]
      -- After rw: goal is ‖(∫ F t) - (∫ F(i/N))‖ ≤ ε/2/N
      -- Use norm_sub_rev to swap: ‖a - b‖ = ‖b - a‖
        rw [norm_sub_rev]
      -- Now goal is ‖(∫ F(i/N)) - (∫ F t)‖ ≤ ε/2/N

      -- Prove the bound directly
        have h_u_le : u i ≤ u (i + 1) := by
          simp only [u]
          apply div_le_div_of_nonneg_right _ (le_of_lt (by positivity : (0 : ℝ) < N))
          simp only [Nat.cast_add, Nat.cast_one]
          linarith
      -- First, combine the integrals
        have h_int_sub : (∫ t in u i..u (i + 1), F ((i : ℝ) / (N : ℝ))) -
            intervalIntegral F (u i) (u (i + 1)) volume =
            ∫ t in u i..u (i + 1), (F ((i : ℝ) / (N : ℝ)) - F t) := by
          symm
          apply intervalIntegral.integral_sub
          · apply Continuous.intervalIntegrable
            exact continuous_const
          · apply Continuous.intervalIntegrable
            exact hF_cont
        rw [h_int_sub]
      -- Goal: ‖∫ (F(i/N) - F t)‖ ≤ ε/2/N
      -- Use norm_integral_le_integral_norm: ‖∫ f‖ ≤ ∫ ‖f‖
        have h_norm_le : ‖∫ t in u i..u (i + 1), (F ((i : ℝ) / (N : ℝ)) - F t)‖ ≤
            ∫ t in u i..u (i + 1), ‖F ((i : ℝ) / (N : ℝ)) - F t‖ :=
          intervalIntegral.norm_integral_le_integral_norm h_u_le
        calc ‖∫ t in u i..u (i + 1), (F ((i : ℝ) / (N : ℝ)) - F t)‖
            ≤ ∫ t in u i..u (i + 1), ‖F ((i : ℝ) / (N : ℝ)) - F t‖ := h_norm_le
          _ ≤ ∫ t in u i..u (i + 1), (ε / 2) := by
              -- Use uniform continuity: for t ∈ [u i, u (i+1)], |F(i/N) - F(t)| < ε/2
              apply intervalIntegral.integral_mono_on h_u_le
              -- F pointwise bound integrable
              · apply Continuous.intervalIntegrable
                apply Continuous.norm
                apply Continuous.sub continuous_const hF_cont
              -- Constant integrable
              · exact intervalIntegrable_const
              -- Pointwise bound: ∀ x ∈ [u i, u (i+1)], ‖F(i/N) - F x‖ ≤ ε/2
              · intro t ht
                apply le_of_lt
                rw [← dist_eq_norm]
                -- Use uniform continuity
                have h_i_in : (i : ℝ) / (N : ℝ) ∈ Set.Icc 0 1 := by
                  constructor
                  · apply div_nonneg (Nat.cast_nonneg i); positivity
                  · have h_i_lt : i < N := Finset.mem_range.mp hi
                    apply le_of_lt
                    calc (i : ℝ) / (N : ℝ)
                        < (N : ℝ) / (N : ℝ) :=
                         div_lt_div_of_pos_right (Nat.cast_lt.mpr h_i_lt) (Nat.cast_pos.mpr hN_pos)
                      _ = 1 := by field_simp
                have h_t_in : t ∈ Set.Icc 0 1 := by
                  have h_i_lt : i < N := Finset.mem_range.mp hi
                  simp only [Set.mem_Icc, Set.mem_Icc, u] at ht ⊢
                  constructor
                  · calc (0 : ℝ)
                        ≤ (i : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg N)
                      _ ≤ t := ht.1
                  · calc t
                        ≤ ((i + 1) : ℝ) / (N : ℝ) := by
                          simp only [Nat.cast_add, Nat.cast_one] at ht ⊢
                          exact ht.2
                      _ ≤ (N : ℝ) / (N : ℝ) := by
                          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
                          have h_le : i + 1 ≤ N := Nat.lt_iff_add_one_le.mp h_i_lt
                          exact_mod_cast Nat.cast_le.mpr h_le
                      _ = 1 := by field_simp
                have h_dist : dist ((i : ℝ) / (N : ℝ)) t < δ := by
                  rw [Real.dist_eq, abs_sub_comm]
                  simp only [Set.mem_Icc, u, Nat.cast_add, Nat.cast_one] at ht
                  calc |t - (i : ℝ) / (N : ℝ)|
                      ≤ (((i : ℝ) + 1) / (N : ℝ)) - ((i : ℝ) / (N : ℝ)) := by
                        rw [abs_of_nonneg (by linarith : 0 ≤ t - (i : ℝ) / (N : ℝ))]
                        linarith
                    _ = 1 / (N : ℝ) := by field_simp; ring
                    _ < δ := by
                      simp only [hN_def]
                      convert h_mesh_bound using 2
                      simp only [Nat.cast_pow]
                exact hδ _ h_i_in _ h_t_in h_dist
          _ = (ε / 2) * (u (i + 1) - u i) := by
              rw [intervalIntegral.integral_const]
              simp only [smul_eq_mul, mul_comm]
          _ = (ε / 2) * (1 / (N : ℝ)) := by
              have hN_ne' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN_pos)
              simp only [u]
              field_simp [hN_ne']
              simp only [add_comm, Nat.cast_add, Nat.cast_one]
              ring
          _ = ε / 2 / N := by ring
      _ = N * (ε / 2 / N) := by simp [Finset.sum_const, Finset.card_range]
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  -- Now show the original goal follows from calc_result
  -- The original goal is: ‖∫ f x - (1/p^n) * ∑ f(m/p^n)‖ < ε
  -- Goal already has: ‖(∫ (t : ℝ) in 0..1, f ↑t) - 1 / ↑p ^ n * ∑ m, f ↑(↑m.val / ↑p ^ n)‖ < ε
  -- Direct approach: show the expressions match via auxiliary lemmas
  have h_integral_eq : (∫ t in (0:ℝ)..(1:ℝ), f (QuotientAddGroup.mk t)) =
      ∑ i ∈ Finset.range N, intervalIntegral F (u i) (u (i + 1)) volume := by
    simp only [hN_def] at h_partition ⊢
    exact h_partition
  have h_sum_eq' : (1 / (p^n : ℂ)) * ∑ m : ZMod (p^n), f ((m.val : ℝ) / (p^n : ℝ) : 𝕋) =
      ∑ i ∈ Finset.range N, (1 / (N : ℂ)) * F ((i : ℝ) / (N : ℝ)) := by
    -- Step 1: Convert f to F using h_sum_eq
    rw [h_sum_eq]
    -- Step 2: Convert p^n to N (N = p^n by definition, so ZMod (p^n) = ZMod N definitionally)
    -- Use show to make the type explicit, then simp handles the rest
    show (1 / (p^n : ℂ)) * ∑ m : ZMod N, F (m.val / p^n) =
         ∑ i ∈ Finset.range N, (1 / (N : ℂ)) * F ((i : ℝ) / (N : ℝ))
    -- Now convert the coercions: p^n to N
    -- Note: ↑p ^ n vs ↑(p ^ n) - need Nat.cast_pow to unify
    have h_pn_eq_N : (p : ℂ) ^ n = (N : ℂ) := by simp only [hN_def, Nat.cast_pow]
    have h_pn_eq_N_real : (p : ℝ) ^ n = (N : ℝ) := by simp only [hN_def, Nat.cast_pow]
    simp only [h_pn_eq_N, h_pn_eq_N_real]
    rw [h_zmod_range, h_dist_eq]
  rw [h_integral_eq, h_sum_eq']
  exact calc_result
/-- The Main Result: Integral of non-constant fourier is zero -/
lemma integral_fourier_of_ne_zero (k : ℤ) (hk : k ≠ 0) :
    ∫ (x : 𝕋), fourier k x = 0 := by
  -- Choose prime p (say 2)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- Get N such that k mod 2^n ≠ 0 for all n ≥ N
  obtain ⟨N, hN⟩ := eventually_ne_zero_mod_prime_power 2 k hk
  -- The Riemann sums are eventually zero
  have h_sum_zero : ∀ᶠ n in Filter.atTop,
      (1 / (2^n : ℂ)) * ∑ m : ZMod (2^n), fourier k ((m.val : ℝ) / (2^n : ℝ) : 𝕋) = 0 := by
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hkmod : (k : ZMod (2 ^ n)) ≠ 0 := hN n hn
    have hsum0 : ∑ m : ZMod (2 ^ n), fourier k ((m.val : ℝ) / (2 ^ n : ℝ) : 𝕋) = 0 :=
      riemann_sum_zero 2 n k hkmod
    rw [hsum0]
    ring
  -- Convergence of Riemann sums to the integral
  have h_conv := riemann_sum_converges_to_integral (fourier k) 2
  -- Eventual zero implies the limit is zero
  have h_tendsto_zero : Filter.Tendsto
      (fun n => (1 / (2^n : ℂ)) * ∑ m : ZMod (2^n), fourier k ((m.val : ℝ) / (2^n : ℝ) : 𝕋))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.congr' (h_sum_zero.mono (fun n hn => hn.symm))
  -- Uniqueness of limits (ℂ is T2Space/Hausdorff)
  exact tendsto_nhds_unique h_conv h_tendsto_zero
-- LINE 5054-5077: MODIFY fourierCoeff_fourier_eq
lemma fourierCoeff_fourier_eq (m n : ℤ) :
    _root_.fourierCoeff (fourier m : 𝕋 → ℂ) n = if m = n then 1 else 0 := by
  unfold _root_.fourierCoeff
  simp only [smul_eq_mul]
  conv_lhs => arg 2; ext t; rw [← fourier_add]
  by_cases h : m = n
  · -- Case m = n: already done (lines 5063-5069)
    subst h
    simp only [neg_add_cancel, ite_true]
    -- Goal: integral haarAddCircle (fourier 0) = 1
    -- fourier 0 = 1 as continuous maps, so integral = 1
    have : (fourier 0 : C(𝕋, ℂ)) = 1 := by ext x; simp [fourier_zero]
    rw [this, ContinuousMap.coe_one]
    -- haarAddCircle is a probability measure, so integral of 1 = 1
    show ∫ _ : 𝕋, (1 : ℂ) ∂AddCircle.haarAddCircle = 1
    rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
  · -- Case m ≠ n: USE THE NEW LEMMA!
    simp only [h, ite_false]
    have hk : (-n) + m ≠ 0 := by omega
    -- Convert between haarAddCircle and volume (they're the same for T=1)
    have h_measure_eq : (AddCircle.haarAddCircle : Measure 𝕋) = volume := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp only [ENNReal.ofReal_one, one_smul]
    rw [h_measure_eq]
    exact integral_fourier_of_ne_zero ((-n) + m) hk
--LINE 5088-5131: MODIFY fourierCoeff_toCircle
lemma fourierCoeff_toCircle (P : TrigPolyℤ) (n : ℤ) :
    _root_.fourierCoeff (P.toCircle : 𝕋 → ℂ) n = P n := by
  -- Steps 1-6: Already done (lines 5097-5124)
  unfold _root_.fourierCoeff
  simp only [TrigPolyℤ.toCircle, ContinuousMap.coe_mk]
  simp_rw [Finset.smul_sum, smul_eq_mul]
  -- Rearrange: fourier(-n) x * (P m * fourier m x) = P m * (fourier(-n) x * fourier m x)
  conv_lhs => arg 2; ext x; arg 2; ext m; rw [mul_comm (P m), ← mul_assoc, mul_comm]
  -- Prove integrability for each term (fourier functions are continuous on compact space)
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have h_int : ∀ i ∈ P.support, Integrable (fun x : 𝕋 => P i * ((fourier (-n)) x * (fourier i) x))
      AddCircle.haarAddCircle := fun i _ => by
    apply Integrable.const_mul
    -- Continuous function on compact space with finite measure is integrable
    have hcont : Continuous (fun x : 𝕋 => (fourier (-n)) x * (fourier i) x) :=
      (fourier (-n)).continuous.mul (fourier i).continuous
    -- Use: LocallyIntegrableOn univ + isCompact univ → IntegrableOn univ = Integrable
    have hli : LocallyIntegrableOn (fun x => (fourier (-n)) x * (fourier i) x) Set.univ
        AddCircle.haarAddCircle :=
      (hcont.locallyIntegrable (μ := AddCircle.haarAddCircle)).locallyIntegrableOn Set.univ
    rw [← integrableOn_univ]
    exact hli.integrableOn_isCompact isCompact_univ
  rw [MeasureTheory.integral_finset_sum _ h_int]
  -- Pull out the constant P m from the integral: ∫ P m * f = P m * ∫ f
  simp_rw [MeasureTheory.integral_const_mul]
  -- Step 7: The integral ∫ fourier(-n) * fourier(m) = δ_{m,n}
  have h_orth : ∀ m : ℤ, ∫ a : 𝕋, (fourier (-n)) a * (fourier m) a ∂AddCircle.haarAddCircle =
      if m = n then 1 else 0 := by
    intro m
    conv_lhs => arg 2; ext a; rw [← fourier_add]
    -- Now we have ∫ fourier(-n + m)
    by_cases h : m = n
    · simp only [h, neg_add_cancel, ite_true]
      have hf0 : (fourier 0 : C(𝕋, ℂ)) = 1 := by ext x; simp [fourier_zero]
      rw [hf0, ContinuousMap.coe_one]
      -- Convert function form to notation form for integral_const
      show ∫ _ : 𝕋, (1 : ℂ) ∂AddCircle.haarAddCircle = 1
      rw [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul]
    · simp only [h, ite_false]
      have hne : -n + m ≠ 0 := by omega
      have h_measure_eq : (AddCircle.haarAddCircle : Measure 𝕋) = volume := by
        rw [AddCircle.volume_eq_smul_haarAddCircle]; simp only [ENNReal.ofReal_one, one_smul]
      rw [h_measure_eq]
      exact integral_fourier_of_ne_zero (-n + m) hne
  simp_rw [h_orth]
  -- Step 8: Collapse sum using Kronecker delta (REPLACES sorry at line 5131)
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · -- n ∉ P.support means P n = 0 by definition of support
    exact (Finsupp.notMem_support_iff.mp hn).symm
/-- PROFINITE ANALOGY LEMMA 2: toCircle is injective via Fourier coefficient extraction. -/
lemma TrigPolyℤ.toCircle_injective : Function.Injective TrigPolyℤ.toCircle := by
  intro P Q hPQ
  ext n
  -- Goal: P n = Q n

  -- Use Fourier coefficient extraction (from Mathlib's AddCircle theory)
  have h1 : _root_.fourierCoeff (P.toCircle : 𝕋 → ℂ) n = P n := fourierCoeff_toCircle P n
  have h2 : _root_.fourierCoeff (Q.toCircle : 𝕋 → ℂ) n = Q n := fourierCoeff_toCircle Q n
  -- From hPQ : P.toCircle = Q.toCircle, we get their Fourier coefficients are equal
  have h_eq : _root_.fourierCoeff (P.toCircle : 𝕋 → ℂ) n =
              _root_.fourierCoeff (Q.toCircle : 𝕋 → ℂ) n := by
    rw [hPQ]
  -- Combine: P n = fourierCoeff (P.toCircle) n = fourierCoeff (Q.toCircle) n = Q n
  rw [← h1, h_eq, h2]

/-! ### Riesz-Markov-Kakutani Construction for Λ -/

/-! ### Riesz-Markov-Kakutani Construction -/

-- PLACEHOLDER: Will move Riesz-Markov construction here after reorganization

/-! ### Fejér and Dirichlet Kernels -/

/-- The Dirichlet kernel D_N(θ) = ∑_{k=-N}^N e^{2πikθ} as a trigonometric polynomial.
    This is just the sum of all Fourier basis elements from -N to N. -/
noncomputable def dirichletKernel (N : ℕ) : TrigPolyℤ :=
  (Finset.Icc (-N : ℤ) N).sum (fun j => Finsupp.single j (1 : ℂ))

/-- The Fejér kernel K_N is the normSq of the Dirichlet kernel. -/
noncomputable def fejerKernel (N : ℕ) : TrigPolyℤ :=
  TrigPolyℤ.normSq (dirichletKernel N)

lemma dirichletKernel_apply (N : ℕ) (k : ℤ) :
    dirichletKernel N k = if k ∈ Finset.Icc (-N : ℤ) N then 1 else 0 := by
  unfold dirichletKernel
  classical
  simp only [Finsupp.finset_sum_apply]
  by_cases h : k ∈ Finset.Icc (-N : ℤ) N
  · simp only [h, if_true]
    rw [Finset.sum_eq_single k]
    · simp [Finsupp.single_apply]
    · intro b hb hbk
      simp [Finsupp.single_apply, hbk]
    · intro hk
      contradiction
  · simp only [h, if_false]
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finsupp.single_apply]
    by_cases hjk : j = k
    · subst hjk
      contradiction
    · simp [hjk]

lemma dirichletKernel_support (N : ℕ) :
    (dirichletKernel N).support ⊆ Finset.Icc (-N : ℤ) N := by
  intro k hk
  rw [Finsupp.mem_support_iff, dirichletKernel_apply] at hk
  by_cases h : k ∈ Finset.Icc (-N : ℤ) N
  · exact h
  · simp [h] at hk


end FourierBochner
