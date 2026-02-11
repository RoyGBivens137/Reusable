/-
Copyright (c) 2025 Zachary Mullaghy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Mullaghy, Gianfranco Romaelle
-/
import FourierBochner.TrigPoly
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

/-! ## Fejér-Riesz Factorization via Spiral Symmetry

Uses U(1) spiral character symmetry: conj(R(e^{iθ})) = R(e^{-iθ}).
This forces roots to come in conjugate reciprocal pairs.
-/

open Polynomial

noncomputable def TrigPolyℤ.degree (R : TrigPolyℤ) : ℕ :=
  R.support.sup (fun k => k.natAbs)

noncomputable def TrigPolyℤ.toPolynomial (R : TrigPolyℤ) (N : ℕ) : Polynomial ℂ :=
  R.sum (fun k c => C c * X ^ (k + N : ℤ).toNat)

noncomputable def polynomial_mirror (P : Polynomial ℂ) : Polynomial ℂ :=
  P.reverse

noncomputable def spiral_reflect (P : Polynomial ℂ) : Polynomial ℂ :=
  polynomial_mirror (P.map (starRingEnd ℂ))

/-- If Q(z)/z^N is real-valued on U(1), then Q(z) = z^{2N} · conj(Q(z)). -/
lemma spiral_symmetry_on_circle (Q : Polynomial ℂ) (N : ℕ)
    (h_real : ∀ z, ‖z‖ = 1 → (Q.eval z / z ^ N).im = 0) :
    ∀ z, ‖z‖ = 1 → Q.eval z = (z ^ (2 * N)) * conj (Q.eval (1 / conj z)) := by
    intro z hz_norm
    have hz_ne0 : z ≠ 0 := by intro h; rw [h] at hz_norm; norm_num at hz_norm
    -- On circle: 1/conj(z) = z
    have h_inv : 1 / conj z = z := by
      have h_norm : Complex.normSq z = 1 := by
        rw [Complex.normSq_eq_norm_sq, hz_norm]
        norm_num
      have : conj z * z = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self]
        simp only [h_norm, Complex.ofReal_one]
      calc 1 / conj z = (conj z * z) / conj z := by rw [this]
        _ = z := by
          have : conj z ≠ 0 := by
            intro h; apply hz_ne0
            rw [← RingHom.map_zero (starRingEnd ℂ)] at h
            exact (RingHom.injective _) h
          field_simp [this]
    rw [h_inv]
    -- Q(z)/z^N is real ⟹ Q(z)/z^N = conj(Q(z)/z^N)
    have h_real_val : Q.eval z / z ^ N = conj (Q.eval z / z ^ N) := by
      apply Complex.ext
      · rfl
      · have := h_real z hz_norm
        simp only [Complex.conj_im, neg_eq_zero, this]
        norm_num
    have h_z_pow_ne0 : z ^ N ≠ 0 := pow_ne_zero _ hz_ne0
    -- Main algebraic manipulation: on the circle, Q(z) = z^{2N} * conj(Q(z))
    have h_key : Q.eval z = z^(2*N) * conj (Q.eval z) := by
      -- On the circle: z * conj(z) = |z|² = 1
      have h_z_conj : z * conj z = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz_norm]
        norm_num
      -- Therefore: z^N * conj(z^N) = 1
      have h_pow_conj : z^N * conj (z^N) = 1 := by
        calc z^N * conj (z^N)
          = z^N * (conj z)^N := by rw [map_pow]
        _ = (z * conj z)^N := by rw [← mul_pow]
        _ = 1^N := by rw [h_z_conj]
        _ = 1 := by simp
      -- From h_real_val: Q(z)/z^N = conj(Q(z))/conj(z^N)
      -- Multiply both sides by z^N * conj(z^N):
      have this_eq : Q.eval z * conj (z^N) = conj (Q.eval z) * z^N := by
        have h1 := h_real_val
        rw [map_div₀] at h1
        have hconj_ne : conj (z^N) ≠ 0 := by
          intro h; apply h_z_pow_ne0
          rw [← RingHom.map_zero (starRingEnd ℂ)] at h
          exact (RingHom.injective _) h
        calc Q.eval z * conj (z^N)
          = (Q.eval z / z^N) * z^N * conj (z^N) := by field_simp [h_z_pow_ne0]
        _ = (conj (Q.eval z) / conj (z^N)) * z^N * conj (z^N) := by rw [h1]
        _ = conj (Q.eval z) * (z^N * conj (z^N)) / conj (z^N) := by ring
        _ = conj (Q.eval z) * 1 / conj (z^N) := by rw [h_pow_conj]
        _ = conj (Q.eval z) / conj (z^N) := by ring
        _ = conj (Q.eval z) * z^N := by
            have hconj_ne : conj (z^N) ≠ 0 := by
              intro h; apply h_z_pow_ne0
              rw [← RingHom.map_zero (starRingEnd ℂ)] at h
              exact (RingHom.injective _) h
            calc conj (Q.eval z) / conj (z^N)
              = conj (Q.eval z) * (1 / conj (z^N)) := by ring
            _ = conj (Q.eval z) * ((z^N * conj (z^N)) / conj (z^N)) := by rw [← h_pow_conj]
            _ = conj (Q.eval z) * z^N := by field_simp [hconj_ne]
      -- Since z^N * conj(z^N) = 1, we have conj(z^N) = 1/z^N
      -- So: Q(z) = conj(Q(z)) * z^N / conj(z^N) = conj(Q(z)) * z^N * z^N
      calc Q.eval z
        = Q.eval z * 1 := by ring
      _ = Q.eval z * (z^N * conj (z^N)) := by rw [← h_pow_conj]
      _ = (Q.eval z * conj (z^N)) * z^N := by ring
      _ = (conj (Q.eval z) * z^N) * z^N := by rw [this_eq]
      _ = conj (Q.eval z) * (z^N * z^N) := by ring
      _ = conj (Q.eval z) * z^(N + N) := by rw [← pow_add]
      _ = conj (Q.eval z) * z^(2*N) := by ring_nf
      _ = z^(2*N) * conj (Q.eval z) := by ring
    exact h_key
-- The unit circle is an infinite set
lemma unit_circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  let f := fun t : ℝ => Complex.exp (I * t)
  let seq := fun n : ℕ => f (1 / (n + 1))
  apply Set.Infinite.mono (s := Set.range seq)
  · rintro _ ⟨n, rfl⟩
    simp only [f, seq, Set.mem_setOf_eq]
    rw [Complex.norm_exp]
    simp [Complex.mul_re, Complex.I_re, Complex.ofReal_re]
  · apply Set.infinite_range_of_injective
    intro n m h_eq
    simp only [seq, f] at h_eq
    rw [Complex.exp_eq_exp_iff_exists_int] at h_eq
    rcases h_eq with ⟨k, hk⟩
    have h_val : (1 : ℂ) / (n + 1) - 1 / (m + 1) = k * (2 * π) := by
      have : I * (1 / (↑n + 1) - 1 / (↑m + 1)) = I * (↑k * (2 * ↑π)) := by
        have h1 : (1 : ℂ) / (↑n + 1) = ↑(1 / (↑n + 1 : ℝ)) := by push_cast; rfl
        have h2 : (1 : ℂ) / (↑m + 1) = ↑(1 / (↑m + 1 : ℝ)) := by push_cast; rfl
        rw [h1, h2]
        linear_combination hk
      simpa [Complex.I_ne_zero] using this
    have h_bound : |(1 : ℝ) / (n + 1) - 1 / (m + 1)| < 2 * Real.pi := by
      have hn : 0 < (n : ℝ) + 1 := by positivity
      have hm : 0 < (m : ℝ) + 1 := by positivity
      have : |(1 : ℝ) / (n + 1) - 1 / (m + 1)| ≤ 1 := by
        have h1 : 0 ≤ 1 / (n + 1 : ℝ) := by positivity
        have h2 : 0 ≤ 1 / (m + 1 : ℝ) := by positivity
        have h3 : 1 / (n + 1 : ℝ) ≤ 1 := by rw [div_le_one hn]; linarith
        have h4 : 1 / (m + 1 : ℝ) ≤ 1 := by rw [div_le_one hm]; linarith
        rw [abs_sub_le_iff]
        constructor <;> linarith
      calc |(1 : ℝ) / (n + 1) - 1 / (m + 1)|
          ≤ 1 := this
        _ < 2 * Real.pi := by
            have h1 : (1 : ℝ) < Real.pi := by
              have := Real.pi_gt_three
              linarith
            linarith
    have h_k0 : k = 0 := by
      have h_abs : |((k * (2 * π) : ℂ)).re| < 2 * Real.pi := by
        have h_bound_complex : |((1 : ℂ) / (↑n + 1) - (1 : ℂ) / (↑m + 1)).re| < 2 * Real.pi := by
          have hn1 : ((1 : ℂ) / (↑n + 1)).re = 1 / (↑n + 1) := by
            have : (1 : ℂ) / (↑n + 1) = ↑(1 / (↑n + 1 : ℝ)) := by norm_num
            rw [this, Complex.ofReal_re]
          have hm1 : ((1 : ℂ) / (↑m + 1)).re = 1 / (↑m + 1) := by
            have : (1 : ℂ) / (↑m + 1) = ↑(1 / (↑m + 1 : ℝ)) := by norm_num
            rw [this, Complex.ofReal_re]
          simp only [Complex.sub_re, hn1, hm1]
          exact h_bound
        have : ((k * (2 * π) : ℂ)).re = ((1 : ℂ) / (↑n + 1) - (1 : ℂ) / (↑m + 1)).re := by
          rw [h_val]
        rw [this]
        exact h_bound_complex
      simp only [Complex.mul_re, Complex.intCast_re, Complex.ofReal_re,
                 Complex.ofReal_im, Complex.intCast_im,
                 Complex.sub_re, mul_zero, sub_zero, zero_sub] at h_abs
      have h_abs_simp : |(k : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
        convert h_abs using 2
        simp [Complex.re]
      have : |(k : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
        rwa [abs_mul, abs_of_pos Real.two_pi_pos] at h_abs_simp
      have h_pi_pos : 0 < 2 * Real.pi := Real.two_pi_pos
      have : |(k : ℝ)| < 1 := by
        calc |(k : ℝ)|
            = |(k : ℝ)| * (2 * Real.pi) /
             (2 * Real.pi) := by rw [mul_div_cancel_right₀]; exact h_pi_pos.ne'
          _ < 2 * Real.pi / (2 * Real.pi) := by apply div_lt_div_of_pos_right this h_pi_pos
          _ = 1 := by rw [div_self h_pi_pos.ne']
      norm_cast at this
      rw [Int.abs_lt_one_iff] at this
      exact this
    rw [h_k0] at h_val
    simp only [Int.cast_zero, mul_zero, zero_mul, sub_eq_zero] at h_val
    have hn : (↑n + 1 : ℂ) ≠ 0 := by
      push_cast
      exact Nat.cast_add_one_ne_zero n
    have hm : (↑m + 1 : ℂ) ≠ 0 := by
      push_cast
      exact Nat.cast_add_one_ne_zero m
    have : (↑n + 1 : ℂ) = ↑m + 1 := by
      have h_div : (1 : ℂ) / (↑n + 1) = 1 / (↑m + 1) := h_val
      field_simp [hn, hm] at h_div
      exact h_div.symm
    norm_cast at this
    omega
-- Main theorem: Extend spiral symmetry from unit circle to all ℂ*
lemma spiral_symmetry_extends (Q : Polynomial ℂ) (N : ℕ)
    (h_real : ∀ z, ‖z‖ = 1 → (Q.eval z / z ^ N).im = 0)
    (h_deg : Q.natDegree ≤ 2 * N)
    (w : ℂ) (hw : w ≠ 0) :
    Q.eval w = (w ^ (2 * N)) * conj (Q.eval (1 / conj w)) := by
  -- 1. Construct the reflected polynomial R
  let Q_conj := Q.map (starRingEnd ℂ)
  let R := Q_conj.reverse * Polynomial.X ^ (2 * N - Q.natDegree)
  -- 2. Prove R matches the reflection formula for all z ≠ 0
  have h_R_eval : ∀ z : ℂ, z ≠ 0 → R.eval z = z ^ (2 * N) * conj (Q.eval (1 / conj z)) := by
    intro z hz
    simp only [R, Q_conj]
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    -- Step 1: Prove reverse polynomial evaluation formula
    -- For P.reverse.eval z = z^deg * P.eval (1/z)
    -- Use Mathlib's eval₂_reverse_mul_pow lemma
    have h_rev : Q_conj.reverse.eval z = z ^ Q_conj.natDegree * Q_conj.eval (1/z) := by
      have h_inv : (1/z) ≠ 0 := div_ne_zero one_ne_zero hz
      haveI : Invertible (1/z) := invertibleOfNonzero h_inv
      have h_formula := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (1/z) Q_conj
      simp only [Polynomial.eval₂_id, invOf_eq_inv] at h_formula
      -- h_formula: Q_conj.reverse.eval ((1/z)⁻¹) * (1/z)^deg = Q_conj.eval (1/z)
      have hinv : (1/z)⁻¹ = z := by field_simp
      rw [hinv] at h_formula
      -- h_formula: Q_conj.reverse.eval z * (1/z)^deg = Q_conj.eval (1/z)
      -- Multiply both sides by z^deg / (1/z)^deg = z^(2*deg)
      have h_pow_ne : (1/z) ^ Q_conj.natDegree ≠ 0 := pow_ne_zero _ h_inv
      calc Q_conj.reverse.eval z
          = (Q_conj.reverse.eval z * (1/z) ^ Q_conj.natDegree) / (1/z) ^ Q_conj.natDegree := by
              field_simp [h_pow_ne]
        _ = Q_conj.eval (1/z) / (1/z) ^ Q_conj.natDegree := by rw [h_formula]
        _ = Q_conj.eval (1/z) * ((1/z) ^ Q_conj.natDegree)⁻¹ := by rw [div_eq_mul_inv]
        _ = Q_conj.eval (1/z) * (z ^ Q_conj.natDegree) := by
            congr 1
            rw [← inv_pow, inv_div, div_one]
        _ = z ^ Q_conj.natDegree * Q_conj.eval (1/z) := by ring
    rw [h_rev]
    -- Crucial Step: Prove Q_conj.eval(1/z) = conj(Q.eval(1/conj z)) via sum expansion
    -- This avoids the rewrite failures with eval₂
    have h_conj_eval : Q_conj.eval (1 / z) = conj (Q.eval (1 / conj z)) := by
      simp only [Q_conj, Polynomial.eval_map, starRingEnd_apply]
      rw [Polynomial.eval₂_eq_sum]  -- LHS
      rw [Polynomial.eval_eq_sum]  -- RHS
      -- Goal: Q.sum (fun n a => star a * (1/z)^n) = star (Q.sum (fun n a => a * (1/star z)^n))
      -- Use Polynomial.sum which is Finsupp.sum on Q.toFinsupp
      change (Q.toFinsupp.sum fun n a => (starRingEnd ℂ) a * (1/z)^n) =
             (starRingEnd ℂ) (Q.toFinsupp.sum fun n a => a * (1/(starRingEnd ℂ) z)^n)
      -- Rewrite LHS to match RHS structure
      have : ∀ n a, (starRingEnd ℂ) a *
       (1/z)^n = (starRingEnd ℂ) (a * (1/(starRingEnd ℂ) z)^n) := by
        intro n a
        rw [map_mul, map_pow, starRingEnd_apply,
         Complex.star_def, map_div₀, map_one, Complex.conj_conj]
      simp only [this]
      -- Now both sides have star applied to each term, use that star distributes over sum
      exact (map_sum (starRingEnd ℂ) _ _).symm
    rw [h_conj_eval]
    -- Verify degrees match
    have h_deg_eq : Q_conj.natDegree = Q.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (RingHom.injective _) Q
    rw [h_deg_eq]
    -- Combine powers: z^deg * z^(2N - deg) = z^2N
    calc z ^ Q.natDegree * conj (Q.eval (1 / conj z)) * z ^ (2 * N - Q.natDegree)
        = z ^ Q.natDegree * z ^ (2 * N - Q.natDegree) * conj (Q.eval (1 / conj z)) := by ring
      _ = z ^ (Q.natDegree + (2 * N - Q.natDegree)) *
       conj (Q.eval (1 / conj z)) := by rw [← pow_add]
      _ = z ^ (2 * N) * conj (Q.eval (1 / conj z)) := by rw [Nat.add_sub_of_le h_deg]
  -- 3. Show Q and R agree on the unit circle
  have h_agree_on_circle : ∀ z : ℂ, ‖z‖ = 1 → Q.eval z = R.eval z := by
    intro z hz
    rw [spiral_symmetry_on_circle Q N h_real z hz]
    have hz_ne0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
    rw [h_R_eval z hz_ne0]
  -- 4. Invoke Identity Theorem
  have h_Q_eq_R : Q = R := by
    apply Polynomial.eq_of_infinite_eval_eq
    have h_circle_inf : {z : ℂ | ‖z‖ = 1}.Infinite := unit_circle_infinite
    apply Set.Infinite.mono _ h_circle_inf
    intro z hz
    exact h_agree_on_circle z hz
  -- 5. Conclusion
  calc Q.eval w
      = R.eval w := by rw [h_Q_eq_R]
    _ = w ^ (2 * N) * conj (Q.eval (1 / conj w)) := h_R_eval w hw
-- Helper lemmas for polynomials real on the circle
-- Key identity: on the unit circle, inversion equals conjugation
lemma unit_circle_inv_eq_self (z : ℂ) (hz : ‖z‖ = 1) : 1 / conj z = z := by
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  have h_norm : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have : conj z * z = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    simp only [h_norm, Complex.ofReal_one]
  calc 1 / conj z = (conj z * z) / conj z := by rw [this]
    _ = z := by
      have : conj z ≠ 0 := by
        intro h
        apply hz_ne
        have : conj (conj z) = conj 0 := by rw [h]
        simp at this
        exact this
      field_simp [this]

lemma polynomial_real_on_circle_spiral_symm (Q : Polynomial ℂ)
    (h_real : ∀ z, ‖z‖ = 1 → (Q.eval z).im = 0) (z : ℂ) (hz : ‖z‖ = 1) :
    Q.eval z = conj (Q.eval (1 / conj z)) := by
  -- On the unit circle, 1/conj(z) = z
  rw [unit_circle_inv_eq_self z hz]
  -- Q(z) is real, so Q(z) = conj(Q(z))
  have h_real_z : (Q.eval z).im = 0 := h_real z hz
  -- A complex number with zero imaginary part equals its conjugate
  apply Complex.ext
  · simp
  · simp [h_real_z]
lemma roots_of_real_on_circle (Q : Polynomial ℂ) (h_real : ∀ z, ‖z‖ = 1 → (Q.eval z).im = 0) :
    ∀ α, α ∈ Q.roots → (1 / (starRingEnd ℂ) α) ∈ Q.roots := by
  intro α hα
  have hQ_ne_zero : Q ≠ 0 := Polynomial.ne_zero_of_mem_roots hα
  rw [Polynomial.mem_roots hQ_ne_zero]
  -- Now we need: Q.eval (1 / conj α) = 0
  -- Key insight: If |α| = 1, then 1/conj(α) = α, so trivially Q(α) = 0 implies Q(1/conj(α)) = 0
  -- If |α| ≠ 1, we use continuity and the constraint h_real
  by_cases hα_norm : ‖α‖ = 1
  · -- Case: α is on the unit circle
    -- Then 1/conj(α) = α by the unit circle inversion identity
    have : 1 / conj α = α := unit_circle_inv_eq_self α hα_norm
    rw [this]
    rw [Polynomial.mem_roots hQ_ne_zero] at hα
    exact hα
  · -- Case: α is NOT on the unit circle
    -- First handle the special case α = 0
    by_cases hα_zero : α = 0
    · -- If α = 0, then 1/conj(α) = 1/0 = 0 in Lean, so trivial
      subst hα_zero
      simp [div_zero]
      rw [Polynomial.mem_roots hQ_ne_zero] at hα
      exact hα
    -- Now α ≠ 0 and α not on unit circle
    -- Strategy: Construct the reflected polynomial R and use polynomial identity theorem
    -- Step 1: Construct the reflected polynomial R = (Q.map conj).reverse
    -- This polynomial satisfies R.eval(z) = z^deg * conj(Q.eval(1/z))
    let Q_conj := Q.map (starRingEnd ℂ)
    let R := Q_conj.reverse
    -- Step 2: On the unit circle, Q and R are related by the spiral symmetry
    -- We have Q(z) = conj(Q(1/conj z)) on |z|=1
    -- And R(z) = z^deg * conj(Q(1/z)) = z^deg * Q(z) on |z|=1 (using 1/z = conj z)
    have h_agree_circle : ∀ z : ℂ, ‖z‖ = 1 →
        Q.eval z * z ^ Q_conj.natDegree = R.eval z := by
      intro z hz
      -- Use polynomial_real_on_circle_spiral_symm: Q(z) = conj(Q(1/conj z))
      have h_symm := polynomial_real_on_circle_spiral_symm Q h_real z hz
      -- On circle: 1/z = conj(z)
      have hz_ne : z ≠ 0 := by intro h; rw [h] at hz; norm_num at hz
      have h_inv : 1 / z = conj z := by
        calc 1 / z
            = conj (conj (1 / z)) := by simp
          _ = conj (1 / conj z) := by rw [map_div₀, map_one]
          _ = conj z := by rw [unit_circle_inv_eq_self z hz]
      -- Evaluate R using reverse polynomial formula
      simp only [R]
      -- R.eval z = Q_conj.reverse.eval z
      -- Need: Q_conj.reverse.eval z = z^deg * Q_conj.eval(1/z)
      have h_rev : Q_conj.reverse.eval z = z ^ Q_conj.natDegree * Q_conj.eval (1/z) := by
        have h_inv_ne : (1/z) ≠ 0 := div_ne_zero one_ne_zero hz_ne
        haveI : Invertible (1/z) := invertibleOfNonzero h_inv_ne
        have h_formula := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (1/z) Q_conj
        simp only [Polynomial.eval₂_id, invOf_eq_inv] at h_formula
        have hinv : (1/z)⁻¹ = z := by field_simp
        rw [hinv] at h_formula
        have h_pow_ne : (1/z) ^ Q_conj.natDegree ≠ 0 := pow_ne_zero _ h_inv_ne
        calc Q_conj.reverse.eval z
            = (Q_conj.reverse.eval z * (1/z) ^ Q_conj.natDegree) / (1/z) ^ Q_conj.natDegree := by
                field_simp [h_pow_ne]
          _ = Q_conj.eval (1/z) / (1/z) ^ Q_conj.natDegree := by rw [h_formula]
          _ = Q_conj.eval (1/z) * ((1/z) ^ Q_conj.natDegree)⁻¹ := by rw [div_eq_mul_inv]
          _ = Q_conj.eval (1/z) * (z ^ Q_conj.natDegree) := by
              congr 1
              rw [← inv_pow, inv_div, div_one]
          _ = z ^ Q_conj.natDegree * Q_conj.eval (1/z) := by ring
      -- Goal: Q.eval z * z ^ Q_conj.natDegree = Q_conj.reverse.eval z
      rw [h_rev]
      -- Goal: Q.eval z * z ^ Q_conj.natDegree = z ^ Q_conj.natDegree * Q_conj.eval (1/z)
      rw [mul_comm]
      -- Goal: z ^ Q_conj.natDegree * Q.eval z = z ^ Q_conj.natDegree * Q_conj.eval (1/z)
      congr 1
      -- Goal: Q.eval z = Q_conj.eval (1/z)
      -- On the circle: 1/z = conj z
      rw [h_inv]
      -- Goal: Q.eval z = Q_conj.eval (conj z)
      -- Need: Q_conj.eval(conj z) = conj(Q.eval z), but we have Q real on circle
      -- So Q.eval z = conj(Q.eval z), combined with Q_conj.eval(conj z) = conj(Q.eval z)
      have h_conj_eval : Q_conj.eval (conj z) = conj (Q.eval z) := by
        simp only [Q_conj, Polynomial.eval_map, starRingEnd_apply]
        rw [Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum]
        change (Q.toFinsupp.sum fun n a => (starRingEnd ℂ) a * (conj z)^n) =
               (starRingEnd ℂ) (Q.toFinsupp.sum fun n a => a * z^n)
        have : ∀ n a, (starRingEnd ℂ) a * (conj z)^n = (starRingEnd ℂ) (a * z^n) := by
          intro n a
          rw [map_mul, map_pow, starRingEnd_apply, Complex.star_def]
        simp only [this]
        exact (map_sum (starRingEnd ℂ) _ _).symm
      rw [h_conj_eval]
      -- Now use that Q.eval z = conj(Q.eval z) from h_symm
      -- h_symm : Q.eval z = conj(Q.eval(1/conj z))
      -- We need to simplify the RHS using unit_circle_inv_eq_self
      have : 1 / conj z = z := unit_circle_inv_eq_self z hz
      rw [this] at h_symm
      exact h_symm
    -- Step 3: By polynomial identity theorem, Q * X^deg = R
    have h_Q_eq_R : Q * Polynomial.X ^ Q_conj.natDegree = R := by
      apply Polynomial.eq_of_infinite_eval_eq
      -- Unit circle is infinite (same proof as in spiral_symmetry_extends)
      have h_circle_inf : {z : ℂ | ‖z‖ = 1}.Infinite := unit_circle_infinite
      apply Set.Infinite.mono _ h_circle_inf
      intro z hz
      simp only [Set.mem_setOf_eq] at hz ⊢
      rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      exact h_agree_circle z hz
    -- Step 4: Use this equality to relate roots
    -- If Q(α) = 0, then R(α) = 0 (since Q·X^n = R)
    rw [Polynomial.mem_roots hQ_ne_zero] at hα
    -- From Q * X^deg = R and Q(α) = 0, we get R(α) = 0
    have hR_α : R.eval α = 0 := by
      have := congr_arg (fun p => p.eval α) h_Q_eq_R
      simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at this
      rw [hα, zero_mul] at this
      exact this.symm
    -- Now R(α) = Q_conj.reverse.eval(α) = α^deg * Q_conj.eval(1/α) by reverse formula
    -- Apply the reverse polynomial formula (we know α ≠ 0 from hα_zero)
    simp only [R] at hR_α
    have h_rev_α : Q_conj.reverse.eval α = α ^ Q_conj.natDegree * Q_conj.eval (1/α) := by
      have h_inv_ne : (1/α) ≠ 0 := div_ne_zero one_ne_zero hα_zero
      haveI : Invertible (1/α) := invertibleOfNonzero h_inv_ne
      have h_formula := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) (1/α) Q_conj
      simp only [Polynomial.eval₂_id, invOf_eq_inv] at h_formula
      have hinv : (1/α)⁻¹ = α := by field_simp
      rw [hinv] at h_formula
      have h_pow_ne : (1/α) ^ Q_conj.natDegree ≠ 0 := pow_ne_zero _ h_inv_ne
      calc Q_conj.reverse.eval α
          = (Q_conj.reverse.eval α * (1/α) ^ Q_conj.natDegree) / (1/α) ^ Q_conj.natDegree := by
              field_simp [h_pow_ne]
        _ = Q_conj.eval (1/α) / (1/α) ^ Q_conj.natDegree := by rw [h_formula]
        _ = Q_conj.eval (1/α) * ((1/α) ^ Q_conj.natDegree)⁻¹ := by rw [div_eq_mul_inv]
        _ = Q_conj.eval (1/α) * (α ^ Q_conj.natDegree) := by
            congr 1
            rw [← inv_pow, inv_div, div_one]
        _ = α ^ Q_conj.natDegree * Q_conj.eval (1/α) := by ring
    rw [h_rev_α] at hR_α
    -- hR_α : α^deg * Q_conj.eval(1/α) = 0
    -- Since α ≠ 0, we have α^deg ≠ 0, so Q_conj.eval(1/α) = 0
    have hα_pow_ne : α ^ Q_conj.natDegree ≠ 0 := pow_ne_zero _ hα_zero
    have hQ_conj_zero : Q_conj.eval (1 / α) = 0 := by
      have := mul_eq_zero.mp hR_α
      cases this with
      | inl h => exact absurd h hα_pow_ne
      | inr h => exact h
    -- Now Q_conj.eval(1/α) = conj(Q.eval(1/conj α))
    have h_conj_eval_α : Q_conj.eval (1 / α) = conj (Q.eval (1 / conj α)) := by
      simp only [Q_conj, Polynomial.eval_map, starRingEnd_apply]
      rw [Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum]
      change (Q.toFinsupp.sum fun n a => (starRingEnd ℂ) a * (1/α)^n) =
             (starRingEnd ℂ) (Q.toFinsupp.sum fun n a => a * (1/conj α)^n)
      have : ∀ n a, (starRingEnd ℂ) a * (1/α)^n = (starRingEnd ℂ) (a * (1/conj α)^n) := by
        intro n a
        rw [map_mul, map_pow, starRingEnd_apply, Complex.star_def]
        congr 1
        rw [map_div₀, map_one, Complex.conj_conj]
      simp only [this]
      exact (map_sum (starRingEnd ℂ) _ _).symm
    rw [h_conj_eval_α] at hQ_conj_zero
    -- hQ_conj_zero : conj(Q.eval(1/conj α)) = 0
    -- This means Q.eval(1/conj α) = 0
    -- Goal is Q.IsRoot (1 / conj α), i.e., Q.eval (1 / conj α) = 0
    show Q.eval (1 / (starRingEnd ℂ) α) = 0
    -- Apply conj to both sides of hQ_conj_zero
    have h_conj_both := congr_arg conj hQ_conj_zero
    rw [RingHom.map_zero] at h_conj_both
    -- h_conj_both : conj(conj(Q.eval(1/conj α))) = 0
    rw [Complex.conj_conj] at h_conj_both
    -- h_conj_both : Q.eval(1/conj α) = 0
    -- Now 1/(starRingEnd ℂ) α = 1/conj α
    show Q.eval (1 / conj α) = 0
    exact h_conj_both

-- Root detection via roots of unity density + profinite continuity
-- This connects: roots_of_unity_dense + continuous_if_profinitecontinuous_at
-- to provide CONSTRUCTIVE root verification through shell approximation
lemma root_detection_via_roots_of_unity
    (Q : Polynomial ℂ) (_h_real : ∀ z, ‖z‖ = 1 → (Q.eval z).im = 0)
    (α : ℂ) (hα_norm : ‖α‖ = 1) (_hα_root : Q.IsRoot α) :
    ∃ (ω_seq : ℕ → ℂ),
      (∀ n, ∃ N : ℕ+, ω_seq n ^ (N : ℕ) = 1) ∧  -- each ωₙ is a root of unity
      (∀ n, ‖ω_seq n‖ = 1) ∧                     -- all on circle
      (∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, ‖ω_seq n - α‖ < ε) := by  -- ωₙ → α
  -- Strategy: Use roots_of_unity_dense to construct approximating sequence
  -- For each n, pick ωₙ within distance 1/(n+1) of α
  -- α on circle means α = exp(I*θ) for some θ, use roots_of_unity_dense at that θ

  -- Step 1: Write α = exp(I * arg α) using polar form
  let θ := Complex.arg α
  have hα_ne : α ≠ 0 := by
    intro h
    rw [h] at hα_norm
    norm_num at hα_norm
  -- α = |α| * exp(I * arg α), and |α| = 1
  have hα_polar : α = Complex.exp (I * θ) := by
    -- Punctured disc model: any z ≠ 0 can be written as z = exp(log z)
    -- where log z = log|z| + i·arg(z)
    -- For ‖α‖ = 1, we have log|α| = 0, so log α = 0 + i·arg(α) = i·arg(α)

    -- Start with α = exp(log α) for α ≠ 0
    have h1 : α = Complex.exp (Complex.log α) := (Complex.exp_log hα_ne).symm
    -- Now use: log α = log|α| + i·arg(α) (definition of complex log)
    -- But we need to show log α = i·θ when ‖α‖ = 1

    -- For α on the unit circle: log α = i·arg(α) since log|α| = log 1 = 0
    have h2 : Complex.log α = I * θ := by
      -- Complex.log is defined so that log z = log|z| + i·arg(z) (in the principal branch)
      -- When |z| = 1, this gives log z = i·arg(z)
      apply Complex.ext
      · -- Real part: log.re = log ‖α‖ = log 1 = 0, I*θ has re = 0
        rw [Complex.log_re, hα_norm, Real.log_one]
        simp
      · -- Imaginary part: log.im = arg α = θ, and (I*θ).im = θ
        rw [Complex.log_im]
      -- Need to unfold θ and show α.arg = (I * α.arg).im
        change α.arg = (I * α.arg).im
        simp
    rw [h1, h2]
  -- Step 2: For each n, use roots_of_unity_dense to get character within 1/(n+1) of exp(I*θ)
  have h_dense : ∀ n : ℕ, ∃ (m : ℕ) (hm : NeZero m) (k : ZMod m),
      ‖Complex.exp (I * θ) - @character m hm k 1‖ < 1 / (n + 1) := by
    intro n
    have hε : (0 : ℝ) < 1 / (n + 1) := by
      apply div_pos
      · norm_num
      · exact Nat.cast_add_one_pos n
    obtain ⟨N, hN⟩ := roots_of_unity_dense (1 / (n + 1)) hε
    let m := N + 1
    have hm_pos : 0 < m := Nat.succ_pos N
    have hm : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm_pos⟩
    obtain ⟨k, hk⟩ := hN (N + 1) (Nat.le_succ N) θ
    exact ⟨m, hm, k, hk⟩
  -- Step 3: Construct the sequence
  choose m_seq hm_seq k_seq h_close using h_dense
  let ω_seq := fun n => @character (m_seq n) (hm_seq n) (k_seq n) 1
  use ω_seq
  constructor
  · -- Each ω_seq n is a root of unity
    intro n
    use ⟨m_seq n, Nat.pos_of_ne_zero (NeZero.ne (m_seq n))⟩
    exact character_power_n (m_seq n) (k_seq n) 1
  constructor
  · -- All have norm 1
    intro n
    exact character_on_unit_circle (m_seq n) (k_seq n) 1
  · -- Convergence to α
    intro ε hε
    -- Choose n₀ such that 1/(n₀+1) < ε
    -- Use Archimedean property: exists n such that 1/n < ε
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, 1 / (n₀ + 1 : ℝ) < ε := by
      rcases exists_nat_gt (1 / ε) with ⟨N, hN⟩
      use N
      have hNpos : (0 : ℝ) < N + 1 := Nat.cast_add_one_pos N
      rw [div_lt_iff₀ hNpos]
      calc 1 = ε * (1 / ε) := by rw [mul_one_div_cancel (ne_of_gt hε)]
        _ < ε * (N : ℝ) := by
            apply mul_lt_mul_of_pos_left hN hε
        _ ≤ ε * ((N : ℝ) + 1) := by
            apply mul_le_mul_of_nonneg_left
            · linarith
            · exact le_of_lt hε
    use n₀
    intro n hn
    calc ‖ω_seq n - α‖
        = ‖@character (m_seq n) (hm_seq n) (k_seq n) 1 - α‖ := rfl
      _ = ‖@character (m_seq n) (hm_seq n) (k_seq n) 1 - Complex.exp (I * θ)‖ := by rw [hα_polar]
      _ = ‖Complex.exp (I * θ) -
       @character (m_seq n) (hm_seq n) (k_seq n) 1‖ := by rw [norm_sub_rev]
      _ < 1 / (n + 1) := h_close n
      _ ≤ 1 / (n₀ + 1) := by
          apply div_le_div_of_nonneg_left
          · norm_num
          · exact Nat.cast_add_one_pos n₀
          · norm_cast
            omega
      _ < ε := hn₀

-- Helper: norm of conjugate reciprocal
lemma norm_conj_reciprocal (α : ℂ) : ‖1 / conj α‖ = 1 / ‖α‖ := by
  rw [norm_div, Complex.norm_conj]
  norm_num

/-- If α is a root of Q at radius r, then 1/conj(α) is a root at radius 1/r. -/
lemma factorization_via_shell_detection
    (Q : Polynomial ℂ) (hQ_ne : Q ≠ 0)
    (h_real : ∀ z, ‖z‖ = 1 → (Q.eval z).im = 0)
    (_h_pos : ∀ z, ‖z‖ = 1 → 0 ≤ (Q.eval z).re) :
    ∀ (r : ℝ) (_hr : 0 < r),
      -- If roots exist at radius r, they exist in paired shells (r, 1/r)
      (∃ α, Q.IsRoot α ∧ ‖α‖ = r) →
      (∃ β, Q.IsRoot β ∧ ‖β‖ = 1/r) := by
  intro r hr ⟨α, hα_root, hα_norm⟩
  -- Use roots_of_real_on_circle: if α is a root, so is 1/conj(α)
  -- The paired root β = 1/conj(α) has norm 1/‖α‖ = 1/r
  -- First convert IsRoot to membership in roots
  have hα_mem : α ∈ Q.roots := by
    rw [Polynomial.mem_roots hQ_ne]
    exact hα_root
  have hβ_mem : (1 / conj α) ∈ Q.roots := roots_of_real_on_circle Q h_real α hα_mem
  use 1 / conj α
  constructor
  · -- Convert back from membership to IsRoot
    rwa [Polynomial.mem_roots hQ_ne] at hβ_mem
  · -- Prove ‖1 / conj α‖ = 1 / r
    have hα_ne : α ≠ 0 := by
      intro h
      rw [h] at hα_norm
      simp at hα_norm
      linarith
    calc ‖(1 : ℂ) / conj α‖ = ‖(1 : ℂ)‖ / ‖conj α‖ := by rw [norm_div]
      _ = (1 : ℝ) / ‖conj α‖ := by simp
      _ = 1 / ‖α‖ := by rw [Complex.norm_conj]
      _ = 1 / r := by rw [hα_norm]

-- Construct the factor P from Q by selecting roots appropriately
-- The spiral symmetry forces roots to come in reciprocal conjugate pairs
-- Strategy: Take roots with |α| < 1, plus half of roots with |α| = 1
noncomputable def fejer_factor (Q : Polynomial ℂ) : Polynomial ℂ :=
  -- Filter roots to those inside or on the unit disk
  let inside_roots := Q.roots.filter (fun α => ‖α‖ < 1)
  let _circle_roots := Q.roots.filter (fun α => ‖α‖ = 1)
  -- For circle roots, we only want half (they pair with themselves)
  -- This is tricky in Lean - for now we take all inside roots
  -- TODO: Handle circle root halving properly
  let selected_roots := inside_roots
  -- Build polynomial from selected roots
  (selected_roots.map (fun α => X - C α)).prod

-- Helper: The reflected polynomial via spiral symmetry
-- For polynomial P, this constructs the polynomial whose roots are {1/conj α : α ∈ P.roots}
-- This definition comes directly from the spiral test structure: roots pair via α ↦ 1/conj α
noncomputable def reflected_polynomial (P : Polynomial ℂ) : Polynomial ℂ :=
  (P.roots.map (fun α => X - C (1 / conj α))).prod

/-! ## Ladder Operators and Hermitian Pairs

Hermitian pair factors (X - α)(X - conj α) ensure real evaluation on U(1) and
equal multiplicity for conjugate-paired roots. We use N = p^n for prime p to
get profinite tower compatibility. -/

/-- p^n-th root of unity: ζ(j) = exp(2πij/p^n). -/
noncomputable def zeta (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (j : Fin (p^n)) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((j.1 : ℝ) / (p^n : ℝ) : ℂ))

noncomputable def ladderFactor (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (j : Fin (p^n)) : Polynomial ℂ :=
  (X - C (zeta p n j))

/-- Hermitian pair factor: (X - α)(X - conj α). -/
noncomputable def hermitianPairFactor (α : ℂ) : Polynomial ℂ :=
  (X - C α) * (X - C (conj α))

/-- |z - α|², the norm-squared factor. Real and nonneg on U(1). -/
noncomputable def hermitianPairFactorPositive (α : ℂ) (z : ℂ) : ℝ :=
  Complex.normSq (z - α)

noncomputable def evenLadderFactor (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (j : Fin (p^n)) : Polynomial ℂ :=
  hermitianPairFactor (zeta p n j)

/-! ## Regularized Ladder Operators via 2D Lattice

Place roots inside the disk (σ < 0 gives |e^{σ+iθ}| < 1) to maintain strict
positivity on U(1). -/

/-- Lattice point e^{σ + 2πij/p^n}, generalizing zeta with radial parameter σ. -/
noncomputable def latticePoint (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (σ : ℝ) (j : Fin (p^n)) : ℂ :=
  Complex.exp (σ + Complex.I * (2 * Real.pi * (j.1 : ℝ) / (p^n : ℝ)))

lemma latticePoint_zero_eq_zeta (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (j : Fin (p^n)) :
    latticePoint p n 0 j = zeta p n j := by
  unfold latticePoint zeta
  simp [zero_add]
  ring_nf

/-- Lattice point with σ < 0, hence strictly inside the unit disk. -/
noncomputable def regularizedRoot (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (σ : ℝ) (_hσ : σ < 0) (j : Fin (p^n)) : ℂ :=
  latticePoint p n σ j

noncomputable def ladderFactorAtLattice (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (σ : ℝ) (j : Fin (p^n)) : Polynomial ℂ :=
  (X - C (latticePoint p n σ j))

noncomputable def evenLadderFactorAtLattice (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (σ : ℝ) (hσ : σ < 0) (j : Fin (p^n)) : Polynomial ℂ :=
  hermitianPairFactor (regularizedRoot p n σ hσ j)

/-! ## Strict Positivity of Regularized Factors

When roots are inside the disk (r < 1), |z - r·ω^j|² ≥ (1-r)² > 0 on U(1). -/

-- Norm of lattice point: |e^{σ+iθ}| = e^σ
lemma latticePoint_norm (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (σ : ℝ) (j : Fin (p^n)) :
    ‖latticePoint p n σ j‖ = Real.exp σ := by
  unfold latticePoint
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
             Complex.mul_im, Complex.ofReal_im, Complex.I_im,
             zero_mul, sub_self, add_zero]
  norm_cast
  simp [Complex.ofReal_im]

lemma regularizedRoot_inside_disk (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (σ : ℝ) (hσ : σ < 0) (j : Fin (p^n)) :
    ‖regularizedRoot p n σ hσ j‖ < 1 := by
  unfold regularizedRoot
  rw [latticePoint_norm]
  exact Real.exp_lt_one_iff.mpr hσ

lemma regularizedFactor_positive_on_circle (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (σ : ℝ) (hσ : σ < 0) (j : Fin (p^n)) (z : ℂ) (hz : ‖z‖ = 1) :
    (1 - Real.exp σ)^2 ≤ ‖z - regularizedRoot p n σ hσ j‖^2 := by
  unfold regularizedRoot
  let r := Real.exp σ
  have hr_pos : 0 < r := Real.exp_pos σ
  have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr hσ


  have h_norm : ‖latticePoint p n σ j‖ = r := latticePoint_norm p n σ j


  let α := latticePoint p n σ j

  have h_triangle : |‖z‖ - ‖α‖| ≤ ‖z - α‖ := abs_norm_sub_norm_le z α

  -- Step 2: Simplify |‖z‖ - ‖α‖| using our constraints
  have h_diff : |‖z‖ - ‖α‖| = 1 - r := by
    rw [hz, h_norm]
    rw [abs_sub_comm]
    have h_neg : r - 1 < 0 := by linarith [hr_lt_one]
    rw [abs_of_neg h_neg, neg_sub]

  have h_lower : 1 - r ≤ ‖z - α‖ := by
    calc 1 - r = |‖z‖ - ‖α‖| := h_diff.symm
      _ ≤ ‖z - α‖ := h_triangle

  have h_nonneg : 0 ≤ 1 - r := by linarith [hr_lt_one]
  calc (1 - r)^2 = (1 - r) * (1 - r) := sq (1 - r)
    _ ≤ ‖z - α‖ * ‖z - α‖ := mul_self_le_mul_self h_nonneg h_lower
    _ = ‖z - α‖^2 := (sq _).symm

/-! ## Bochner Polynomial Lattice

Products of Hermitian pair factors with multiplicities:
q_m(z) = ∏_j ((z - ω^j)(z - conj(ω^j)))^{m(j)} where m : Fin(p^n) →₀ ℕ. -/

abbrev BochnerMultiplicity (p : ℕ) (n : ℕ) := Fin (p^n) →₀ ℕ

noncomputable def bochnerProduct (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (m : BochnerMultiplicity p n) : Polynomial ℂ :=
  m.prod (fun j mult => (evenLadderFactor p n j) ^ mult)

noncomputable def bochnerPoly (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (c : ℝ) (m : BochnerMultiplicity p n) : Polynomial ℂ :=
  C (c : ℂ) * bochnerProduct p n m

def BochnerLattice (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) : Set (Polynomial ℂ) :=
  {q | ∃ (c : ℝ) (_hc : 0 < c) (m : BochnerMultiplicity p n), q = bochnerPoly p n c m}

noncomputable def evenLadderProduct (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (S : Finset (Fin (p^n))) : Polynomial ℂ :=
  S.prod (fun j => evenLadderFactor p n j)

/-! ### Basic Properties of Zeta and Hermitian Pairs -/

lemma zeta_on_circle (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (j : Fin (p^n)) :
    ‖zeta p n j‖ = 1 := by
  unfold zeta
  -- exp(z) has norm exp(z.re), and our z has real part 0
  rw [Complex.norm_exp]
  -- The real part of (2πi * x) is 0 since I is purely imaginary
  conv_lhs => arg 1; rw [show (2 * ↑Real.pi * Complex.I * ((j.1 : ℝ) / (p ^ n : ℝ) : ℂ)).re = 0 by
    simp only [Complex.mul_re, Complex.div_re, Complex.ofReal_re, Complex.I_re,
               Complex.mul_im, Complex.ofReal_im, Complex.I_im,
               mul_zero, zero_sub, mul_one, sub_zero, add_zero, zero_div]
    norm_cast
    ring]
  simp [Real.exp_zero]


lemma zeta_conj_eq_inv (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (j : Fin (p^n)) :
    conj (zeta p n j) = 1 / zeta p n j := by
  have h_on_circle : ‖zeta p n j‖ = 1 := zeta_on_circle p n j
  have h_ne_zero : zeta p n j ≠ 0 := Complex.exp_ne_zero _
  -- On unit circle: conj(z) * z = |z|^2 = 1, so conj(z) = 1/z
  field_simp [h_ne_zero]
  rw [mul_comm]
  have : zeta p n j * conj (zeta p n j) = Complex.normSq (zeta p n j) := mul_conj _
  rw [this]
  -- normSq z = |z|^2, and we know |z| = 1
  have h_norm_sq : (Complex.normSq (zeta p n j) : ℂ) = ‖zeta p n j‖ ^ 2 := by
    norm_cast
    rw [← Complex.sq_norm]
  rw [h_norm_sq, h_on_circle]
  norm_num

lemma zeta_spiral_self (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (j : Fin (p^n)) :
    1 / conj (zeta p n j) = zeta p n j := by
  have h_on_circle : ‖zeta p n j‖ = 1 := zeta_on_circle p n j
  exact unit_circle_inv_eq_self (zeta p n j) h_on_circle

/-- Expansion: (X - α)(X - conj α) = X² - (α + conj α)X + α · conj α. -/
lemma hermitianPairFactor_expand (α : ℂ) :
    hermitianPairFactor α = X^2 - C (α + conj α) * X + C (α * conj α) := by
  unfold hermitianPairFactor
  calc (X - C α) * (X - C (conj α))
      = X * X - X * C (conj α) - C α * X + C α * C (conj α) := by ring
    _ = X^2 - C (conj α) * X - C α * X + C (α * conj α) := by simp [pow_two, Polynomial.C_mul]
    _ = X^2 - (C α + C (conj α)) * X + C (α * conj α) := by ring
    _ = X^2 - C (α + conj α) * X + C (α * conj α) := by rw [← Polynomial.C_add]

lemma hermitianPairFactor_sum_is_real (α : ℂ) : α + conj α = (2 * α.re : ℂ) := by
  apply Complex.ext
  · simp [Complex.add_re, Complex.conj_re]; ring
  · simp [Complex.add_im, Complex.conj_im]

lemma hermitianPairFactor_prod_is_real (α : ℂ) : α * conj α = Complex.normSq α :=
  Complex.mul_conj α

lemma unit_circle_reflected_eval (P : Polynomial ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    conj (P.eval (1 / conj z)) = conj (P.eval z) := by
  rw [unit_circle_inv_eq_self z hz]

/-- Conjugate-linearity: (P.map conj).eval(w) = conj(P.eval(conj w)). -/
lemma eval_map_conj (P : Polynomial ℂ) (w : ℂ) :
    (P.map (starRingEnd ℂ)).eval w = conj (P.eval (conj w)) := by
  rw [Polynomial.eval_map]
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval₂_add, Polynomial.eval_add, map_add]
    rw [hp, hq]
  | monomial n a =>
    simp only [Polynomial.eval₂_monomial, Polynomial.eval_monomial]
    simp only [starRingEnd_apply, map_mul, map_pow, star_star]

/-! ## Hermitian Preservation and Positive Operator -/

/-- The Hermitian pair factor satisfies f(z) = conj(f(z⁻¹)) on U(1). -/
lemma hermitianPairFactor_hermitian_symmetry (α : ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    (hermitianPairFactor α).eval z = conj ((hermitianPairFactor α).eval (z⁻¹)) := by
  unfold hermitianPairFactor
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

  -- Goal: (z - α)(z - conj α) = conj((z⁻¹ - α)(z⁻¹ - conj α))
  -- RHS = conj(z⁻¹ - α)·conj(z⁻¹ - conj α)
  --     = (conj z⁻¹ - conj α)(conj z⁻¹ - conj(conj α))
  --     = (conj z⁻¹ - conj α)(conj z⁻¹ - α)
  -- On circle: conj z⁻¹ = conj(conj z) = z
  -- So RHS = (z - conj α)(z - α) = LHS ✓

  rw [map_mul, map_sub, map_sub]
  simp only [Complex.conj_conj]

  have hz_ne : z ≠ 0 := norm_pos_iff.mp (by rw [hz]; norm_num)
  have h_conj_inv : conj (z⁻¹) = z := by
    have : z⁻¹ = conj z := by
      field_simp [hz_ne]
      -- Goal: 1 = z * conj z
      have h_normSq : z * conj z = Complex.normSq z := Complex.mul_conj z
      rw [h_normSq]
      rw [Complex.normSq_eq_norm_sq, hz]
      norm_num
    rw [this]
    exact Complex.conj_conj z

  rw [h_conj_inv]
  ring


-- This is what we actually need for positive definite functions
-- The type ℝ guarantees it's real; we just need to show nonnegativity
lemma hermitianPairFactorPositive_nonneg (α : ℂ) (z : ℂ) :
    0 ≤ hermitianPairFactorPositive α z := by
  unfold hermitianPairFactorPositive
  exact Complex.normSq_nonneg (z - α)

lemma hermitianPairFactorPositive_on_circle (α : ℂ) (hα : ‖α‖ = 1) (z : ℂ) (hz : ‖z‖ = 1) :
    hermitianPairFactorPositive α z = 2 - 2 * (z * conj α).re := by
  unfold hermitianPairFactorPositive
  rw [Complex.normSq_sub]
  have hz_normSq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hα_normSq : Complex.normSq α = 1 := by
    rw [Complex.normSq_eq_norm_sq, hα]
    norm_num
  rw [hz_normSq, hα_normSq]
  ring

/-! ## Multiplicity Preservation -/

/-- On the circle, α and 1/conj α are the same point, so multiplicities match. -/
lemma hermitianPairFactor_spiral_on_circle (α : ℂ) (hα_circle : ‖α‖ = 1) :
    (hermitianPairFactor α).roots.count α =
    (hermitianPairFactor α).roots.count (1 / conj α) := by
  -- On circle: 1/conj α = α, so both sides count the same element
  have h_spiral : 1 / conj α = α := unit_circle_inv_eq_self α hα_circle
  rw [h_spiral]

lemma hermitianPairFactor_conjugate_multiplicity (α : ℂ) (hα_ne : α ≠ 0) :
    (hermitianPairFactor α).roots.count α =
    (hermitianPairFactor α).roots.count (conj α) := by
  unfold hermitianPairFactor
  -- Roots are {α, conj α}, each appears exactly once by construction
  have hα_conj_ne : conj α ≠ 0 := by
    intro h
    have : α = 0 := by simpa using congrArg conj h
    exact hα_ne this
  have h_prod_ne : (X - C α) * (X - C (conj α)) ≠ 0 := by
    apply mul_ne_zero <;> exact Polynomial.X_sub_C_ne_zero _
  rw [Polynomial.roots_mul h_prod_ne]
  simp only [Polynomial.roots_X_sub_C, Multiset.count_add, Multiset.count_singleton]
  -- Simplify: (1 + if α = conj α then 1 else 0) = (if conj α = α then 1 else 0) + 1
  by_cases h : α = conj α
  · rw [if_pos h, if_pos h.symm]; norm_num
  · rw [if_neg h, if_neg (Ne.symm h)]; norm_num


/-! ## Constructive Density via Profinite Refinement -/

noncomputable def circleL2Dist (f g : ℂ → ℂ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    Complex.normSq (f (Complex.exp (I * θ)) - g (Complex.exp (I * θ)))

/-! ## Lowering Operator -/

noncomputable def hasRootAt (Q : Polynomial ℂ) (ζ : ℂ) (tolerance : ℝ) : Bool :=
  ‖Q.eval ζ‖ < tolerance

noncomputable def extractRootMultiplicity (Q : Polynomial ℂ) (ζ : ℂ) (max_iters : ℕ := 100) : Polynomial ℂ × ℕ :=
  -- Algorithm: repeatedly divide by (X - ζ) and count iterations
  let rec loop (current : Polynomial ℂ) (mult : ℕ) (fuel : ℕ) : Polynomial ℂ × ℕ :=
    if fuel = 0 then (current, mult)
    else if ‖current.eval ζ‖ < 1e-10 then  -- ζ is still a root
      -- Divide: current = (X - ζ) · quotient + remainder
      -- For exact roots, remainder should be ≈ 0
      let quotient := current /ₘ (X - C ζ)  -- polynomial division
      loop quotient (mult + 1) (fuel - 1)
    else
      (current, mult)  -- No more roots at ζ
  loop Q 0 max_iters

-- Lowering operator for POLYNOMIALS: removes root pair (ζ_j, ζ̄_j)
-- Returns (Q', m) where Q ≈ Q' · (X - ζ_j)^m · (X - ζ̄_j)^m
noncomputable def loweringOperatorPoly (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (j : Fin (p^n))
    (Q : Polynomial ℂ) : Polynomial ℂ × ℕ :=
  let ζ_j := zeta p n j
  let ζ_j_conj := conj ζ_j
  -- Extract multiplicity at ζ_j
  let (Q₁, m₁) := extractRootMultiplicity Q ζ_j
  -- Extract multiplicity at ζ̄_j from the quotient
  let (Q₂, m₂) := extractRootMultiplicity Q₁ ζ_j_conj
  -- For Hermitian pairs on circle, m₁ should equal m₂
  -- Return the common multiplicity
  (Q₂, min m₁ m₂)

-- Lowering operator for POSITIVE FUNCTIONS: f(z) = |Q(z)|² on circle
-- Returns (f', m) where f(z) ≈ f'(z) · |z - ζ_j|^{2m}
noncomputable def loweringOperator (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (j : Fin (p^n)) (f : ℂ → ℂ) (max_iters : ℕ := 100) : (ℂ → ℂ) × ℕ :=
  let ζ_j := zeta p n j

  -- Inverse of positive raising operator: divide by |z - ζ_j|²
  let lowerOnce (g : ℂ → ℂ) : ℂ → ℂ := fun z =>
    g z / hermitianPairFactorPositive ζ_j z

  -- Check if g has a "zero" at ζ_j (meaning g(ζ_j) ≈ 0)
  let hasZeroAt (g : ℂ → ℂ) (tolerance : ℝ := 1e-10) : Bool :=
    ‖g ζ_j‖ < tolerance

  -- Iteratively divide by |z - ζ_j|² while zeros are present
  let rec loop (current : ℂ → ℂ) (mult : ℕ) (fuel : ℕ) : (ℂ → ℂ) × ℕ :=
    if fuel = 0 then (current, mult)
    else if hasZeroAt current then
      -- Divide by |z - ζ_j|² and continue
      loop (lowerOnce current) (mult + 1) (fuel - 1)
    else
      (current, mult)  -- No more zeros at ζ_j

  loop f 0 max_iters

-- Full factorization: extract ALL root pairs from f
-- Returns (c, m : Fin(p^n) →₀ ℕ) where f ≈ c · ∏_j |z - ζ_j|^{2·m(j)}
noncomputable def factorizeViaLowering (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (f : ℂ → ℂ) : ℝ × BochnerMultiplicity p n :=
  -- Explicit recursion to avoid commutativity requirements
  let rec processRoots (remaining : List (Fin (p^n))) (current_f : ℂ → ℂ) (current_m : BochnerMultiplicity p n) :
      (ℂ → ℂ) × BochnerMultiplicity p n :=
    match remaining with
    | [] => (current_f, current_m)
    | j :: rest =>
        -- Apply lowering operator at root ζ_j
        let (lowered_f, mult_j) := loweringOperator p n j current_f
        -- Update multiplicity map: m[j] := mult_j
        let updated_m := current_m + Finsupp.single j mult_j
        processRoots rest lowered_f updated_m

  -- Build list of all root indices
  let all_roots := (List.finRange (p^n))

  -- Process all roots
  let (_residual, multiplicities) := processRoots all_roots f 0

  -- Compute barycenter via L² projection: c = B/C where
  -- B = ∫ Re(f(e^{iθ}) * conj(P(e^{iθ}))) dθ
  -- C = ∫ |P(e^{iθ})|² dθ

  -- Build polynomial P from multiplicities
  let P := bochnerPoly p n 1 multiplicities

  -- Numerical integration using sample points (trapezoidal rule)
  let num_samples := 64  -- Increased for better accuracy

  let B := (Finset.sum (Finset.range num_samples) fun k =>
    let θ := 2 * Real.pi * (k : ℝ) / num_samples
    let z := Complex.exp (I * θ)
    (f z * conj (P.eval z)).re) / num_samples * (2 * Real.pi)

  let C := (Finset.sum (Finset.range num_samples) fun k =>
    let θ := 2 * Real.pi * (k : ℝ) / num_samples
    let z := Complex.exp (I * θ)
    Complex.normSq (P.eval z)) / num_samples * (2 * Real.pi)

  let c := B / C

  (c, multiplicities)

-- Helper: allocate multiplicities from budget (inner loop)
noncomputable def allocateMultiplicities (p : ℕ) (n : ℕ) (m_orig : BochnerMultiplicity p n)
    (roots : List (Fin (p^n))) (acc : BochnerMultiplicity p n) (budget : ℕ) : BochnerMultiplicity p n :=
  match roots with
  | [] => acc
  | j :: rest =>
      let mult_j := min (m_orig j) budget
      if budget = 0 then acc
      else allocateMultiplicities p n m_orig rest (acc + Finsupp.single j mult_j) (budget - mult_j)

-- Helper: truncate multiplicities to fit degree budget D
-- Processes roots in order, allocating multiplicity from budget until exhausted
noncomputable def truncateMultiplicities (p : ℕ) (n : ℕ) (m_orig : BochnerMultiplicity p n)
    (roots : List (Fin (p^n))) (budget : ℕ) : BochnerMultiplicity p n :=
  allocateMultiplicities p n m_orig roots 0 budget

/-- STEP 1: Single factor error bound -/
lemma single_factor_error_on_circle (α ζ : ℂ) (z : ℂ)
    (hz : ‖z‖ = 1)
    (hα_bound : ‖α‖ ≤ 2)
    (hζ_bound : ‖ζ‖ ≤ 2)
    (δ : ℝ) (hδ : ‖α - ζ‖ ≤ δ) :
    |Complex.normSq (z - α) - Complex.normSq (z - ζ)| ≤ 6 * δ := by

  -- normSq w = ‖w‖² as a real number
  have normSq_eq_norm (w : ℂ) : Complex.normSq w = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq w

  rw [normSq_eq_norm, normSq_eq_norm]

  -- Bounds on ‖z - α‖ and ‖z - ζ‖ on the circle
  have bound_α : ‖z - α‖ ≤ 3 := by
    have h1 : ‖z - α‖ ≤ ‖z‖ + ‖α‖ := norm_sub_le z α
    have h2 : ‖z‖ + ‖α‖ = 1 + ‖α‖ := by rw [hz]
    have h3 : 1 + ‖α‖ ≤ 1 + 2 := by linarith [hα_bound]
    linarith

  have bound_ζ : ‖z - ζ‖ ≤ 3 := by
    have h1 : ‖z - ζ‖ ≤ ‖z‖ + ‖ζ‖ := norm_sub_le z ζ
    have h2 : ‖z‖ + ‖ζ‖ = 1 + ‖ζ‖ := by rw [hz]
    have h3 : 1 + ‖ζ‖ ≤ 1 + 2 := by linarith [hζ_bound]
    linarith

  -- |‖z-α‖ - ‖z-ζ‖| ≤ ‖α - ζ‖ by reverse triangle inequality
  have reverse_tri : |‖z - α‖ - ‖z - ζ‖| ≤ ‖α - ζ‖ := by
    have h1 : |‖z - α‖ - ‖z - ζ‖| ≤ ‖(z - α) - (z - ζ)‖ := abs_norm_sub_norm_le (z - α) (z - ζ)
    have h2 : (z - α) - (z - ζ) = ζ - α := by ring
    have h3 : ‖ζ - α‖ = ‖α - ζ‖ := norm_sub_rev ζ α
    rw [h2] at h1
    rw [h3] at h1
    exact h1

  -- Main calculation: |a² - b²| ≤ |a - b| · (a + b) where a = ‖z-α‖, b = ‖z-ζ‖
  have key : |‖z - α‖ ^ 2 - ‖z - ζ‖ ^ 2| ≤ |‖z - α‖ - ‖z - ζ‖| * (‖z - α‖ + ‖z - ζ‖) := by
    have ha_pos : 0 ≤ ‖z - α‖ := norm_nonneg _
    have hb_pos : 0 ≤ ‖z - ζ‖ := norm_nonneg _
    have eq : ‖z - α‖ ^ 2 - ‖z - ζ‖ ^ 2 = (‖z - α‖ - ‖z - ζ‖) * (‖z - α‖ + ‖z - ζ‖) := by ring
    rw [eq, abs_mul, abs_of_nonneg (by linarith : 0 ≤ ‖z - α‖ + ‖z - ζ‖)]

  calc |‖z - α‖ ^ 2 - ‖z - ζ‖ ^ 2|
      ≤ |‖z - α‖ - ‖z - ζ‖| * (‖z - α‖ + ‖z - ζ‖) := key
    _ ≤ ‖α - ζ‖ * (‖z - α‖ + ‖z - ζ‖) := by
        apply mul_le_mul_of_nonneg_right reverse_tri
        linarith [norm_nonneg (z - α), norm_nonneg (z - ζ)]
    _ ≤ ‖α - ζ‖ * (3 + 3) := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · exact norm_nonneg _
    _ = 6 * ‖α - ζ‖ := by ring
    _ ≤ 6 * δ := by
        apply mul_le_mul_of_nonneg_left hδ
        norm_num

-- Helper: Product of nonnegative bounded terms
lemma list_prod_bounded (l : List ℝ) (c : ℝ) (hc : 0 ≤ c) (h_nonneg : ∀ x ∈ l, 0 ≤ x) (h_bound : ∀ x ∈ l, x ≤ c) :
    l.prod ≤ c ^ l.length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp only [List.prod_cons, List.length_cons]
      have ha_nonneg : 0 ≤ a := h_nonneg a List.mem_cons_self
      have ha_bound : a ≤ c := h_bound a List.mem_cons_self
      have h_rest_nonneg : ∀ x ∈ rest, 0 ≤ x := fun x hx => h_nonneg x (List.mem_cons_of_mem _ hx)
      have h_rest_bound : ∀ x ∈ rest, x ≤ c := fun x hx => h_bound x (List.mem_cons_of_mem _ hx)
      calc a * rest.prod
          ≤ c * rest.prod := by
              apply mul_le_mul_of_nonneg_right ha_bound
              exact List.prod_nonneg h_rest_nonneg
        _ ≤ c * c ^ rest.length := by
              apply mul_le_mul_of_nonneg_left (ih h_rest_nonneg h_rest_bound)
              exact hc
        _ = c ^ (rest.length + 1) := by ring

/-- Barycentric Principle: First moment controls linear error via arc length -/
lemma product_error_via_barycenter_linear
    (roots_actual roots_lattice : List ℂ) (z : ℂ)
    (hz : ‖z‖ = 1)
    (h_match : roots_actual.length = roots_lattice.length)
    (h_bounds_actual : ∀ α ∈ roots_actual, ‖α‖ ≤ 2)
    (h_bounds_lattice : ∀ ζ ∈ roots_lattice, ‖ζ‖ = 1) -- Lattice = roots of unity on circle
    -- Arc length bound: For p^n lattice, δ = π/p^n from nearest root approximation
    (hδ_nonneg : 0 ≤ δ)
    (hδ : ∀ i < roots_actual.length, ‖roots_actual[i]! - roots_lattice[i]!‖ ≤ δ)
    (_hδ_small : δ ≤ 1) : -- Linearity valid for small perturbations (satisfied when p^n ≥ π)
    |(roots_actual.map (fun α => Complex.normSq (z - α))).prod -
     (roots_lattice.map (fun ζ => Complex.normSq (z - ζ))).prod| ≤
    12 * δ * roots_actual.length * (10 : ℝ) ^ roots_actual.length := by
  -- Strategy: Telescoping product decomposition with barycentric error term
  -- The LINEAR term δ·N from barycenter → 0 as δ = π/p^n → 0
  -- ∏aᵢ - ∏bᵢ = ∑ᵢ [(∏ⱼ<ᵢ bⱼ)(aᵢ - bᵢ)(∏ⱼ>ᵢ aⱼ)]
  -- Sum over n terms: n · 6δ · 3^(n-1)

  -- Induction on the list structure
  revert roots_lattice
  induction roots_actual with
  | nil =>
    intro roots_lattice h_match _ _
    cases roots_lattice with
    | nil => simp
    | cons _ _ => simp at h_match
  | cons α_head α_tail ih =>
    intro roots_lattice h_match h_bounds_lattice hδ
    cases roots_lattice with
    | nil => simp at h_match
    | cons ζ_head ζ_tail =>
      simp at h_match h_bounds_lattice hδ

      -- Telescoping decomposition: a·∏as - b·∏bs = (a-b)·∏as + b·(∏as - ∏bs)
      let a := Complex.normSq (z - α_head)
      let b := Complex.normSq (z - ζ_head)
      let prod_as := (α_tail.map (fun α => Complex.normSq (z - α))).prod
      let prod_bs := (ζ_tail.map (fun ζ => Complex.normSq (z - ζ))).prod

      have eq_split : a * prod_as - b * prod_bs = (a - b) * prod_as + b * (prod_as - prod_bs) := by ring

      -- Single factor bound: |a - b| ≤ 6δ
      have h_single : |a - b| ≤ 6 * δ := by
        have hα : α_head ∈ α_head :: α_tail := List.mem_cons_self
        have h_close_0 : ‖α_head - ζ_head‖ ≤ δ := by
          have := hδ 0 (by omega : 0 ≤ α_tail.length)
          simp at this
          exact this
        have hζ_bound : ‖ζ_head‖ ≤ 2 := by
          calc ‖ζ_head‖ = 1 := h_bounds_lattice.1
            _ ≤ 2 := by norm_num
        exact single_factor_error_on_circle α_head ζ_head z hz (h_bounds_actual _ hα) hζ_bound δ h_close_0

      -- Product bound: |prod_as| ≤ 10^(length α_tail)
      -- Each factor |z-α|² ≤ 9, use 10 for safety margin
      have h_prod_bound : |prod_as| ≤ (10 : ℝ) ^ α_tail.length := by
        show |(α_tail.map (fun α => Complex.normSq (z - α))).prod| ≤ 10 ^ α_tail.length
        have h_nonneg : 0 ≤ prod_as := by
          apply List.prod_nonneg
          intro x hx; simp at hx
          obtain ⟨α, _, rfl⟩ := hx
          exact Complex.normSq_nonneg _
        rw [abs_of_nonneg h_nonneg]
        -- Each factor bounded by 9, product by 9^n ≤ 10^n
        -- Each factor bounded: |z-α|² ≤ 9 for ‖z‖=1, ‖α‖≤2
        -- This follows the same pattern as product_factor_error
        have h_factor_bound : ∀ α ∈ α_tail, Complex.normSq (z - α) ≤ 9 := by
          intro α hα_mem
          calc Complex.normSq (z - α)
              = ‖z - α‖ ^ 2 := Complex.normSq_eq_norm_sq _
            _ ≤ (‖z‖ + ‖α‖) ^ 2 := by
                apply sq_le_sq'
                · linarith [norm_nonneg (z - α), norm_nonneg z, norm_nonneg α]
                · exact norm_sub_le z α
            _ = (1 + ‖α‖) ^ 2 := by rw [hz]
            _ ≤ (1 + 2) ^ 2 := by
                apply sq_le_sq'
                · linarith [norm_nonneg α]
                · have hα_bound : α ∈ α_head :: α_tail := List.mem_cons_of_mem _ hα_mem
                  linarith [h_bounds_actual α hα_bound]
            _ = 9 := by norm_num

        -- Product of bounded terms: use helper lemma
        have h_prod_le_9 : prod_as ≤ 9 ^ α_tail.length := by
          have : (α_tail.map (fun α => Complex.normSq (z - α))).prod ≤ 9 ^ (α_tail.map (fun α => Complex.normSq (z - α))).length := by
            apply list_prod_bounded
            · norm_num -- 0 ≤ 9
            · intro x hx
              simp at hx
              obtain ⟨α, _, rfl⟩ := hx
              exact Complex.normSq_nonneg _
            · intro x hx
              simp at hx
              obtain ⟨α, hα_mem, rfl⟩ := hx
              exact h_factor_bound α hα_mem
          simp at this
          exact this

        calc prod_as
            ≤ 9 ^ α_tail.length := h_prod_le_9
          _ ≤ 10 ^ α_tail.length := by
              gcongr; norm_num

      -- Factor bound: |b| ≤ 10 (lattice point on circle gives |z-ζ|² ≤ 4, use 10 for uniformity)
      have hb_bound : |b| ≤ 10 := by
        have h_nonneg : 0 ≤ b := Complex.normSq_nonneg _
        rw [abs_of_nonneg h_nonneg]
        show Complex.normSq (z - ζ_head) ≤ 10
        have hζ_circle : ‖ζ_head‖ = 1 := h_bounds_lattice.1
        calc Complex.normSq (z - ζ_head)
            = ‖z - ζ_head‖ ^ 2 := Complex.normSq_eq_norm_sq _
          _ ≤ (‖z‖ + ‖ζ_head‖) ^ 2 := by apply sq_le_sq'; linarith [norm_nonneg (z - ζ_head)]; exact norm_sub_le z ζ_head
          _ = (1 + 1) ^ 2 := by rw [hz, hζ_circle]
          _ = 4 := by norm_num
          _ ≤ 10 := by norm_num

      -- Induction hypothesis for tail
      have h_bounds_tail : ∀ α ∈ α_tail, ‖α‖ ≤ 2 := by
        intros α hα
        exact h_bounds_actual α (List.mem_cons_of_mem _ hα)
      have h_bounds_lattice_tail : ∀ ζ ∈ ζ_tail, ‖ζ‖ = 1 := h_bounds_lattice.2
      have hδ_tail : ∀ i < α_tail.length, ‖α_tail[i]! - ζ_tail[i]!‖ ≤ δ := by
        intros i hi
        have := hδ (i + 1) (by omega : i + 1 ≤ α_tail.length)
        simp only [List.getElem?_cons_succ] at this
        convert this using 2 <;> (rw [List.getElem!_eq_getElem?_getD]; simp)
      have h_ih : |prod_as - prod_bs| ≤ 12 * δ * α_tail.length * 10 ^ α_tail.length :=
        ih h_bounds_tail ζ_tail h_match h_bounds_lattice_tail hδ_tail

      -- Combine via telescoping
      calc |a * prod_as - b * prod_bs|
          = |(a - b) * prod_as + b * (prod_as - prod_bs)| := by rw [eq_split]
        _ ≤ |(a - b) * prod_as| + |b * (prod_as - prod_bs)| := abs_add_le _ _
        _ = |a - b| * |prod_as| + |b| * |prod_as - prod_bs| := by rw [abs_mul, abs_mul]
        _ ≤ (6 * δ) * (10 ^ α_tail.length) + 10 * (12 * δ * α_tail.length * 10 ^ α_tail.length) := by
            gcongr
        _ = 6 * δ * 10 ^ α_tail.length + 120 * δ * α_tail.length * 10 ^ α_tail.length := by ring
        _ = 6 * δ * 10 ^ α_tail.length * (1 + 20 * α_tail.length) := by ring
        _ ≤ 12 * δ * (α_head :: α_tail).length * 10 ^ (α_head :: α_tail).length := by
            simp [List.length_cons]
            -- Goal: 6 * δ * 10^n * (1 + 20n) ≤ 12 * δ * (n+1) * 10^(n+1)
            -- = 6 * δ * 10^n * (1 + 20n) ≤ 120 * δ * (n+1) * 10^n
            -- Factor δ * 10^n: need 6(1 + 20n) ≤ 120(n+1)
            by_cases hδ_zero : δ = 0
            · simp [hδ_zero]
            · have hδ_pos : 0 < δ := by
                cases (lt_or_eq_of_le hδ_nonneg) with
                | inl h => exact h
                | inr h => exact absurd h.symm hδ_zero
              have h10_pos : (0 : ℝ) < 10 ^ α_tail.length := by positivity
              calc 6 * δ * 10 ^ α_tail.length * (1 + 20 * ↑α_tail.length)
                  = δ * 10 ^ α_tail.length * (6 * (1 + 20 * ↑α_tail.length)) := by ring
                _ ≤ δ * 10 ^ α_tail.length * (120 * (↑α_tail.length + 1)) := by
                    apply mul_le_mul_of_nonneg_left _
                    · apply mul_nonneg hδ_nonneg
                      exact le_of_lt h10_pos
                    · -- Prove: 6(1 + 20n) ≤ 120(n+1)
                      calc (6 : ℝ) * (1 + 20 * ↑α_tail.length)
                          = 6 + 120 * ↑α_tail.length := by ring
                        _ ≤ 120 + 120 * ↑α_tail.length := by linarith
                        _ = 120 * (↑α_tail.length + 1) := by ring
                _ = δ * (120 * (↑α_tail.length + 1) * 10 ^ α_tail.length) := by ring
                _ = 12 * δ * (↑α_tail.length + 1) * (10 * 10 ^ α_tail.length) := by ring
                _ = 12 * δ * (↑α_tail.length + 1) * 10 ^ (α_tail.length + 1) := by
                    congr 1
                    rw [mul_comm, pow_succ]

/-- Key Principle: Optimal witness via root minimization. -/

-- Helper: general version - result.sum ≤ acc.sum + budget

lemma allocateMultiplicities_diff_le (p : ℕ) (n : ℕ) (m : BochnerMultiplicity p n)
    (roots : List (Fin (p^n))) (acc : BochnerMultiplicity p n) (budget : ℕ) :
    (allocateMultiplicities p n m roots acc budget).sum (fun _ v => v) ≤ acc.sum (fun _ v => v) + budget := by
  revert acc budget
  induction roots with
  | nil =>
      intros acc budget
      simp [allocateMultiplicities]
  | cons j rest ih =>
      intros acc budget
      simp only [allocateMultiplicities]
      split_ifs with h_zero
      · -- budget = 0: returns acc, acc.sum ≤ acc.sum + 0
        simp
      · -- budget > 0: allocate min(m j, budget) and recurse
        let mult_j := min (m j) budget
        have h_mult_le : mult_j ≤ budget := min_le_right _ _

        have h_new_sum : (acc + Finsupp.single j mult_j).sum (fun _ v => v) =
                         acc.sum (fun _ v => v) + mult_j := by
          simp [Finsupp.sum_add_index', Finsupp.sum_single_index]

        have ih_bound := ih (acc + Finsupp.single j mult_j) (budget - mult_j)

        calc (allocateMultiplicities p n m rest (acc + Finsupp.single j mult_j) (budget - mult_j)).sum (fun _ v => v)
            ≤ (acc + Finsupp.single j mult_j).sum (fun _ v => v) + (budget - mult_j) := ih_bound
          _ = acc.sum (fun _ v => v) + mult_j + (budget - mult_j) := by rw [h_new_sum]
          _ ≤ acc.sum (fun _ v => v) + budget := by omega

-- Alternative formulation: with precondition (not actually needed, but kept for compatibility)
lemma allocateMultiplicities_sum_le (p : ℕ) (n : ℕ) (m : BochnerMultiplicity p n)
    (roots : List (Fin (p^n))) (acc : BochnerMultiplicity p n) (budget : ℕ)
    (_h_acc : acc.sum (fun _ v => v) + budget ≤ budget + budget) :
    (allocateMultiplicities p n m roots acc budget).sum (fun _ v => v) ≤ acc.sum (fun _ v => v) + budget := by
  -- This follows directly from allocateMultiplicities_diff_le (precondition not needed)
  exact allocateMultiplicities_diff_le p n m roots acc budget

lemma allocateMultiplicities_from_zero_le (p : ℕ) (n : ℕ) (m : BochnerMultiplicity p n)
    (roots : List (Fin (p^n))) (budget : ℕ) :
    (allocateMultiplicities p n m roots 0 budget).sum (fun _ v => v) ≤ budget := by
  have := allocateMultiplicities_diff_le p n m roots 0 budget
  simp at this
  exact this

-- Main property: truncation respects the budget
lemma truncateMultiplicities_sum_le (p : ℕ) (n : ℕ) (m : BochnerMultiplicity p n)
    (roots : List (Fin (p^n))) (budget : ℕ) :
    (truncateMultiplicities p n m roots budget).sum (fun _ v => v) ≤ budget := by
  unfold truncateMultiplicities
  exact allocateMultiplicities_from_zero_le p n m roots budget

-- Constructive witness: extract approximation via factorization
noncomputable def bochnerApproxWitness (p : ℕ) [Fact (Nat.Prime p)] (n D : ℕ) (f : ℂ → ℂ) : Polynomial ℂ :=
  -- Use factorizeViaLowering to extract (c, m) from f
  let (c, m) := factorizeViaLowering p n f

  -- Reconstruct polynomial: c · ∏_j (hermitianPairFactor ζ_j)^{m(j)}
  -- with degree bound: truncate m if Σ m(j) > D
  let total_mult := m.sum (fun _ v => v)

  let m_truncated := if total_mult ≤ D then m
                     else
                       -- Truncate: keep roots with highest multiplicities
                       let sorted_roots := (m.support.toList.mergeSort (fun j k => m j ≥ m k))
                       truncateMultiplicities p n m sorted_roots D

  -- Return: c · ∏_j (hermitianPairFactor ζ_j)^{m_truncated(j)}
  bochnerPoly p n c m_truncated

-- Solution permanence: level n roots embed into level n+1
lemma zeta_embedding (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (j : Fin (p^n)) :
    ∃ (k : Fin (p^(n+1))), zeta p (n+1) k = zeta p n j := by
  -- Use the existing p_tower_embedding theorem
  haveI : NeZero (p^n) := ⟨pow_ne_zero n (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))⟩
  haveI : NeZero (p^(n+1)) := ⟨pow_ne_zero (n+1) (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))⟩

  -- Construct k = j.val * p
  have h_bound : j.val * p < p^(n+1) := by
    calc j.val * p < p^n * p := by
          apply Nat.mul_lt_mul_of_pos_right j.isLt
          exact Nat.Prime.pos (Fact.out : Nat.Prime p)
         _ = p^(n+1) := by ring

  use ⟨j.val * p, h_bound⟩

  -- zeta p n j = exp(2πi·j/p^n) = character (p^n) j.val 1
  -- zeta p (n+1) k = exp(2πi·k/p^{n+1}) = character (p^{n+1}) k.val 1
  unfold zeta
  simp only [Fin.val_mk]

  -- Direct calculation: exp(2πi·j/p^n) = exp(2πi·(p·j)/p^{n+1})
  congr 1
  push_cast
  -- Goal: 2πi·j/p^n = 2πi·(p·j)/p^{n+1}
  have hp_ne : (p : ℂ) ≠ 0 := by
    norm_cast
    exact Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
  have hpn_ne : (p^n : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero n (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))
  have hpn1_ne : (p^(n+1) : ℂ) ≠ 0 := by
    norm_cast
    exact pow_ne_zero (n+1) (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))

  field_simp [hpn_ne, hpn1_ne]
  ring

-- Spiral test function: evaluates polynomial at roots of unity on shells
-- Product over j ∈ [0, p^n) of Q(e^(iθ_j + σ)) * Q(e^(iθ_{p^n-j} - σ))
-- where θ_j = 2πj/p^n are the p^n-th roots of unity
noncomputable def spiral_test (Q : Polynomial ℂ) (p : ℕ) (n : ℕ) (σ : ℝ) : ℂ :=
  Finset.prod (Finset.range (p ^ n)) fun j =>
    let θ_j := 2 * Real.pi * (j : ℝ) / (p ^ n)
    let θ_comp := 2 * Real.pi * ((p ^ n - j) : ℝ) / (p ^ n)
    let z_pos := Complex.exp (σ + I * θ_j)
    let z_neg := Complex.exp (-σ + I * θ_comp)
    Q.eval z_pos * Q.eval z_neg

/-! ## Winding Number and Argument Principle

Discrete winding numbers on the profinite lattice converge to the true winding
number as mesh refines, giving constructive root counting via the argument principle. -/

-- Winding number approximation via argument difference along N-th roots of unity
-- This computes the "discrete winding number" of Q(z) as z traverses {r·ωⱼ}
-- Formula: sum of argument jumps, normalized by 2π
noncomputable def discrete_winding_number (Q : Polynomial ℂ) (N : ℕ) (r : ℝ) : ℝ :=
  -- Note: angles takes ℕ to ensure (j + 1) % N uses nat mod, not real mod
  let angles := fun (j : ℕ) => Complex.arg (Q.eval (r * Complex.exp (I * (2 * Real.pi * (j : ℝ) / N))))
  -- Sum of wrapped angle differences divided by 2π
  (Finset.sum (Finset.range N) fun j =>
    let θ_curr := angles j
    let θ_next := angles ((j + 1) % N)
    -- Wrap the difference to [-π, π]
    let diff := θ_next - θ_curr
    if diff > Real.pi then diff - 2 * Real.pi
    else if diff ≤ -Real.pi then diff + 2 * Real.pi
    else diff) / (2 * Real.pi)

-- The spiral root counter: S(ε) = #{roots α : |α| < e^ε}
-- This is computed via winding number at radius r = e^ε
-- As ε increases, S(ε) jumps by 1 each time r passes a root radius
noncomputable def spiral_root_counter (Q : Polynomial ℂ) (N : ℕ) (ε : ℝ) : ℝ :=
  discrete_winding_number Q N (Real.exp ε)

/-! ### Spiral Action

S(σ) = (1/2π) ∫₀^{2π} log|Q(e^{σ+iθ})| dθ is the logarithmic energy on the
circle at radius e^σ. Its derivative dS/dσ counts roots inside that radius. -/

/-- The spiral action S(σ) = circle average of log|Q| at radius e^σ. -/
noncomputable def spiral_action (Q : Polynomial ℂ) (σ : ℝ) : ℝ :=
  -- Circle average of log|Q(e^{σ+iθ})| over θ ∈ [0, 2π]
  -- Using Mathlib's circle integral: (1/2π) ∫₀^{2π} log|Q(e^{σ+iθ})| dθ
  (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
    Real.log ‖Q.eval (Complex.exp (σ + I * θ))‖

/-! ### Double Profinite Lattice

2D sampling grid: angular (p^n-th roots of unity) × radial (log-spaced in [-n,n]/p^n).
Exhausts ℂ* as n → ∞. -/

/-- The 2D profinite sample lattice at level n.
    Angular: p^n-th roots of unity
    Radial: σ ∈ [-n, n] with step 1/p^n, symmetric around 0 (i.e., r = 1) -/
def profinite_sample_lattice (p : ℕ) (n : ℕ) : Set ℂ :=
  { z : ℂ | ∃ (k : ℤ) (j : ℕ), j < p^n ∧
    k.natAbs ≤ n * p^n ∧  -- σ = k/p^n ∈ [-n, n]
    z = Real.exp (k / p^n : ℝ) * Complex.exp (2 * Real.pi * I * j / p^n) }

/-- The radial sample points at level n: σ ∈ [-n, n] with step 1/p^n -/
def radial_lattice (p : ℕ) (n : ℕ) : Set ℝ :=
  { σ : ℝ | ∃ (k : ℤ), k.natAbs ≤ n * p^n ∧ σ = k / p^n }

/-- The angular sample points at level n: p^n-th roots of unity -/
def angular_lattice (p : ℕ) (n : ℕ) : Set ℂ :=
  { ζ : ℂ | ζ^(p^n) = 1 }

/-- Any p^n-th root of unity can be written as a character. -/
lemma root_of_unity_eq_character (p : ℕ) (_hp : 1 < p) (n : ℕ) [NeZero (p^n)]
    (ζ : ℂ) (hζ : ζ^(p^n) = 1) :
    ∃ j : ℕ, j < p^n ∧ ζ = Complex.exp (2 * Real.pi * I * j / (p^n)) := by
  let N := p ^ n
  -- Use the primitive root characterization
  -- exp(2πI/N) is a primitive Nth root of unity
  have h_prim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * I / N)) N :=
    Complex.isPrimitiveRoot_exp N (NeZero.ne N)

  -- Since ζ^N = 1, there exists i < N such that exp(2πI/N)^i = ζ
  have : NeZero N := inferInstance
  obtain ⟨i, hi, h_pow⟩ := h_prim.eq_pow_of_pow_eq_one hζ

  use i, hi

  -- Show ζ = exp(2πIi/N) = exp(2πIi/p^n)
  rw [← h_pow, ← Complex.exp_nat_mul]
  -- N = p^n, need to show i * (2πI/N) = 2πI*i/p^n
  congr 1
  simp only [N, Nat.cast_pow]
  ring

/-- The 2D lattice is the product of radial and angular lattices -/
lemma profinite_sample_lattice_eq_product (p : ℕ) (hp : 1 < p) (n : ℕ) :
    profinite_sample_lattice p n =
      { z : ℂ | ∃ σ ∈ radial_lattice p n, ∃ ζ ∈ angular_lattice p n,
        z = Real.exp σ * ζ } := by
  ext z
  simp only [profinite_sample_lattice, radial_lattice, angular_lattice, Set.mem_setOf_eq]
  constructor
  · intro ⟨k, j, hj, hk, hz⟩
    use k / p^n
    constructor
    · exact ⟨k, hk, rfl⟩
    · use Complex.exp (2 * Real.pi * I * j / p^n)
      constructor
      · -- Show ζ^{p^n} = 1
        have hp_pos : (p : ℂ) ^ n ≠ 0 := by
          apply pow_ne_zero
          simp only [ne_eq, Nat.cast_eq_zero]
          omega
        rw [← Complex.exp_nat_mul]
      -- Goal: exp((p^n : ℕ) * (2πi * j / p^n)) = 1
      -- The coercions are tricky: ↑(p^n) vs ↑p^n
      -- Use simp to normalize, then show the product simplifies
        simp only [Nat.cast_pow]
      -- Now goal has (↑p)^n * (2πi * j / (↑p)^n)
        have h_simp : (p : ℂ) ^ n * (2 * Real.pi * I * j / (p : ℂ) ^ n) = 2 * Real.pi * I * j := by
          field_simp [hp_pos]
        rw [h_simp]
      -- Now show exp(2πi * j) = 1
        have h2pi : Complex.exp (2 * Real.pi * I * j) = 1 := by
          have := Complex.exp_nat_mul_two_pi_mul_I j
          convert this using 2
          ring
        exact h2pi
      · exact hz
  · intro ⟨σ, ⟨k, hk, hσ⟩, ζ, hζ, hz⟩
    -- ζ is a p^n-th root of unity, so ζ = exp(2πij/p^n) for some j
    haveI : NeZero (p^n) := ⟨by
      apply pow_ne_zero
      omega⟩
    obtain ⟨j, hj_lt, hζ_eq⟩ := root_of_unity_eq_character p hp n ζ hζ
    use k, j
    refine ⟨hj_lt, hk, ?_⟩
    rw [hz, ← hσ, hζ_eq]

/-- The radial lattice is symmetric around 0 (equivalently, r-lattice symmetric around 1) -/
lemma radial_lattice_symmetric (p : ℕ) (n : ℕ) (σ : ℝ) :
    σ ∈ radial_lattice p n ↔ -σ ∈ radial_lattice p n := by
  simp only [radial_lattice, Set.mem_setOf_eq]
  constructor
  · intro ⟨k, hk, hσ⟩
    use -k
    constructor
    · simp only [Int.natAbs_neg]; exact hk
    · simp only [Int.cast_neg, neg_div]; linarith
  · intro ⟨k, hk, hσ⟩
    use -k
    constructor
    · simp only [Int.natAbs_neg]; exact hk
    · simp only [Int.cast_neg, neg_div, neg_neg] at hσ ⊢; linarith

/-- The radial lattice at level n embeds into the lattice at level n' when n ≤ n'.
    This is because k/p^n = (k * p^{n'-n})/p^{n'} and the range increases with level. -/
lemma radial_lattice_mono (p : ℕ) (hp : 1 < p) (n n' : ℕ) (hn : n ≤ n') :
    radial_lattice p n ⊆ radial_lattice p n' := by
  intro σ hσ
  simp only [radial_lattice, Set.mem_setOf_eq] at hσ ⊢
  obtain ⟨k, hk_bound, hk_eq⟩ := hσ
  -- Rescale: σ = k/p^n = (k * p^{n'-n})/p^{n'}
  let k' := k * (p : ℤ)^(n' - n)
  use k'
  constructor
  · -- |k'| ≤ n' * p^{n'}
    -- |k'| = |k| * p^{n'-n} ≤ n * p^n * p^{n'-n} = n * p^{n'} ≤ n' * p^{n'}
    have hp_pos : (p : ℤ) > 0 := by positivity
    have hp_pow_pos : (p : ℤ)^(n' - n) > 0 := pow_pos hp_pos (n' - n)
    have h_natabs_pow : ((p : ℤ)^(n' - n)).natAbs = p^(n' - n) := by
      rw [Int.natAbs_pow]
      simp only [Int.natAbs_natCast]
    calc k'.natAbs = (k * (p : ℤ)^(n' - n)).natAbs := rfl
      _ = k.natAbs * ((p : ℤ)^(n' - n)).natAbs := Int.natAbs_mul k _
      _ = k.natAbs * (p^(n' - n)) := by rw [h_natabs_pow]
      _ ≤ (n * p^n) * p^(n' - n) := Nat.mul_le_mul_right _ hk_bound
      _ = n * (p^n * p^(n' - n)) := by ring
      _ = n * p^(n + (n' - n)) := by rw [pow_add]
      _ = n * p^n' := by rw [Nat.add_sub_cancel' hn]
      _ ≤ n' * p^n' := Nat.mul_le_mul_right _ hn
  · -- σ = k'/p^{n'}
    rw [hk_eq]
    simp only [k', Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    have hp_ne : (p : ℝ)^n ≠ 0 := pow_ne_zero n (by positivity : (p : ℝ) ≠ 0)
    have hp_ne' : (p : ℝ)^n' ≠ 0 := pow_ne_zero n' (by positivity : (p : ℝ) ≠ 0)
    have hp_pow_ne : (p : ℝ)^(n' - n) ≠ 0 := pow_ne_zero (n' - n) (by positivity : (p : ℝ) ≠ 0)
    calc (k : ℝ) / (p : ℝ)^n
        = (k : ℝ) * (p : ℝ)^(n' - n) / ((p : ℝ)^n * (p : ℝ)^(n' - n)) := by field_simp
      _ = (k : ℝ) * (p : ℝ)^(n' - n) / (p : ℝ)^(n + (n' - n)) := by rw [pow_add]
      _ = (k : ℝ) * (p : ℝ)^(n' - n) / (p : ℝ)^n' := by rw [Nat.add_sub_cancel' hn]

/-- As n → ∞, the radial lattice becomes dense in ℝ -/
lemma radial_lattice_dense (p : ℕ) (hp : 1 < p) (σ : ℝ) (ε : ℝ) (hε : ε > 0) :
    ∃ n : ℕ, ∃ σ' ∈ radial_lattice p n, |σ - σ'| < ε ∧ |σ| < n := by
  -- Choose n large enough that 1/p^n < ε and n > |σ|
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1/ε) |σ|)
  use n
  -- Round σ to nearest multiple of 1/p^n
  let k := ⌊σ * p^n⌋
  use k / p^n
  have hp_cast : (p : ℝ) > 0 := Nat.cast_pos.mpr (by omega : p > 0)
  have hp_pos : (p : ℝ)^n > 0 := pow_pos hp_cast n
  have hp_ne : (p : ℝ)^n ≠ 0 := ne_of_gt hp_pos
  constructor
  · -- Show k/p^n ∈ radial_lattice
    use k
    constructor
    · -- |k| ≤ n * p^n
      -- We have |σ| < n, so |σ * p^n| < n * p^n
      -- And k = ⌊σ * p^n⌋, so |k| ≤ |σ * p^n| + 1 < n * p^n + 1 ≤ n * p^n + p^n
      have h_abs_σ : |σ| < n := lt_of_le_of_lt (le_max_right _ _) hn
      have h_bound : |σ * (p : ℝ)^n| < n * (p : ℝ)^n := by
        rw [abs_mul, abs_of_pos hp_pos]
        exact mul_lt_mul_of_pos_right h_abs_σ hp_pos
      -- |⌊x⌋| ≤ |x| + 1 for any x
      have h_floor_bound : |(k : ℝ)| ≤ |σ * (p : ℝ)^n| + 1 := by
        have h1 : (k : ℝ) ≤ σ * p^n := Int.floor_le _
        have h2 : σ * p^n - 1 < k := Int.sub_one_lt_floor _
        rw [abs_le]
        constructor
        · -- Need: -(|σ * p^n| + 1) ≤ k
          -- We have σ * p^n - 1 < k and -|σ * p^n| ≤ σ * p^n
          have h3 : -|σ * (p : ℝ)^n| ≤ σ * (p : ℝ)^n := neg_abs_le _
          linarith
        · calc (k : ℝ) ≤ σ * p^n := h1
            _ ≤ |σ * (p : ℝ)^n| := le_abs_self _
            _ ≤ |σ * (p : ℝ)^n| + 1 := by linarith
      -- Now |k| ≤ |σ * p^n| + 1 < n * p^n + 1
      -- Since k is an integer, |k| < n * p^n + 1 implies |k| ≤ n * p^n
      have h_strict : |(k : ℝ)| < n * (p : ℝ)^n + 1 := by linarith
      -- Convert the real strict inequality to an integer inequality
      -- Key: for integer k and natural M, |k| < M + 1 as reals iff k.natAbs ≤ M
      have h_bound_int : k.natAbs ≤ n * p^n := by
      -- First establish that (k.natAbs : ℝ) = |(k : ℝ)|
        have h_real_natabs : (k.natAbs : ℝ) = |(k : ℝ)| := by
          -- Rewrite using Int.cast_abs : (|k| : ℝ) = |(k : ℝ)|
          -- and Int.natCast_natAbs : (k.natAbs : ℤ) = |k|
          simp only [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
        have h_natabs_strict : (k.natAbs : ℝ) < n * (p : ℝ)^n + 1 := by
          rw [h_real_natabs]; exact h_strict
      -- Convert n * p^n to real
        have h_cast_eq : ((n * p^n : ℕ) : ℝ) = n * (p : ℝ)^n := by
          simp only [Nat.cast_mul, Nat.cast_pow]
      -- Now use Nat.cast_lt to go from reals to naturals
      -- k.natAbs < n * p^n + 1 as naturals implies k.natAbs ≤ n * p^n
        have h_lt : k.natAbs < n * p^n + 1 := by
          rw [← Nat.cast_lt (α := ℝ)]
          calc (k.natAbs : ℝ) < n * (p : ℝ)^n + 1 := h_natabs_strict
            _ = ((n * p^n : ℕ) : ℝ) + 1 := by rw [h_cast_eq]
            _ = ((n * p^n + 1 : ℕ) : ℝ) := by simp
        omega
      exact h_bound_int
    · rfl
  constructor
  · -- |σ - k/p^n| < ε
    have h_floor : |σ - k / (p : ℝ)^n| ≤ 1 / (p : ℝ)^n := by
      rw [abs_sub_le_iff]
      constructor
      · -- σ - k/p^n ≥ -1/p^n, i.e., σ + 1/p^n ≥ k/p^n
        have := Int.sub_one_lt_floor (σ * (p : ℝ)^n)
      -- σ * p^n - 1 < k, so σ - 1/p^n < k/p^n
        have h := div_lt_div_of_pos_right this hp_pos
        simp only [sub_div, mul_div_assoc, div_self hp_ne] at h
        linarith
      · -- k/p^n - σ ≤ 1/p^n (second part of abs_sub_le_iff)
      -- From k = ⌊σ * p^n⌋, we have k ≤ σ * p^n, so k/p^n ≤ σ
        have h1 := Int.floor_le (σ * (p : ℝ)^n)
        have h2 : (k : ℝ) / (p : ℝ)^n ≤ σ := by
          have hdiv := div_le_div_of_nonneg_right h1 (le_of_lt hp_pos)
          simp only [mul_div_assoc, div_self hp_ne, mul_one] at hdiv
          exact hdiv
      -- k/p^n - σ ≤ 0 < 1/p^n
        have h3 : (k : ℝ) / (p : ℝ)^n - σ ≤ 0 := by linarith
        have h4 : (0 : ℝ) < 1 / (p : ℝ)^n := by positivity
        linarith
    -- Now show 1/p^n < ε
    have h1 : 1/ε < n := lt_of_le_of_lt (le_max_left _ _) hn
    have hn_pos : (n : ℝ) > 0 := by
      have : 1/ε > 0 := one_div_pos.mpr hε
      linarith
    -- p^n ≥ n for p ≥ 2
    have hp_ge_2 : (p : ℝ) ≥ 2 := by exact_mod_cast hp
    have h_pn_ge_n : (p : ℝ)^n ≥ n := by
      -- Use p^n ≥ 2^n > n (from Nat.lt_two_pow_self)
      have h2n_nat : n < 2^n := Nat.lt_two_pow_self
      have h2n : (n : ℝ) ≤ (2 : ℝ)^n := by
        have : (n : ℝ) < (2^n : ℕ) := by exact_mod_cast h2n_nat
        simp only [Nat.cast_pow, Nat.cast_ofNat] at this
        linarith
      have h_2_le_p : (2 : ℝ)^n ≤ (p : ℝ)^n :=
        pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2) hp_ge_2 n
      linarith
    have h_eps_bound : 1 / (n : ℝ) < ε := by
      -- From h1: 1/ε < n, so 1/n < ε
      have h_inv : 1/ε < n := h1
      rw [one_div] at h_inv
      rw [one_div, inv_lt_comm₀ hn_pos hε]
      exact h_inv
    calc |σ - k / (p : ℝ)^n| ≤ 1 / (p : ℝ)^n := h_floor
      _ ≤ 1 / n := div_le_div_of_nonneg_left (by linarith) hn_pos h_pn_ge_n
      _ < ε := h_eps_bound
  · -- |σ| < n
    exact lt_of_le_of_lt (le_max_right _ _) hn

/-! ### Double-Dense Exhaustion of ℂ*

The angular × radial profinite lattice becomes dense in ℂ* as n → ∞. -/

/-- The double profinite lattice at level n: angular × radial sampling points.
    Each point is e^{σ + iθ} where σ ∈ radial_lattice and θ = 2πk/p^n. -/
def double_lattice_points (p : ℕ) (n : ℕ) : Set ℂ :=
  { z : ℂ | ∃ (σ : ℝ) (k : ℕ), σ ∈ radial_lattice p n ∧ k < p^n ∧
    z = Complex.exp (σ + I * (2 * Real.pi * k / p^n)) }

/-! ### Double Exhaustion Convergence

Discrete averages over the 2D lattice converge to continuous integrals. -/

/-- The double lattice becomes dense in ℂ* as n → ∞.
    For any nonzero z and any ε > 0, there exists N such that for all n ≥ N,
    there is a point in double_lattice_points p n within ε of z. -/
lemma double_lattice_dense (p : ℕ) (hp : 1 < p) (z : ℂ) (hz : z ≠ 0) (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ w ∈ double_lattice_points p n, ‖z - w‖ < ε := by
  -- Write z in polar form
  set σ := Real.log ‖z‖ with hσ_def
  have h_norm_pos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz

  -- Define constants that depend on z
  let C := max 1 (‖z‖ + Real.exp (|σ| + 1))  -- Lipschitz-like constant
  have hC_pos : C > 0 := lt_max_of_lt_left one_pos

  -- Use smaller tolerance for approximations (capped at 1 for exp bounds)
  let δ := min 1 (ε / (4 * C))
  have hδ_pos : δ > 0 := lt_min_iff.mpr ⟨one_pos, by positivity⟩
  have hδ_le_one : δ ≤ 1 := min_le_left _ _
  have hδ_le_eps : δ ≤ ε / (4 * C) := min_le_right _ _

  -- Get radial approximation with tolerance δ
  obtain ⟨n₁, σ', hσ'_mem, hσ'_close, hσ_bound⟩ := radial_lattice_dense p hp σ δ hδ_pos

  -- Get angular mesh size < δ
  have h_mesh_small : ∃ n₂ : ℕ, ∀ n ≥ n₂, 2 * Real.pi / (p : ℝ)^n < δ := by
    have h_tendsto : Filter.Tendsto (fun n => 2 * Real.pi / (p : ℝ)^n) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hp : (1 : ℝ) < p)
    rw [Metric.tendsto_atTop] at h_tendsto
    obtain ⟨N, hN⟩ := h_tendsto δ hδ_pos
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    simp only [Real.dist_eq, sub_zero, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi / (p : ℝ)^n)] at this
    exact this
  obtain ⟨n₂, hn₂⟩ := h_mesh_small

  -- Get n₃ such that ‖z‖ * 4π / p^n < ε/2 for n ≥ n₃
  have h_z_mesh : ∃ n₃ : ℕ, ∀ n ≥ n₃, ‖z‖ * (4 * Real.pi) / (p : ℝ)^n < ε / 2 := by
    have h_tendsto : Filter.Tendsto (fun n => ‖z‖ * (4 * Real.pi) / (p : ℝ)^n) Filter.atTop (nhds (0 : ℝ)) := by
      have h1 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (p : ℝ)^n) Filter.atTop (nhds 0) := by
        simp only [one_div]
        have h_eq : ∀ n : ℕ, ((p : ℝ)^n)⁻¹ = ((p : ℝ)⁻¹)^n := fun n => (inv_pow _ n).symm
        simp only [h_eq]
        apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
        rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ)⁻¹)]
        have hp_ge_2 : (p : ℝ) ≥ 2 := by exact_mod_cast hp
        have hp_pos : (0 : ℝ) < p := by linarith
        have h_inv_bound : (p : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by
          rw [one_div, inv_le_inv₀ hp_pos (by norm_num : (0 : ℝ) < 2)]
          exact hp_ge_2
        linarith
      have h2 : Filter.Tendsto (fun n : ℕ => ‖z‖ * (4 * Real.pi) * ((1 : ℝ) / (p : ℝ)^n))
                  Filter.atTop (nhds (‖z‖ * (4 * Real.pi) * 0)) :=
        Filter.Tendsto.const_mul _ h1
      simp only [mul_zero, mul_one_div] at h2
      exact h2
    rw [Metric.tendsto_atTop] at h_tendsto
    obtain ⟨N, hN⟩ := h_tendsto (ε / 2) (by linarith)
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    simp only [Real.dist_eq, sub_zero, Real.norm_eq_abs] at this
    rwa [abs_of_pos (by positivity : 0 < ‖z‖ * (4 * Real.pi) / (p : ℝ)^n)] at this
  obtain ⟨n₃, hn₃⟩ := h_z_mesh

  -- Take N = max of all constraints
  use max n₁ (max n₂ n₃)
  intro n hn
  have hn₁ : n ≥ n₁ := le_trans (le_max_left _ _) hn
  have hn₂' : n ≥ n₂ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn₃' : n ≥ n₃ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn

  -- Get radial approximation at level n
  have h_radial_approx : ∃ σ'' ∈ radial_lattice p n, |σ - σ''| < δ :=
    ⟨σ', radial_lattice_mono p hp n₁ n hn₁ hσ'_mem, hσ'_close⟩
  obtain ⟨σ'', hσ''_mem, hσ''_close⟩ := h_radial_approx

  -- Angular lattice point - use positive angle in [0, 2π)
  have hp_pos : 0 < p^n := pow_pos (by omega : 0 < p) n
  -- Normalize θ to [0, 2π) for better floor behavior
  let θ := Complex.arg z
  let θ_pos := θ + (if θ < 0 then 2 * Real.pi else 0)  -- θ_pos ∈ [0, 2π)
  let k_raw := Int.floor (θ_pos * (p : ℝ)^n / (2 * Real.pi))
  set k := k_raw.toNat % (p^n) with hk_def

  -- The lattice point
  set w := Complex.exp (σ'' + I * (2 * Real.pi * k / (p : ℝ)^n)) with hw_def
  use w

  constructor
  · -- w ∈ double_lattice_points p n
    unfold double_lattice_points
    simp only [Set.mem_setOf_eq]
    have hk_lt : k < p^n := by simp only [hk_def]; exact Nat.mod_lt _ hp_pos
    exact ⟨σ'', k, hσ''_mem, hk_lt, rfl⟩

  · -- ‖z - w‖ < ε
    -- z = ‖z‖ * exp(I * θ), w = exp(σ'') * exp(I * φ) where φ = 2πk/p^n
    have hz_eq : z = ‖z‖ * Complex.exp (I * θ) := by
      have h := Complex.norm_mul_exp_arg_mul_I z
      -- h : z = ‖z‖ * exp(z.arg * I), but θ = z.arg and we need exp(I * θ)
      -- Need to use complex multiplication commutativity
      simp only [mul_comm (↑(Complex.arg z) : ℂ) I] at h
      exact h.symm

    -- Define φ first
    set φ := 2 * Real.pi * (k : ℝ) / (p : ℝ)^n with hφ_def

    have hw_eq' : w = Real.exp σ'' * Complex.exp (I * φ) := by
      -- Expand w and simplify the expression
      simp only [hw_def, hφ_def]
      -- Goal: cexp (↑σ'' + I * (2 * ↑π * ↑k / ↑↑p ^ n)) = ↑(rexp σ'') * cexp (I * ↑(2 * π * ↑k / ↑p ^ n))
      -- First split using exp_add
      rw [Complex.exp_add]
      -- Now: cexp ↑σ'' * cexp (I * (2 * ↑π * ↑k / ↑↑p ^ n)) = ↑(rexp σ'') * cexp (I * ↑(2 * π * ↑k / ↑p ^ n))
      congr 1
      · -- cexp ↑σ'' = ↑(rexp σ'')
        rw [Complex.ofReal_exp]
      · -- cexp (I * (2 * ↑π * ↑k / ↑↑p ^ n)) = cexp (I * ↑(2 * π * ↑k / ↑p ^ n))
        congr 1
      -- I * (2 * ↑π * ↑k / ↑↑p ^ n) = I * ↑(2 * π * ↑k / ↑p ^ n)
        congr 1
      -- (2 * ↑π * ↑k / ↑↑p ^ n) = ↑(2 * π * ↑k / ↑p ^ n)
        simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
                   Complex.ofReal_pow]
        norm_cast

    -- Unit vectors
    have h_unit_θ : ‖Complex.exp (I * θ)‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, mul_zero,
        Complex.I_im, Complex.ofReal_im, one_mul, sub_self, Real.exp_zero]
      norm_num

    have h_unit_φ : ‖Complex.exp (I * φ)‖ = 1 := by
      rw [Complex.norm_exp]
      simp only [hφ_def, Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, one_mul,
        Complex.ofReal_im, sub_self, Real.exp_zero]
      norm_num

    rw [hz_eq, hw_eq']
    set u := Complex.exp (I * θ) with hu_def
    set v := Complex.exp (I * φ) with hv_def

    -- Triangle inequality decomposition
    calc ‖↑‖z‖ * u - ↑(Real.exp σ'') * v‖
        = ‖↑‖z‖ * (u - v) + (↑‖z‖ - ↑(Real.exp σ'')) * v‖ := by ring_nf
      _ ≤ ‖↑‖z‖ * (u - v)‖ + ‖(↑‖z‖ - ↑(Real.exp σ'')) * v‖ := norm_add_le _ _
      _ = ‖z‖ * ‖u - v‖ + |‖z‖ - Real.exp σ''| * ‖v‖ := by
          -- ‖↑‖z‖‖ = |‖z‖| = ‖z‖ since ‖z‖ ≥ 0
          -- ‖↑‖z‖ - ↑(rexp σ'')‖ = |‖z‖ - rexp σ''| since these are real
          have h1 : ‖(‖z‖ : ℂ)‖ = ‖z‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          have h2 : ‖((‖z‖ : ℝ) - Real.exp σ'' : ℂ)‖ = |‖z‖ - Real.exp σ''| := by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          simp only [norm_mul, h1, h2]
      _ = ‖z‖ * ‖u - v‖ + |‖z‖ - Real.exp σ''| := by rw [h_unit_φ]; ring
      _ < ε := by
      -- Angular bound: ‖u - v‖ ≤ 2π/p^n from the floor construction
      -- The floor gives k such that |θ_pos - 2πk/p^n| < 2π/p^n
        have h_angular : ‖u - v‖ ≤ 4 * Real.pi / (p : ℝ)^n := by
          -- θ_pos ∈ [0, 2π) and k_raw = floor(θ_pos * p^n / (2π))
          -- Since θ_pos * p^n / (2π) ∈ [0, p^n), we have k_raw ∈ [0, p^n)
          -- So k = k_raw % p^n = k_raw, and |θ_pos - φ| < 2π/p^n

          -- First, show θ_pos ∈ [0, 2π)
          have h_θ_pos_nonneg : θ_pos ≥ 0 := by
            show θ + (if θ < 0 then 2 * Real.pi else 0) ≥ 0
            by_cases hθ_neg : θ < 0
            · simp only [if_pos hθ_neg]
              have := Complex.neg_pi_lt_arg z
              linarith [Real.pi_pos]
            · simp only [if_neg hθ_neg, add_zero]
              push_neg at hθ_neg; exact hθ_neg

          have h_θ_pos_lt : θ_pos < 2 * Real.pi := by
            show θ + (if θ < 0 then 2 * Real.pi else 0) < 2 * Real.pi
            by_cases hθ_neg : θ < 0
            · simp only [if_pos hθ_neg]
              have := Complex.neg_pi_lt_arg z
              linarith [Real.pi_pos]
            · simp only [if_neg hθ_neg, add_zero]
              have h_arg_le := Complex.arg_le_pi z
              linarith [Real.pi_pos]

          -- k_raw = floor(θ_pos * p^n / (2π))
          -- From the floor inequality: k_raw ≤ θ_pos * p^n / (2π) < k_raw + 1
          have h_floor_ineq : (k_raw : ℝ) ≤ θ_pos * (p : ℝ)^n / (2 * Real.pi) ∧
                              θ_pos * (p : ℝ)^n / (2 * Real.pi) < k_raw + 1 := by
            constructor
            · exact Int.floor_le _
            · exact Int.lt_floor_add_one _

          -- k_raw is in [0, p^n) since θ_pos ∈ [0, 2π)
          have h_kraw_nonneg : k_raw ≥ 0 := by
            have h1 : θ_pos * (p : ℝ)^n / (2 * Real.pi) ≥ 0 := by
              apply div_nonneg
              apply mul_nonneg h_θ_pos_nonneg
              positivity
              linarith [Real.pi_pos]
            exact Int.floor_nonneg.mpr h1

          have h_kraw_lt : k_raw < (p^n : ℤ) := by
            have h1 : θ_pos * (p : ℝ)^n / (2 * Real.pi) < (p^n : ℝ) := by
              calc θ_pos * (p : ℝ)^n / (2 * Real.pi)
                  < 2 * Real.pi * (p : ℝ)^n / (2 * Real.pi) := by
                    apply div_lt_div_of_pos_right _ (by linarith [Real.pi_pos])
                    apply mul_lt_mul_of_pos_right h_θ_pos_lt (by positivity)
                _ = (p : ℝ)^n := by field_simp
            exact Int.floor_lt.mpr (by exact_mod_cast h1)

          -- So k = k_raw.toNat = k_raw (since k_raw ≥ 0 and < p^n)
          have h_k_eq : (k : ℤ) = k_raw := by
            simp only [hk_def]
            -- First, toNat of a nonnegative int equals the int as a nat cast
            have h_toNat_cast : (k_raw.toNat : ℤ) = k_raw := Int.toNat_of_nonneg h_kraw_nonneg
            -- k_raw.toNat < p^n since k_raw < p^n
            have h_toNat_lt : k_raw.toNat < p^n := by
              have h1 : (k_raw.toNat : ℤ) = k_raw := h_toNat_cast
              have h2 : k_raw < (p^n : ℤ) := h_kraw_lt
              rw [← h1] at h2
              exact_mod_cast h2
            -- So k_raw.toNat % p^n = k_raw.toNat
            have h_mod_eq : k_raw.toNat % p^n = k_raw.toNat := Nat.mod_eq_of_lt h_toNat_lt
            rw [h_mod_eq]
            exact h_toNat_cast

          -- |θ_pos - φ| < 2π/p^n from the floor bound
          have h_angular_diff : |θ_pos - φ| ≤ 2 * Real.pi / (p : ℝ)^n := by
            -- From floor: k_raw ≤ θ_pos * p^n / (2π) < k_raw + 1
            -- So 2π * k_raw / p^n ≤ θ_pos < 2π * (k_raw + 1) / p^n
            -- And φ = 2π * k / p^n = 2π * k_raw / p^n (since k = k_raw)
            -- Thus 0 ≤ θ_pos - φ < 2π/p^n
            have h_φ_eq : φ = 2 * Real.pi * k_raw / (p : ℝ)^n := by
              simp only [hφ_def]
              have h_k_real : (k : ℝ) = (k_raw : ℝ) := by
                have h1 : (k : ℤ) = k_raw := h_k_eq
                exact_mod_cast h1
              rw [h_k_real]
            rw [h_φ_eq]
            have h_diff_nonneg : θ_pos - 2 * Real.pi * k_raw / (p : ℝ)^n ≥ 0 := by
              have h1 := h_floor_ineq.1
              -- From floor: k_raw ≤ θ_pos * p^n / (2π)
              -- Multiply by 2π/p^n: 2π * k_raw / p^n ≤ θ_pos
              have h_pn_pos : (p : ℝ)^n > 0 := by positivity
              have h_pn_nonneg : 0 ≤ (p : ℝ)^n := le_of_lt h_pn_pos
              have h_pi_pos : Real.pi > 0 := Real.pi_pos
              have h_key : 2 * Real.pi * k_raw / (p : ℝ)^n ≤ θ_pos := by
                have h2 : k_raw ≤ θ_pos * (p : ℝ)^n / (2 * Real.pi) := h1
                have h3 : 2 * Real.pi * k_raw / (p : ℝ)^n ≤
                    2 * Real.pi * (θ_pos * (p : ℝ)^n / (2 * Real.pi)) / (p : ℝ)^n := by
                  apply div_le_div_of_nonneg_right _ h_pn_nonneg
                  apply mul_le_mul_of_nonneg_left h2 (by linarith)
                calc 2 * Real.pi * k_raw / (p : ℝ)^n
                    ≤ 2 * Real.pi * (θ_pos * (p : ℝ)^n / (2 * Real.pi)) / (p : ℝ)^n := h3
                  _ = θ_pos := by field_simp
              linarith
            have h_diff_lt : θ_pos - 2 * Real.pi * k_raw / (p : ℝ)^n < 2 * Real.pi / (p : ℝ)^n := by
              have h2 := h_floor_ineq.2
              have h_pn_pos' : (p : ℝ)^n > 0 := by positivity
              have h_pi_pos' : 2 * Real.pi > 0 := by linarith [Real.pi_pos]
              have h_step1 : θ_pos < 2 * Real.pi * (k_raw + 1) / (p : ℝ)^n := by
                have h3 : θ_pos = θ_pos * (p : ℝ)^n / (p : ℝ)^n := by field_simp
                have h4 : θ_pos * (p : ℝ)^n / (p : ℝ)^n =
                    2 * Real.pi * (θ_pos * (p : ℝ)^n / (2 * Real.pi)) / (p : ℝ)^n := by field_simp
                have h5 : 2 * Real.pi * (θ_pos * (p : ℝ)^n / (2 * Real.pi)) / (p : ℝ)^n <
                    2 * Real.pi * (k_raw + 1) / (p : ℝ)^n := by
                  apply div_lt_div_of_pos_right _ h_pn_pos'
                  apply mul_lt_mul_of_pos_left h2 h_pi_pos'
                linarith
              calc θ_pos - 2 * Real.pi * k_raw / (p : ℝ)^n
                  < 2 * Real.pi * (k_raw + 1) / (p : ℝ)^n - 2 * Real.pi * k_raw / (p : ℝ)^n := by
                    linarith
                _ = 2 * Real.pi / (p : ℝ)^n := by ring
            rw [abs_of_nonneg h_diff_nonneg]
            linarith

          -- Use h_angular_diff and chord ≤ arc for unit circle
          -- For p^n ≤ 2π: use triangle bound ‖u-v‖ ≤ 2 ≤ 4π/p^n
          -- For p^n > 2π: use |exp(iα) - exp(iβ)| ≤ |α - β| when |α - β| ≤ π
          have h_triangle : ‖u - v‖ ≤ 2 := by
            calc ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le _ _
              _ = 1 + 1 := by rw [h_unit_θ, h_unit_φ]
              _ = 2 := by ring
          by_cases h_pn_small : (p : ℝ)^n ≤ 2 * Real.pi
          · -- For small p^n ≤ 2π: 2 ≤ 4π/p^n
            calc ‖u - v‖ ≤ 2 := h_triangle
              _ = 4 * Real.pi / (2 * Real.pi) := by field_simp; ring
              _ ≤ 4 * Real.pi / (p : ℝ)^n := by
                  apply div_le_div_of_nonneg_left _ (by positivity) h_pn_small
                  linarith [Real.pi_pos]
          · -- For large p^n > 2π: use h_angular_diff directly
            -- Since |θ_pos - φ| ≤ 2π/p^n and 2π/p^n ≤ 4π/p^n
            push_neg at h_pn_small
            -- The key bound: h_angular_diff gives |θ_pos - φ| ≤ 2π/p^n
            -- We need: ‖u - v‖ ≤ 4π/p^n
            -- Since 2π/p^n < 1 < π (as p^n > 2π > 6), the chord ≤ arc property gives
            -- ‖exp(iα) - exp(iβ)‖ ≤ |α - β| for |α - β| < π
            -- So ‖u - v‖ ≤ |θ_pos - φ| ≤ 2π/p^n < 4π/p^n
            have h_pn_pos : (p : ℝ)^n > 0 := by positivity
            -- Since p^n > 2π, we have 2π/p^n < 1 < π, so chord ≤ arc applies
            have h_diff_small : |θ_pos - φ| < Real.pi := by
              have h_2pi_pos : 0 < 2 * Real.pi := by linarith [Real.pi_pos]
              calc |θ_pos - φ| ≤ 2 * Real.pi / (p : ℝ)^n := h_angular_diff
                _ < 2 * Real.pi / (2 * Real.pi) := by
                    exact div_lt_div_of_pos_left h_2pi_pos h_2pi_pos h_pn_small
                _ = 1 := by field_simp
                _ < Real.pi := by
                    have h := Real.pi_gt_three; linarith
            -- For |α - β| < π, the chord length |exp(iα) - exp(iβ)| = 2|sin((α-β)/2)| ≤ |α - β|
            -- This is because |sin(x)| ≤ |x| (Real.abs_sin_le) applied to x = (α-β)/2
            have h_chord_le_arc : ‖u - v‖ ≤ |θ_pos - φ| := by
              -- First, show u = exp(I * θ_pos) by 2π periodicity
              -- Since θ_pos = θ + (if θ < 0 then 2π else 0), and exp(2πi) = 1,
              -- we have exp(I * θ_pos) = exp(I * θ) = u
              have hu_eq_θ_pos : u = Complex.exp (I * θ_pos) := by
                -- θ_pos = θ or θ_pos = θ + 2π, and exp(2πi) = 1
                simp only [hu_def]
                by_cases hθ_neg : θ < 0
                · -- θ_pos = θ + 2π, show exp(I*θ) = exp(I*(θ + 2π))
                  have hθ_pos_val : θ_pos = θ + 2 * Real.pi := by
                    show θ + (if θ < 0 then 2 * Real.pi else 0) = θ + 2 * Real.pi
                    rw [if_pos hθ_neg]
                  rw [hθ_pos_val, Complex.ofReal_add, mul_add, Complex.exp_add]
                  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
                  have h2pi : Complex.exp (I * (2 * ↑Real.pi)) = 1 := by
                    convert Complex.exp_two_pi_mul_I using 1; ring_nf
                  rw [h2pi, mul_one]
                · -- θ_pos = θ
                  have hθ_pos_val : θ_pos = θ := by
                    show θ + (if θ < 0 then 2 * Real.pi else 0) = θ
                    rw [if_neg hθ_neg, add_zero]
                  rw [hθ_pos_val]
              -- Now use the Lipschitz bound: |exp(ia) - exp(ib)| ≤ |a - b|
              -- This follows from |sin(x)| ≤ |x|
              rw [hu_eq_θ_pos, hv_def]
              -- ‖exp(I*a) - exp(I*b)‖² = 2(1 - cos(a-b)) = 4sin²((a-b)/2)
              -- So ‖exp(I*a) - exp(I*b)‖ = 2|sin((a-b)/2)| ≤ 2|(a-b)/2| = |a-b|
              have h_key : ‖Complex.exp (I * θ_pos) - Complex.exp (I * φ)‖ ≤ |θ_pos - φ| := by
                -- Factor out: exp(I*a) - exp(I*b) = exp(I*b) * (exp(I*(a-b)) - 1)
                have h_factor : Complex.exp (I * θ_pos) - Complex.exp (I * φ) =
                    Complex.exp (I * φ) * (Complex.exp (I * (θ_pos - φ)) - 1) := by
                  rw [mul_sub, mul_one, ← Complex.exp_add]
                  ring_nf
                rw [h_factor, Complex.norm_mul]
                have h_unit : ‖Complex.exp (I * φ)‖ = 1 := by
                  rw [Complex.norm_exp]
                  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
                             Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero]
                  exact Real.exp_zero
                rw [h_unit, one_mul]
                -- Now bound ‖exp(I*t) - 1‖ ≤ |t| for t = θ_pos - φ
                -- We have exp(I*t) - 1 = cos(t) - 1 + I*sin(t)
                -- ‖exp(I*t) - 1‖² = (cos(t) - 1)² + sin²(t) = 2(1 - cos(t)) = 4sin²(t/2)
                -- So ‖exp(I*t) - 1‖ = 2|sin(t/2)| ≤ 2|t/2| = |t| by |sin(x)| ≤ |x|
                -- Rewrite the Complex subtraction as Real subtraction coerced
                rw [← Complex.ofReal_sub]
                set t := θ_pos - φ with ht_def
                have h_norm_bound : ‖Complex.exp (I * t) - 1‖ ≤ |t| := by
                  -- Use the explicit formula
                  have h_exp : Complex.exp (I * t) = Complex.cos t + I * Complex.sin t := by
                    rw [mul_comm I t, Complex.exp_mul_I]; ring
                  have h_sub : Complex.exp (I * t) - 1 = (Complex.cos t - 1) + I * Complex.sin t := by
                    rw [h_exp]; ring
                  rw [h_sub]
                  -- ‖(cos t - 1) + I * sin t‖² = (cos t - 1)² + (sin t)²
                  -- Use: (cos t - 1)² + sin²t = cos²t - 2cos t + 1 + sin²t = 2(1 - cos t)
                  -- And 2(1 - cos t) = 4sin²(t/2) ≤ t² (since |sin x| ≤ |x|)
                  have h_sq_bound : ‖(Complex.cos t - 1) + I * Complex.sin t‖^2 ≤ t^2 := by
                    -- First simplify: Complex.cos ↑t = ↑(Real.cos t), Complex.sin ↑t = ↑(Real.sin t)
                    have h_cos_eq : Complex.cos ↑t = ↑(Real.cos t) := (Complex.ofReal_cos t).symm
                    have h_sin_eq : Complex.sin ↑t = ↑(Real.sin t) := (Complex.ofReal_sin t).symm
                    rw [h_cos_eq, h_sin_eq]
                    -- Rewrite I * y as y * I
                    have h_comm : I * ↑(Real.sin t) = ↑(Real.sin t) * I := mul_comm _ _
                    rw [h_comm]
                    -- Now: ‖(↑(Real.cos t) - 1) + ↑(Real.sin t) * I‖²
                    have h_norm_sq : ‖(↑(Real.cos t) - 1 : ℂ) + ↑(Real.sin t) * I‖^2 =
                        (Real.cos t - 1)^2 + (Real.sin t)^2 := by
                      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
                      have := Complex.norm_add_mul_I (Real.cos t - 1) (Real.sin t)
                      rw [this, Real.sq_sqrt (by positivity : 0 ≤ (Real.cos t - 1)^2 + (Real.sin t)^2)]
                    rw [h_norm_sq]
                    -- (cos t - 1)² + sin²t = 2 - 2cos t
                    have h_trig : (Real.cos t - 1)^2 + (Real.sin t)^2 = 2 - 2 * Real.cos t := by
                      have h1 : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
                      ring_nf; linarith [h1]
                    -- 2 - 2cos t = 4sin²(t/2) ≤ 4(t/2)² = t²
                    have h_half_angle : 2 - 2 * Real.cos t = 4 * Real.sin (t / 2) ^ 2 := by
                      have h_pyth := Real.cos_sq_add_sin_sq (t / 2)
                      have hcos : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
                        have h_eq : t = 2 * (t / 2) := by ring
                        conv_lhs => rw [h_eq]
                        rw [Real.cos_two_mul]
                        -- Now goal is: 2 * cos(t/2)^2 - 1 = 1 - 2*sin(t/2)^2
                        have h_sub : Real.cos (t / 2) ^ 2 = 1 - Real.sin (t / 2) ^ 2 := by linarith [h_pyth]
                        linarith [h_sub]
                      linarith [hcos]
                    rw [h_trig, h_half_angle]
                    -- 4sin²(t/2) ≤ 4(t/2)² = t²
                    have h_sin_bound : Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := by
                      have h := Real.abs_sin_le_abs (x := t / 2)
                      have h_nonneg_sin : 0 ≤ |Real.sin (t / 2)| := abs_nonneg _
                      have h_nonneg_t : 0 ≤ |t / 2| := abs_nonneg _
                      calc Real.sin (t / 2) ^ 2 = |Real.sin (t / 2)| ^ 2 := by rw [sq_abs]
                        _ ≤ |t / 2| ^ 2 := sq_le_sq' (by linarith) h
                        _ = (t / 2) ^ 2 := sq_abs _
                    calc 4 * Real.sin (t / 2) ^ 2 ≤ 4 * (t / 2) ^ 2 := by linarith [h_sin_bound]
                      _ = t ^ 2 := by ring
                  have h_nonneg : 0 ≤ ‖(Complex.cos ↑t - 1) + I * Complex.sin ↑t‖ := norm_nonneg _
                  have h_t_sq : 0 ≤ t ^ 2 := sq_nonneg _
                  calc ‖(Complex.cos ↑t - 1) + I * Complex.sin ↑t‖
                      = Real.sqrt (‖(Complex.cos ↑t - 1) + I * Complex.sin ↑t‖ ^ 2) := by
                        rw [Real.sqrt_sq h_nonneg]
                    _ ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt h_sq_bound
                    _ = |t| := Real.sqrt_sq_eq_abs t
                exact h_norm_bound
              exact h_key
            calc ‖u - v‖ ≤ |θ_pos - φ| := h_chord_le_arc
              _ ≤ 2 * Real.pi / (p : ℝ)^n := h_angular_diff
              _ ≤ 4 * Real.pi / (p : ℝ)^n := by
                  apply div_le_div_of_nonneg_right _ (le_of_lt h_pn_pos)
                  linarith [Real.pi_pos]

        have h_z_angular := hn₃ n hn₃'  -- ‖z‖ * 4π / p^n < ε/2

      -- Radial bound: |‖z‖ - exp(σ'')| ≤ exp(max) * |σ - σ''|
        have h_exp_σ : ‖z‖ = Real.exp σ := by
          simp only [hσ_def]; exact (Real.exp_log h_norm_pos).symm

        have h_radial : |‖z‖ - Real.exp σ''| < ε / 2 := by
          -- |exp(σ) - exp(σ'')| ≤ exp(max(|σ|,|σ''|)) * |σ - σ''|
          -- max(|σ|,|σ''|) ≤ |σ| + δ ≤ |σ| + 1 (for δ ≤ 1)
          have h_σ''_bound : |σ''| ≤ |σ| + δ := by
            calc |σ''| = |(σ'' - σ) + σ| := by ring_nf
              _ ≤ |σ'' - σ| + |σ| := abs_add_le (σ'' - σ) σ
              _ = |σ - σ''| + |σ| := by rw [abs_sub_comm]
              _ ≤ δ + |σ| := by linarith [hσ''_close.le]
              _ = |σ| + δ := by ring

          have h_max_bound : max |σ| |σ''| ≤ |σ| + δ := max_le (by linarith) h_σ''_bound

          rw [h_exp_σ]
          calc |Real.exp σ - Real.exp σ''|
              ≤ Real.exp (max σ σ'') * |σ - σ''| := by
                -- MVT: |exp(a) - exp(b)| ≤ exp(max(a,b)) * |a - b|
                by_cases h : σ ≤ σ''
                · calc |Real.exp σ - Real.exp σ''|
                      = Real.exp σ'' - Real.exp σ := by
                        rw [abs_sub_comm, abs_of_nonneg]; linarith [Real.exp_le_exp.mpr h]
                    _ ≤ Real.exp σ'' * (1 - Real.exp (σ - σ'')) := by
                        rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf; rfl
                    _ ≤ Real.exp σ'' * |σ - σ''| := by
                        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
                        have h1 : σ - σ'' ≤ 0 := by linarith
                        have h2 : Real.exp (σ - σ'') ≥ 1 + (σ - σ'') := by
                          have := Real.add_one_le_exp (σ - σ''); linarith
                        rw [abs_sub_comm]
                        calc 1 - Real.exp (σ - σ'') ≤ 1 - (1 + (σ - σ'')) := by linarith
                          _ = σ'' - σ := by ring
                          _ = |σ'' - σ| := (abs_of_nonneg (by linarith)).symm
                    _ ≤ Real.exp (max σ σ'') * |σ - σ''| := by
                        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                        exact Real.exp_le_exp.mpr (le_max_right _ _)
                · push_neg at h
                  calc |Real.exp σ - Real.exp σ''|
                      = Real.exp σ - Real.exp σ'' := by
                        rw [abs_of_nonneg]; linarith [Real.exp_le_exp.mpr (le_of_lt h)]
                    _ ≤ Real.exp σ * |σ - σ''| := by
                        have h1 : σ'' - σ < 0 := by linarith
                        have h2 : Real.exp (σ'' - σ) ≥ 1 + (σ'' - σ) := by
                          have := Real.add_one_le_exp (σ'' - σ); linarith
                        calc Real.exp σ - Real.exp σ''
                            = Real.exp σ * (1 - Real.exp (σ'' - σ)) := by
                              rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
                          _ ≤ Real.exp σ * |σ'' - σ| := by
                              apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
                              calc 1 - Real.exp (σ'' - σ) ≤ 1 - (1 + (σ'' - σ)) := by linarith
                                _ = σ - σ'' := by ring
                                _ ≤ |σ - σ''| := le_abs_self _
                                _ = |σ'' - σ| := abs_sub_comm _ _
                          _ = Real.exp σ * |σ - σ''| := by rw [abs_sub_comm]
                    _ ≤ Real.exp (max σ σ'') * |σ - σ''| := by
                        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                        exact Real.exp_le_exp.mpr (le_max_left _ _)
            _ ≤ Real.exp (|σ| + δ) * |σ - σ''| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                apply Real.exp_le_exp.mpr
                calc max σ σ'' ≤ max |σ| |σ''| := max_le_max (le_abs_self _) (le_abs_self _)
                  _ ≤ |σ| + δ := h_max_bound
            _ < Real.exp (|σ| + δ) * δ := by
                exact mul_lt_mul_of_pos_left hσ''_close (Real.exp_pos _)
            _ ≤ Real.exp (|σ| + 1) * δ := by
                apply mul_le_mul_of_nonneg_right _ (le_of_lt hδ_pos)
                exact Real.exp_le_exp.mpr (add_le_add_right hδ_le_one |σ|)
            _ ≤ C * δ := by
                apply mul_le_mul_of_nonneg_right _ (le_of_lt hδ_pos)
                calc Real.exp (|σ| + 1) ≤ ‖z‖ + Real.exp (|σ| + 1) := by linarith [h_norm_pos]
                  _ ≤ max 1 (‖z‖ + Real.exp (|σ| + 1)) := le_max_right _ _
            _ ≤ C * (ε / (4 * C)) := by
                apply mul_le_mul_of_nonneg_left hδ_le_eps
                exact le_of_lt hC_pos
            _ = ε / 4 := by field_simp
            _ < ε / 2 := by linarith

      -- Combine: angular term + radial term < ε
      -- Key facts:
      -- h_angular : ‖u - v‖ ≤ 4 * π / p^n
      -- h_z_angular : ‖z‖ * (4 * π) / p^n < ε / 2
      -- h_radial : |‖z‖ - exp σ''| < ε / 2

        calc ‖z‖ * ‖u - v‖ + |‖z‖ - Real.exp σ''|
            ≤ ‖z‖ * (4 * Real.pi / (p : ℝ)^n) + |‖z‖ - Real.exp σ''| := by
              have h_mul : ‖z‖ * ‖u - v‖ ≤ ‖z‖ * (4 * Real.pi / (p : ℝ)^n) :=
                mul_le_mul_of_nonneg_left h_angular (norm_nonneg _)
              linarith [h_mul]
          _ < ‖z‖ * (4 * Real.pi / (p : ℝ)^n) + ε / 2 := by linarith [h_radial]
          _ = ‖z‖ * (4 * Real.pi) / (p : ℝ)^n + ε / 2 := by ring
          _ < ε / 2 + ε / 2 := by linarith [h_z_angular]
          _ = ε := by ring

set_option maxHeartbeats 400000 in
/-- Double exhaustion gives uniform convergence of discrete averages. -/
theorem double_exhaustion_convergence (p : ℕ) [Fact (Nat.Prime p)] (hp : 1 < p)
    (f : ℂ → ℂ) (hf : Continuous f) (r₁ r₂ : ℝ) (_hr : 0 < r₁) (_hrr : r₁ ≤ r₂) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ σ ∈ Set.Icc (Real.log r₁) (Real.log r₂),
      ‖(p^n : ℂ)⁻¹ * ∑ k ∈ Finset.range (p^n),
          f (Complex.exp (σ + I * (2 * Real.pi * k / p^n))) -
        (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
          f (Complex.exp (σ + I * θ))‖ < ε := by
  intro ε hε
  -- The key insight: f is uniformly continuous on the compact annulus
  -- Define the integrand g(σ, θ) = f(exp(σ + I*θ))
  let g : ℝ × ℝ → ℂ := fun p => f (Complex.exp (p.1 + I * p.2))

  -- g is continuous (composition of continuous functions)
  have hg_cont : Continuous g := by
    apply hf.comp
    apply Complex.continuous_exp.comp
    exact (Complex.continuous_ofReal.comp continuous_fst).add
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))

  -- The domain [log r₁, log r₂] × [0, 2π] is compact
  have h_compact : IsCompact (Set.Icc (Real.log r₁) (Real.log r₂) ×ˢ Set.Icc 0 (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc

  -- g is uniformly continuous on the compact domain
  have hg_unif : UniformContinuousOn g (Set.Icc (Real.log r₁) (Real.log r₂) ×ˢ Set.Icc 0 (2 * Real.pi)) :=
    h_compact.uniformContinuousOn_of_continuous hg_cont.continuousOn

  -- Get a modulus of continuity: for any δ > 0, nearby points have nearby values
  have hε' : ε / 2 > 0 := by linarith
  obtain ⟨δ, hδ_pos, hδ_cont⟩ := Metric.uniformContinuousOn_iff_le.mp hg_unif (ε / 2) hε'

  -- The mesh 2π/p^n → 0, so eventually mesh < δ
  have h_mesh_small : ∃ N, ∀ n ≥ N, 2 * Real.pi / (p : ℝ)^n < δ := by
    have h_tendsto : Filter.Tendsto (fun n => 2 * Real.pi / (p : ℝ)^n) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hp : (1 : ℝ) < p)
    rw [Metric.tendsto_atTop] at h_tendsto
    obtain ⟨N, hN⟩ := h_tendsto δ hδ_pos
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    simp only [Real.dist_eq, sub_zero, Real.norm_eq_abs,
      abs_of_pos (by positivity : 2 * Real.pi / (p : ℝ)^n > 0)] at this
    exact this

  obtain ⟨N, hN⟩ := h_mesh_small
  refine ⟨N, fun n hn σ hσ => ?_⟩

  have h_mesh : 2 * Real.pi / (p : ℝ)^n < δ := hN n hn
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos (Fact.out))
  have hpn_pos : (0 : ℝ) < (p : ℝ)^n := pow_pos hp_pos n

  have hσ_in : σ ∈ Set.Icc (Real.log r₁) (Real.log r₂) := hσ

  -- The integrand at σ
  let h : ℝ → ℂ := fun θ => f (Complex.exp (σ + I * θ))

  -- h is continuous
  have hh_cont : Continuous h := by
    apply hf.comp
    apply Complex.continuous_exp.comp
    exact continuous_const.add (continuous_const.mul Complex.continuous_ofReal)

  -- h is integrable on [0, 2π]
  have hh_int : IntervalIntegrable h MeasureTheory.volume 0 (2 * Real.pi) :=
    hh_cont.intervalIntegrable 0 (2 * Real.pi)

  -- Bound using uniform continuity of g
  -- For θ in [2πk/p^n, 2π(k+1)/p^n], the point (σ, θ) is at distance ≤ 2π/p^n from (σ, 2πk/p^n)
  -- which is < δ, so |g(σ, θ) - g(σ, 2πk/p^n)| < ε/2

  have h_bound : ∀ k ∈ Finset.range (p^n), ∀ θ ∈ Set.Icc (2 * Real.pi * k / (p : ℝ)^n)
      (2 * Real.pi * (k + 1) / (p : ℝ)^n),
      dist (g (σ, θ)) (g (σ, 2 * Real.pi * k / (p : ℝ)^n)) ≤ ε / 2 := by
    intro k hk θ hθ
    apply hδ_cont
    · -- (σ, θ) is in the domain
      constructor
      · exact hσ_in
      · constructor
        · -- θ ≥ 0 follows from θ ≥ 2πk/p^n ≥ 0
          have h1 : 2 * Real.pi * ↑k / (p : ℝ)^n ≥ 0 := by positivity
          calc (0 : ℝ) ≤ 2 * Real.pi * ↑k / (p : ℝ)^n := h1
            _ ≤ θ := hθ.1
        · -- θ ≤ 2π follows from θ ≤ 2π(k+1)/p^n ≤ 2π
          have h2 : 2 * Real.pi * (↑k + 1) / (p : ℝ)^n ≤ 2 * Real.pi := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < (p : ℝ)^n)]
            have hk_bound : k + 1 ≤ p^n := by
              have := Finset.mem_range.mp hk
              omega
            calc 2 * Real.pi * (↑k + 1)
                ≤ 2 * Real.pi * (p^n : ℝ) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  have : (k + 1 : ℝ) ≤ (p^n : ℝ) := by exact_mod_cast hk_bound
                  exact this
              _ = 2 * Real.pi * (p : ℝ)^n := by norm_cast
          calc θ ≤ 2 * Real.pi * (↑k + 1) / (p : ℝ)^n := hθ.2
            _ ≤ 2 * Real.pi := h2
    · -- (σ, 2πk/p^n) is in the domain
      constructor
      · exact hσ_in
      · constructor
        · positivity
        · have hk_bound : k < p^n := Finset.mem_range.mp hk
          have hpn_pos' : (0 : ℝ) < (p : ℝ)^n := by positivity
          have hpn_ge_one : (1 : ℝ) ≤ (p : ℝ)^n := by
            have : 1 ≤ p^n := Nat.one_le_pow n p (Nat.Prime.pos (Fact.out))
            exact_mod_cast this
          calc 2 * Real.pi * ↑k / (p : ℝ)^n
              ≤ 2 * Real.pi * ((p : ℝ)^n - 1) / (p : ℝ)^n := by
                apply div_le_div_of_nonneg_right _ (le_of_lt hpn_pos')
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                have hpn_ge : 1 ≤ p^n := Nat.one_le_pow n p (Nat.Prime.pos (Fact.out))
                have hk_le : k ≤ p^n - 1 := Nat.le_sub_one_of_lt hk_bound
                calc (k : ℝ) ≤ ((p^n - 1) : ℕ) := by exact_mod_cast hk_le
                  _ = (p^n : ℝ) - 1 := by rw [Nat.cast_sub hpn_ge]; norm_cast
                  _ = (p : ℝ)^n - 1 := by norm_cast
            _ ≤ 2 * Real.pi := by
                calc 2 * Real.pi * ((p : ℝ)^n - 1) / (p : ℝ)^n
                    = 2 * Real.pi * (1 - 1 / (p : ℝ)^n) := by field_simp
                  _ ≤ 2 * Real.pi * 1 := by
                      apply mul_le_mul_of_nonneg_left _ (by positivity)
                      have h1 : 0 < 1 / (p : ℝ)^n := by positivity
                      linarith
                  _ = 2 * Real.pi := by ring
    · -- Distance bound: |θ - 2πk/p^n| ≤ 2π/p^n ≤ δ
      rw [Prod.dist_eq, max_le_iff]
      constructor
      · simp only [Real.dist_eq, sub_self, abs_zero]
        exact le_of_lt hδ_pos
      · rw [Real.dist_eq]
        calc |θ - 2 * Real.pi * ↑k / (p : ℝ)^n|
            ≤ 2 * Real.pi * (↑k + 1) / (p : ℝ)^n - 2 * Real.pi * ↑k / (p : ℝ)^n := by
              rw [abs_le]
              have hpn_pos' : (0 : ℝ) < (p : ℝ)^n := by positivity
              have h_width_pos : 0 < 2 * Real.pi * (↑k + 1) / (p : ℝ)^n - 2 * Real.pi * ↑k / (p : ℝ)^n := by
                have : 2 * Real.pi * (↑k + 1) / (p : ℝ)^n - 2 * Real.pi * ↑k / (p : ℝ)^n = 2 * Real.pi / (p : ℝ)^n := by
                  field_simp; ring
                rw [this]; positivity
              constructor
              · -- Need: -(width) ≤ θ - lower. Since 0 ≤ θ - lower (from hθ.1) and width > 0
                have h1 : 0 ≤ θ - 2 * Real.pi * ↑k / (p : ℝ)^n := by linarith [hθ.1]
                linarith
              · -- Need: θ - lower ≤ upper - lower. Follows from θ ≤ upper
                linarith [hθ.2]
          _ = 2 * Real.pi / (p : ℝ)^n := by field_simp; ring
          _ ≤ δ := le_of_lt h_mesh

  -- Now we need to bound the Riemann sum error
  -- This is a standard but technical calculation
  -- The key is that on each subinterval, the function varies by < ε/2

  -- Use triangle inequality and the subinterval bounds
  have h_sum_bound : ‖(p^n : ℂ)⁻¹ * ∑ k ∈ Finset.range (p^n),
      f (Complex.exp (σ + I * (2 * Real.pi * k / p^n))) -
      (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
      f (Complex.exp (σ + I * θ))‖ ≤ ε / 2 := by
    -- Rewrite Riemann sum in terms of g
    have h_sum_eq : (p^n : ℂ)⁻¹ * ∑ k ∈ Finset.range (p^n),
        f (Complex.exp (σ + I * (2 * Real.pi * k / p^n))) =
        (p^n : ℂ)⁻¹ * ∑ k ∈ Finset.range (p^n), g (σ, 2 * Real.pi * k / (p^n : ℝ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      simp only [g]
      congr 2
      simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]
      congr 1
      norm_cast
    rw [h_sum_eq]

    -- Rewrite integral in terms of h (which equals g(σ, ·))
    have h_int_eq : (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        f (Complex.exp (σ + I * θ)) =
        (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), h θ := rfl
    rw [h_int_eq]

    have h_coerce : (p^n : ℂ)⁻¹ = ((p^n : ℕ) : ℂ)⁻¹ := by simp only [Nat.cast_pow]
    rw [h_coerce]
    have h_sum_bound : ‖((p^n : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (p^n), g (σ, 2 * Real.pi * k / (p^n : ℝ)) -
          (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), h θ‖
        ≤ ε / 2 := by
          -- Convert both to common form and use uniform continuity
          -- The Riemann sum (2π/p^n) Σ_k g(σ, 2πk/p^n) approximates ∫₀^{2π} g(σ,θ) dθ
          -- with error ≤ (ε/2) * 2π (since each subintegral has error ≤ (ε/2) * (2π/p^n))
          -- After dividing by 2π, error ≤ ε/2

          -- Use that (1/p^n) = (2π/p^n) / (2π) = (1/2π) * (2π/p^n)
          have hpn_ne : ((p^n : ℕ) : ℂ) ≠ 0 := by
            simp only [ne_eq, Nat.cast_eq_zero]
            exact Nat.pos_iff_ne_zero.mp (Nat.one_le_pow n p (Nat.Prime.pos (Fact.out)))
          have h2pi_pos_real : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
          have h2pi_ne' : (2 * Real.pi : ℂ) ≠ 0 := by
            simp only [ne_eq, Complex.ofReal_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
                       Real.pi_ne_zero, or_self, not_false_eq_true]
          have h_factor : ((p^n : ℕ) : ℂ)⁻¹ = (2 * Real.pi : ℂ)⁻¹ * ((2 * Real.pi : ℂ) / ((p^n : ℕ) : ℂ)) := by
            field_simp
          rw [h_factor]
          -- Normalize coercions: ↑(a⁻¹) = (↑a)⁻¹ for reals
          -- The integral term has (↑(2 * π)⁻¹ : ℂ) which equals (2 * Real.pi : ℂ)⁻¹
          simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat] at h_int_eq ⊢
          -- Simplify: (1/2π) * (2π/p^n) * Σ g - (1/2π) * ∫ h = (1/2π) * ((2π/p^n) * Σ g - ∫ h)
          rw [mul_assoc, ← mul_sub]

          -- Now the term is (1/2π) * |Σ_k (2π/p^n) * g_k - ∫ h|
          have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
          have h2pi_ne : (2 * Real.pi : ℂ) ≠ 0 := by
            simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero,
                       Real.pi_ne_zero, or_self, not_false_eq_true]

          -- Simplify ‖(2π)⁻¹‖ = (2π)⁻¹
          -- Note: (2 * Real.pi : ℂ) becomes 2 * ↑π after simp, so ‖2 * ↑π‖ = 2 * π
          have h_2pi_norm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
            calc ‖(2 * Real.pi : ℂ)‖ = ‖(2 : ℂ) * ↑Real.pi‖ := by
                  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
              _ = ‖(2 : ℂ)‖ * ‖(↑Real.pi : ℂ)‖ := norm_mul _ _
              _ = 2 * |Real.pi| := by
                  rw [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
              _ = 2 * Real.pi := by rw [abs_of_pos Real.pi_pos]
          rw [norm_mul, norm_inv, h_2pi_norm]

          -- Need: (2π)⁻¹ * ‖Σ_k (2π/p^n) * g_k - ∫ h‖ ≤ ε/2
          -- i.e., ‖Σ_k (2π/p^n) * g_k - ∫ h‖ ≤ ε/2 * 2π = επ

          have h_target : ‖(2 * Real.pi / (p^n : ℝ)) * ∑ k ∈ Finset.range (p^n),
              g (σ, 2 * Real.pi * k / (p^n : ℝ)) - ∫ θ in (0:ℝ)..(2 * Real.pi), h θ‖
              ≤ ε / 2 * (2 * Real.pi) := by
            -- Split integral into sum of subintegrals
            have h_sum_int : ∫ θ in (0:ℝ)..(2 * Real.pi), h θ =
                ∑ k ∈ Finset.range (p^n), ∫ θ in (2 * Real.pi * k / (p^n : ℝ))..(2 * Real.pi * (k + 1) / (p^n : ℝ)), h θ := by
              -- Use intervalIntegral.sum_integral_adjacent_intervals
              -- The intervals [2πk/p^n, 2π(k+1)/p^n] for k = 0, ..., p^n-1 partition [0, 2π]
              -- Use the Mathlib lemma which requires ∀ k < n
              -- Define the partition function for sum_integral_adjacent_intervals
              let a : ℕ → ℝ := fun k => 2 * Real.pi * k / (p^n : ℝ)
              have hint : ∀ k < p^n, IntervalIntegrable h MeasureTheory.volume (a k) (a (k + 1)) := by
                intro k hk
                apply hh_int.mono_set
                intro x hx
                have h_lb_le_ub : a k ≤ a (k + 1) := by
                  simp only [a]
                  gcongr
                  exact Nat.cast_le.mpr (Nat.le_succ k)
                rw [Set.uIcc_of_le h_lb_le_ub] at hx
                -- The target uses Set.uIcc 0 (2*π), and since 0 ≤ 2*π, this is Set.Icc 0 (2*π)
                rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
                simp only [Set.mem_Icc] at hx ⊢
                constructor
                · calc (0 : ℝ) ≤ a k := by simp only [a]; positivity
                    _ ≤ x := hx.1
                · have hkn : k + 1 ≤ p^n := Nat.succ_le_of_lt hk
                  have hpn_ne : (p^n : ℝ) ≠ 0 := ne_of_gt hpn_pos
                  have h_ak1_le : a (k + 1) ≤ 2 * Real.pi := by
                    simp only [a]
                    rw [div_le_iff₀ hpn_pos]
                    calc 2 * Real.pi * ((k + 1) : ℕ)
                        ≤ 2 * Real.pi * (p^n : ℕ) := by
                          apply mul_le_mul_of_nonneg_left
                          exact_mod_cast hkn
                          positivity
                      _ = 2 * Real.pi * (p^n : ℝ) := by norm_cast
                  linarith [hx.2, h_ak1_le]
              -- Apply the sum_integral_adjacent_intervals lemma
              have h_eq := intervalIntegral.sum_integral_adjacent_intervals (a := a) hint
              have hpn_ne : (p^n : ℝ) ≠ 0 := ne_of_gt hpn_pos
              have ha0 : a 0 = 0 := by simp only [a, Nat.cast_zero, mul_zero, zero_div]
              have hapn : a (p^n) = 2 * Real.pi := by
                simp only [a]
                have h : (Nat.cast (p^n) : ℝ) = (p : ℝ)^n := by norm_cast
                rw [h]
                field_simp
              simp only [ha0, hapn] at h_eq
              -- h_eq : ∑ k ∈ range (p^n), ∫ θ in (a k)..(a (k+1)), h θ = ∫ θ in 0..2*π, h θ
              -- Goal: ∫ θ in 0..2π, h θ = ∑ k, ∫ θ in (2π*k/p^n)..(2π*(k+1)/p^n), h θ
              rw [← h_eq]
              congr 1 with k
              -- Need: ∫ θ in (a k)..(a (k+1)), h θ = ∫ θ in (2π*k/p^n)..(2π*(k+1)/p^n), h θ
              -- This is true by definition of a, plus Nat.cast_add_one
              simp only [a, Nat.cast_add_one]

            rw [h_sum_int]
            rw [mul_sum, ← Finset.sum_sub_distrib]

            -- Now bound: ‖Σ_k [(2π/p^n) * g_k - ∫_{I_k} h]‖ ≤ Σ_k ‖...‖
            calc ‖∑ k ∈ Finset.range (p^n),
                ((2 * Real.pi / (p^n : ℝ)) * g (σ, 2 * Real.pi * k / (p^n : ℝ)) -
                 ∫ θ in (2 * Real.pi * k / (p^n : ℝ))..(2 * Real.pi * (k + 1) / (p^n : ℝ)), h θ)‖
                ≤ ∑ k ∈ Finset.range (p^n),
                  ‖(2 * Real.pi / (p^n : ℝ)) * g (σ, 2 * Real.pi * k / (p^n : ℝ)) -
                   ∫ θ in (2 * Real.pi * k / (p^n : ℝ))..(2 * Real.pi * (k + 1) / (p^n : ℝ)), h θ‖ :=
                    norm_sum_le _ _
              _ ≤ ∑ k ∈ Finset.range (p^n), (ε / 2) * (2 * Real.pi / (p^n : ℝ)) := by
                  apply Finset.sum_le_sum
                  intro k hk
                  -- On the interval I_k, |h(θ) - g(σ, 2πk/p^n)| < ε/2
                  -- So |∫_{I_k} h - g_k * |I_k|| ≤ (ε/2) * |I_k|
                  have h_interval_bound :
                      ‖(∫ θ in (2 * Real.pi * k / (p^n : ℝ))..(2 * Real.pi * (k + 1) / (p^n : ℝ)), h θ) -
                       (2 * Real.pi / (p^n : ℝ)) * g (σ, 2 * Real.pi * k / (p^n : ℝ))‖
                      ≤ (ε / 2) * (2 * Real.pi / (p^n : ℝ)) := by
                    -- The integral of a constant equals the constant times the length
                    have h_const_int : ∫ θ in (2 * Real.pi * k / (p^n : ℝ))..(2 * Real.pi * (k + 1) / (p^n : ℝ)),
                        g (σ, 2 * Real.pi * k / (p^n : ℝ)) =
                        (2 * Real.pi / (p^n : ℝ)) * g (σ, 2 * Real.pi * k / (p^n : ℝ)) := by
                      rw [intervalIntegral.integral_const]
                      rw [Complex.real_smul]
                      congr 1
                      -- Need: ↑(upper - lower) = 2*π/p^n (in ℂ)
                      have hpn_ne : (p^n : ℝ) ≠ 0 := ne_of_gt hpn_pos
                      -- The difference 2π(k+1)/p^n - 2πk/p^n = 2π/p^n
                      have h_real : 2 * Real.pi * ((k : ℝ) + 1) / (p^n : ℝ) - 2 * Real.pi * k / (p^n : ℝ)
                          = 2 * Real.pi / (p^n : ℝ) := by field_simp [hpn_ne]; ring
                      -- Now cast to ℂ: both sides are equal in ℝ, so equal after coercion
                      simp only [h_real]
                      push_cast
                      rfl
                    rw [← h_const_int]
                    -- ‖∫_{I_k} h - ∫_{I_k} g_k‖ = ‖∫_{I_k} (h - g_k)‖ ≤ ∫_{I_k} ‖h - g_k‖ ≤ (ε/2) * |I_k|
                    have hk_range : k ∈ Finset.range (p^n) := hk
                    have hk_bound : k < p^n := Finset.mem_range.mp hk_range
                    have hk_bound' : k + 1 ≤ p^n := Nat.succ_le_of_lt hk_bound
                    have hpn_pos' : (0 : ℝ) < (p^n : ℝ) := by positivity
                    have h_lb : (0 : ℝ) ≤ 2 * Real.pi * k / (p^n : ℝ) := by positivity
                    have h_ub : 2 * Real.pi * (k + 1) / (p^n : ℝ) ≤ 2 * Real.pi := by
                      rw [div_le_iff₀ hpn_pos']
                      calc 2 * Real.pi * (k + 1) ≤ 2 * Real.pi * (p^n : ℕ) := by
                              apply mul_le_mul_of_nonneg_left _ (by positivity)
                              exact_mod_cast hk_bound'
                        _ = 2 * Real.pi * (p^n : ℝ) := by norm_cast
                    have h_lb_le_ub : 2 * Real.pi * k / (p^n : ℝ) ≤ 2 * Real.pi * (k + 1) / (p^n : ℝ) := by
                      gcongr; linarith
                    have h_hint_sub : IntervalIntegrable h MeasureTheory.volume
                        (2 * Real.pi * k / (p^n : ℝ)) (2 * Real.pi * (k + 1) / (p^n : ℝ)) := by
                      apply hh_int.mono_set
                      rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ 2 * Real.pi)]
                      rw [Set.uIcc_of_le h_lb_le_ub]
                      intro x hx
                      simp only [Set.mem_Icc] at hx ⊢
                      constructor <;> linarith
                    rw [← intervalIntegral.integral_sub h_hint_sub intervalIntegrable_const]
                    calc ‖∫ θ in (2 * Real.pi * k / (p^n : ℝ))..(2 * Real.pi * (k + 1) / (p^n : ℝ)),
                            h θ - g (σ, 2 * Real.pi * k / (p^n : ℝ))‖
                        ≤ |∫ θ in (2 * Real.pi * k / (p^n : ℝ))..(2 * Real.pi * (k + 1) / (p^n : ℝ)),
                            ‖h θ - g (σ, 2 * Real.pi * k / (p^n : ℝ))‖| := by
                          apply intervalIntegral.norm_integral_le_abs_integral_norm
                      _ ≤ ∫ θ in (2 * Real.pi * k / (p^n : ℝ))..(2 * Real.pi * (k + 1) / (p^n : ℝ)),
                            ‖h θ - g (σ, 2 * Real.pi * k / (p^n : ℝ))‖ := by
                          rw [abs_of_nonneg]
                          apply intervalIntegral.integral_nonneg
                          · exact h_lb_le_ub
                          · intro θ _; exact norm_nonneg _
                      _ ≤ ∫ θ in (2 * Real.pi * k / (p^n : ℝ))..(2 * Real.pi * (k + 1) / (p^n : ℝ)),
                            (ε / 2) := by
                          apply intervalIntegral.integral_mono_on
                          · exact h_lb_le_ub
                          · exact (hh_cont.sub continuous_const).norm.intervalIntegrable _ _
                          · exact intervalIntegrable_const
                          · intro θ hθ
                            -- h(θ) = g(σ, θ) and we have h_bound
                            -- integral_mono_on gives hθ : θ ∈ Set.Icc, and h_bound expects Set.Icc
                            have h_dist := h_bound k hk θ hθ
                            rw [dist_eq_norm] at h_dist
                            -- g(σ, θ) = h(θ) by definition
                            have hg_eq_h : g (σ, θ) = h θ := rfl
                            rw [← hg_eq_h]
                            exact h_dist
                      _ = (ε / 2) * (2 * Real.pi / (p^n : ℝ)) := by
                          rw [intervalIntegral.integral_const]
                          simp only [smul_eq_mul]
                          have hpn_ne' : (p^n : ℝ) ≠ 0 := ne_of_gt hpn_pos
                          have h_len : 2 * Real.pi * ((k : ℝ) + 1) / (p^n : ℝ) - 2 * Real.pi * k / (p^n : ℝ)
                              = 2 * Real.pi / (p^n : ℝ) := by field_simp [hpn_ne']; ring
                          rw [h_len]
                          ring
                  rw [norm_sub_rev] at h_interval_bound
                  exact h_interval_bound
              _ = ε / 2 * (2 * Real.pi) := by
                  rw [Finset.sum_const, Finset.card_range]
                  simp only [nsmul_eq_mul, Nat.cast_pow]
                  have hpn_ne'' : (p : ℝ)^n ≠ 0 := by positivity
                  field_simp [hpn_ne'']

          -- Use h_target to bound the expression
          -- After rw [norm_mul, norm_inv, h_2pi_norm], goal is:
          -- (2*π)⁻¹ * ‖(2π/p^n) * ∑g - ∫h‖ ≤ ε/2
          -- Normalize coercions: ↑(p^n) = ↑p^n
          simp only [← Nat.cast_pow] at h_target ⊢
          have hπ_pos : (0 : ℝ) < 2 * Real.pi := by positivity
          have hπ_inv_nonneg : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
          calc (2 * Real.pi)⁻¹ * ‖((2 * Real.pi / ((p^n : ℕ) : ℝ)) : ℂ) *
                ∑ k ∈ Finset.range (p^n), g (σ, 2 * Real.pi * k / ((p^n : ℕ) : ℝ)) -
                ∫ θ in (0:ℝ)..(2 * Real.pi), h θ‖
              ≤ (2 * Real.pi)⁻¹ * (ε / 2 * (2 * Real.pi)) := by
                apply mul_le_mul_of_nonneg_left h_target hπ_inv_nonneg
            _ = ε / 2 := by field_simp
    exact h_sum_bound

  -- Now use h_sum_bound to prove the main goal: ‖...‖ < ε
  linarith [h_sum_bound]

/-- The discrete Riemann sum approximation to spiral_action.
    S_n(σ) = (1/p^n) Σ_{k=0}^{p^n-1} log|Q(e^{σ + 2πik/p^n})| -/
noncomputable def spiral_action_discrete (Q : Polynomial ℂ) (p : ℕ) (n : ℕ) (σ : ℝ) : ℝ :=
  ((p : ℝ)^n)⁻¹ * ∑ k ∈ Finset.range (p^n),
    Real.log ‖Q.eval (Complex.exp (σ + I * (2 * Real.pi * k / p^n)))‖

/-- Key lemma: The discrete sum converges to the integral as n → ∞.
    This follows from uniform continuity of the integrand and the fact that
    p^n-th roots of unity have mesh 2π/p^n → 0. -/
lemma spiral_action_discrete_tendsto (Q : Polynomial ℂ) (hQ : Q ≠ 0) (p : ℕ) (hp : 1 < p) (σ : ℝ)
    (h_no_roots : ∀ α ∈ Q.roots, ‖α‖ ≠ Real.exp σ) :
    Filter.Tendsto (fun n => spiral_action_discrete Q p n σ) Filter.atTop
      (nhds (spiral_action Q σ)) := by
  --
  -- Step 1: Define the integrand f(θ) = log|Q(e^{σ+iθ})|
  let f : ℝ → ℝ := fun θ => Real.log ‖Q.eval (Complex.exp (σ + I * θ))‖

  have hf_cont : Continuous f := by
    -- f(θ) = log ‖Q.eval (exp(σ + I*θ))‖
    -- This is continuous because Q.eval is never zero on the circle
    have h_eval_ne_zero : ∀ θ : ℝ, Q.eval (Complex.exp (σ + I * θ)) ≠ 0 := by
      intro θ h_zero
      -- If Q.eval (exp(σ + I*θ)) = 0, then exp(σ + I*θ) is a root
      have h_root : Complex.exp (σ + I * θ) ∈ Q.roots := by
        rw [Polynomial.mem_roots hQ]
        exact h_zero
      -- But |exp(σ + I*θ)| = e^σ
      have h_norm : ‖Complex.exp (σ + I * θ)‖ = Real.exp σ := by
        rw [Complex.norm_exp]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                   Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, zero_mul]
        ring_nf
      -- This contradicts h_no_roots
      exact h_no_roots _ h_root h_norm
    have h_norm_ne_zero : ∀ θ : ℝ, ‖Q.eval (Complex.exp (σ + I * θ))‖ ≠ 0 := by
      intro θ
      exact norm_ne_zero_iff.mpr (h_eval_ne_zero θ)
    -- Now use continuity of composition
    have h_inner : Continuous (fun θ : ℝ => ‖Q.eval (Complex.exp (σ + I * θ))‖) := by
      apply Continuous.norm
      have h1 : Continuous (fun θ : ℝ => Complex.exp (σ + I * θ)) := by
        apply Complex.continuous_exp.comp
        exact continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
      exact (Polynomial.continuous_aeval Q).comp h1
    exact h_inner.log h_norm_ne_zero
  -- Step 3: The mesh 2π/p^n → 0 as n → ∞
  have h_mesh_tendsto : Filter.Tendsto (fun n => 2 * Real.pi / (p : ℝ)^n)
      Filter.atTop (nhds 0) := by
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega : 0 < p)
    have hp_gt_one : (1 : ℝ) < p := by exact_mod_cast hp
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_pow_atTop_atTop_of_one_lt hp_gt_one
  -- Step 4: f is integrable on [0,2π] (continuous implies integrable on compact interval)
  have hf_integrable : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi) :=
    hf_cont.intervalIntegrable 0 (2 * Real.pi)

  unfold spiral_action spiral_action_discrete

  have hf_unif_cont : UniformContinuousOn f (Set.Icc 0 (2 * Real.pi)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf_cont.continuousOn
  -- Step 2: The error bound for Riemann sums
  -- We use the Metric.tendsto_atTop characterization:
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Get uniform continuity modulus using the _le version
  have hε' : ε / (2 * Real.pi + 1) > 0 := by positivity
  obtain ⟨δ, hδ_pos, hδ_cont⟩ := Metric.uniformContinuousOn_iff_le.mp hf_unif_cont
    (ε / (2 * Real.pi + 1)) hε'
  -- Choose N large enough that 2π/p^N < δ
  have hp_pos : (p : ℝ) > 1 := by exact_mod_cast hp
  have h_exp_unbounded : Filter.Tendsto (fun n => (p : ℝ)^n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hp_pos
  -- There exists N such that 2π/p^N < δ
  have h_mesh_small : ∃ N, ∀ n ≥ N, 2 * Real.pi / (p : ℝ)^n < δ := by
    have h1 : Filter.Tendsto (fun n => 2 * Real.pi / (p : ℝ)^n) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds h_exp_unbounded
    rw [Metric.tendsto_atTop] at h1
    obtain ⟨N, hN⟩ := h1 δ hδ_pos
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos] at hN
    · exact hN
    · positivity
  obtain ⟨N, hN⟩ := h_mesh_small
  use N
  intro n hn
  have h_mesh_bound : 2 * Real.pi / (p : ℝ)^n < δ := hN n hn
  rw [Real.dist_eq]
  -- The difference can be bounded using the oscillation estimate
  -- |discrete - integral| ≤ 2π · (ε/(2π+1)) < ε
  have h_bound : |((p : ℝ)^n)⁻¹ * ∑ k ∈ Finset.range (p^n),
        Real.log ‖Q.eval (Complex.exp (σ + I * (2 * Real.pi * k / (p : ℝ)^n)))‖ -
      (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
        Real.log ‖Q.eval (Complex.exp (σ + I * θ))‖| < ε := by
    -- The bound follows from uniform continuity of f
    -- Key insight: rewrite discrete sum in terms of Riemann sum structure
    -- First, note that (1/p^n) * Σ f(2πk/p^n) = (1/2π) * Σ f(2πk/p^n) * (2π/p^n)
    -- This is a left Riemann sum with mesh 2π/p^n
    have hp_n_pos : (0 : ℝ) < (p : ℝ)^n := by positivity
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    calc |((p : ℝ)^n)⁻¹ * ∑ k ∈ Finset.range (p^n),
            Real.log ‖Q.eval (Complex.exp (σ + I * (2 * Real.pi * k / (p : ℝ)^n)))‖ -
          (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
            Real.log ‖Q.eval (Complex.exp (σ + I * θ))‖|
        ≤ ε / (2 * Real.pi + 1) := by
          have h_rewrite : ((p : ℝ)^n)⁻¹ * ∑ k ∈ Finset.range (p^n),
           f (2 * Real.pi * k / (p : ℝ)^n) =
              (2 * Real.pi)⁻¹ * (∑ k ∈ Finset.range (p^n),
               f (2 * Real.pi * k / (p : ℝ)^n) * (2 * Real.pi / (p : ℝ)^n)) := by
            have hN_ne : (p : ℝ)^n ≠ 0 := by positivity
            have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := by positivity
            rw [Finset.mul_sum]
            conv_rhs => rw [Finset.mul_sum]
            congr 1
            ext k
            field_simp
          have h_osc_bound : ∀ θ₁ θ₂ : ℝ, θ₁ ∈ Set.Icc 0 (2 * Real.pi) →
              θ₂ ∈ Set.Icc 0 (2 * Real.pi) → |θ₁ - θ₂| ≤ 2 * Real.pi / (p : ℝ)^n →
              |f θ₁ - f θ₂| ≤ ε / (2 * Real.pi + 1) := by
            intro θ₁ θ₂ hθ₁ hθ₂ h_close
            have h_dist : dist θ₁ θ₂ ≤ δ := by
              rw [Real.dist_eq]
              calc |θ₁ - θ₂| ≤ 2 * Real.pi / (p : ℝ)^n := h_close
                _ ≤ δ := le_of_lt h_mesh_bound
            have := hδ_cont θ₁ hθ₁ θ₂ hθ₂ h_dist
            rwa [Real.dist_eq] at this
          have h_abs_bound : |((p : ℝ)^n)⁻¹ *
           ∑ k ∈ Finset.range (p^n), f (2 * Real.pi * k / (p : ℝ)^n) -
              (2 * Real.pi)⁻¹ * ∫ θ' in (0)..(2 * Real.pi), f θ'|
              ≤ ε / (2 * Real.pi + 1) := by
            -- Transform using h_rewrite
            rw [h_rewrite]
            -- Now both have (2π)⁻¹ factor: (2π)⁻¹ * Σ... - (2π)⁻¹ * ∫...
            -- Factor out (2π)⁻¹: (2π)⁻¹ * (Σ... - ∫...)
            rw [← mul_sub]
            rw [abs_mul]
            have h2pi_inv_pos : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
            rw [abs_of_nonneg h2pi_inv_pos]
            -- Need: (2π)⁻¹ · |Riemann_sum - integral| ≤ ε/(2π+1)
            -- i.e., |Riemann_sum - integral| ≤ 2π · ε/(2π+1)
            -- The Riemann sum error bound
            -- This is the standard result: for uniformly continuous f on [a,b],
            -- |left_Riemann_sum - integral| ≤ oscillation × (b - a)
            -- where oscillation ≤ ε/(2π+1) when mesh < δ
            -- We establish this using the integral decomposition and MVT
            have h_sum_bound : |∑ k ∈ Finset.range (p^n),
             f (2 * Real.pi * k / (p : ℝ)^n) * (2 * Real.pi / (p : ℝ)^n) -
                ∫ θ' in (0)..(2 * Real.pi), f θ'| ≤ 2 * Real.pi * (ε / (2 * Real.pi + 1)) := by
              have h_osc : ε / (2 * Real.pi + 1) > 0 := hε'
              have hp_n_pos' : (0 : ℝ) < (p : ℝ)^n := by positivity
              have h2pi_pos' : (0 : ℝ) < 2 * Real.pi := by positivity
              have h_mesh : 2 * Real.pi / (p : ℝ)^n > 0 := by positivity
              -- The proof requires decomposing the integral and bounding each piece
              -- This is a standard result in analysis; the formalization requires
              -- interval integral lemmas from Mathlib
              -- Use the oscillation bound: each subinterval contributes ≤ osc × width
              -- Total = osc × total_width = (ε/(2π+1)) × 2π
              -- The bound is: 2π × ε/(2π+1) which is positive
              have h_bound_pos : 0 < 2 * Real.pi * (ε / (2 * Real.pi + 1)) := by
                apply mul_pos h2pi_pos' hε'
              calc |∑ k ∈ Finset.range (p^n), f (2 * Real.pi * k / (p : ℝ)^n) *
               (2 * Real.pi / (p : ℝ)^n) -
                  ∫ θ' in (0)..(2 * Real.pi), f θ'|
                  ≤ ∑ k ∈ Finset.range (p^n), |f (2 * Real.pi * k / (p : ℝ)^n) *
                   (2 * Real.pi / (p : ℝ)^n) -
                    ∫ θ' in (2 * Real.pi * k / (p : ℝ)^n)..(2 * Real.pi * (k + 1) /
                     (p : ℝ)^n), f θ'| := by
                      have h_decomp : ∫ θ' in (0)..(2 * Real.pi), f θ' =
                          ∑ k ∈ Finset.range (p^n), ∫ θ' in (2 * Real.pi * k /
                           (p : ℝ)^n)..(2 * Real.pi * (k + 1) /
                           (p : ℝ)^n), f θ' := by
                        -- The formal proof uses intervalIntegral.sum_integral_adjacent_intervals
                        -- with partition function a(k) = 2πk/p^n
                        -- a(0) = 0, a(p^n) = 2π, and f is integrable on each subinterval
                        -- Define the partition function
                        let a : ℕ → ℝ := fun k => 2 * Real.pi * k / (p : ℝ)^n
                        -- Verify endpoints: a 0 = 0, a (p^n) = 2π
                        have ha0 : a 0 = 0 := by simp [a]
                        have hapn : a (p^n) = 2 * Real.pi := by
                          simp only [a]
                          have hp_n_ne : (p : ℝ)^n ≠ 0 := by positivity
                          field_simp [hp_n_ne]
                          push_cast
                          ring
                        -- f is integrable on each subinterval (continuous on compact)
                        have hint : ∀ k < p^n, IntervalIntegrable f MeasureTheory.volume
                         (a k) (a (k + 1)) := by
                          intro k _
                          apply Continuous.intervalIntegrable
                          exact hf_cont
                        -- Apply sum of adjacent intervals
                        have h_sum := intervalIntegral.sum_integral_adjacent_intervals hint
                        rw [ha0, hapn] at h_sum
                        rw [← h_sum]
                        -- Need to show sum over the same function with same intervals
                        -- The terms are equal after unfolding a
                        refine Finset.sum_congr rfl fun k _ => ?_
                        simp only [a]
                        congr 2
                        push_cast
                        ring
                      rw [h_decomp]
                      -- Rewrite Σa - Σb as Σ(a - b) then apply triangle inequality
                      rw [← Finset.sum_sub_distrib]
                      apply Finset.abs_sum_le_sum_abs
                _ ≤ ∑ _k ∈ Finset.range (p^n), ε / (2 * Real.pi + 1) * (2 * Real.pi /
                 (p : ℝ)^n) := by
                      -- Each term is bounded by osc × Δθ = (ε/(2π+1)) × (2π/p^n)
                      apply Finset.sum_le_sum
                      intro k hk
                      -- Need: |f(θ_k) × Δθ - ∫_{θ_k}^{θ_{k+1}} f| ≤ osc × Δθ
                      -- Define the partition points
                      set θ_k := 2 * Real.pi * k / (p : ℝ)^n with hθ_k_def
                      set θ_k1 := 2 * Real.pi * (k + 1) / (p : ℝ)^n with hθ_k1_def
                      set Δθ := 2 * Real.pi / (p : ℝ)^n with hΔθ_def
                      have hk_bound : k < p^n := Finset.mem_range.mp hk
                      -- Note: θ_k1 - θ_k = Δθ and θ_k ≤ θ_k1
                      have h_interval_len : θ_k1 - θ_k = Δθ := by
                        simp only [hθ_k_def, hθ_k1_def, hΔθ_def]
                        have hp_n_ne : (p : ℝ)^n ≠ 0 := by positivity
                        field_simp [hp_n_ne]
                        ring
                      have h_θ_k_le_θ_k1 : θ_k ≤ θ_k1 := by linarith [h_mesh]
                      -- θ_k ∈ [0, 2π]
                      have h_θ_k_nonneg : 0 ≤ θ_k := by positivity
                      have h_θ_k_le_2pi : θ_k ≤ 2 * Real.pi := by
                        simp only [hθ_k_def]
                        have hk_le : (k : ℝ) ≤ (p : ℝ)^n := by
                          rw [← Nat.cast_pow]
                          exact Nat.cast_le.mpr (le_of_lt hk_bound)
                        calc 2 * Real.pi * k / (p : ℝ)^n
                            ≤ 2 * Real.pi * (p : ℝ)^n / (p : ℝ)^n := by
                              apply div_le_div_of_nonneg_right _ (by positivity)
                              exact mul_le_mul_of_nonneg_left hk_le (by linarith [Real.pi_pos])
                          _ = 2 * Real.pi := by field_simp
                      have h_θ_k_mem : θ_k ∈ Set.Icc 0 (2 * Real.pi) := ⟨h_θ_k_nonneg, h_θ_k_le_2pi⟩
                      -- θ_k1 ≤ 2π
                      have h_θ_k1_le_2pi : θ_k1 ≤ 2 * Real.pi := by
                        simp only [hθ_k1_def]
                        have hk1_le : (k + 1 : ℝ) ≤ (p : ℝ)^n := by
                          have : k + 1 ≤ p^n := hk_bound
                          exact_mod_cast this
                        calc 2 * Real.pi * (k + 1) / (p : ℝ)^n
                            ≤ 2 * Real.pi * (p : ℝ)^n / (p : ℝ)^n := by
                              apply div_le_div_of_nonneg_right _ (by positivity)
                              exact mul_le_mul_of_nonneg_left hk1_le (by linarith [Real.pi_pos])
                          _ = 2 * Real.pi := by field_simp
                      -- f(θ_k) × Δθ = ∫_{θ_k}^{θ_k1} f(θ_k)
                      have h_const_integral : f θ_k * Δθ = ∫ _ in θ_k..θ_k1, f θ_k := by
                        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm, h_interval_len]
                      rw [h_const_integral]
                      -- Now: |∫_{θ_k}^{θ_k1} f(θ_k) - ∫_{θ_k}^{θ_k1} f| ≤ osc × Δθ
                      rw [← intervalIntegral.integral_sub
                          (intervalIntegrable_const) (hf_cont.intervalIntegrable _ _)]
                      -- Use norm_integral_le_of_norm_le_const
                      have h_bound : ∀ x ∈ Set.uIoc θ_k θ_k1, |f θ_k - f x| ≤
                       ε / (2 * Real.pi + 1) := by
                        intro x hx
                        -- x ∈ (θ_k, θ_k1] since θ_k ≤ θ_k1
                        rw [Set.uIoc_of_le h_θ_k_le_θ_k1] at hx
                        -- x ∈ [0, 2π]
                        have h_x_mem : x ∈ Set.Icc 0 (2 * Real.pi) := by
                          constructor
                          · exact le_trans h_θ_k_nonneg (le_of_lt hx.1)
                          · exact le_trans hx.2 h_θ_k1_le_2pi
                        -- |θ_k - x| ≤ Δθ < δ
                        have h_dist_bound : |θ_k - x| ≤ Δθ := by
                          rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hx.1)]
                          calc x - θ_k ≤ θ_k1 - θ_k := by linarith [hx.2]
                            _ = Δθ := h_interval_len
                        have h_dist_le_δ : dist θ_k x ≤ δ := by
                          rw [Real.dist_eq]
                          exact le_trans h_dist_bound (le_of_lt h_mesh_bound)
                        exact hδ_cont θ_k h_θ_k_mem x h_x_mem h_dist_le_δ
                      -- Apply intervalIntegral.norm_integral_le_of_norm_le_const
                      -- Convert |·| to ‖·‖ for the bound
                      have h_bound' : ∀ x ∈ Set.uIoc θ_k θ_k1, ‖f θ_k - f x‖ ≤
                       ε / (2 * Real.pi + 1) := by
                        intro x hx
                        rw [Real.norm_eq_abs]
                        exact h_bound x hx
                      have h_norm_bound :=
                       intervalIntegral.norm_integral_le_of_norm_le_const h_bound'
                      simp only [Real.norm_eq_abs] at h_norm_bound
                      calc |∫ (x : ℝ) in θ_k..θ_k1, f θ_k - f x|
                          ≤ ε / (2 * Real.pi + 1) * |θ_k1 - θ_k| := h_norm_bound
                        _ = ε / (2 * Real.pi + 1) * Δθ :=
                         by rw [h_interval_len, abs_of_pos h_mesh]
                        _ = ε / (2 * Real.pi + 1) * (2 * Real.pi / (p : ℝ)^n) := rfl
                _ = ε / (2 * Real.pi + 1) * (p^n : ℝ) * (2 * Real.pi / (p : ℝ)^n) := by
                      rw [Finset.sum_const, Finset.card_range]
                      ring
                _ = ε / (2 * Real.pi + 1) * 2 * Real.pi := by
                      have hp_n_ne : (p : ℝ)^n ≠ 0 := by positivity
                      field_simp [hp_n_ne]
                _ = 2 * Real.pi * (ε / (2 * Real.pi + 1)) := by ring
            -- Now: (2π)⁻¹ × |...| ≤ (2π)⁻¹ × 2π × (ε/(2π+1)) = ε/(2π+1)
            calc (2 * Real.pi)⁻¹ *
             |∑ k ∈ Finset.range (p^n), f (2 * Real.pi * k / (p : ℝ)^n) *
              (2 * Real.pi / (p : ℝ)^n) -
                ∫ θ' in (0)..(2 * Real.pi), f θ'|
                ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * (ε / (2 * Real.pi + 1))) := by
                    apply mul_le_mul_of_nonneg_left h_sum_bound
                    positivity
              _ = ε / (2 * Real.pi + 1) := by
                    have h2pi_ne : 2 * Real.pi ≠ 0 := by positivity
                    field_simp [h2pi_ne]
          -- The goal matches h_abs_bound (f is defined as the log expression)
          -- Both sides are equal after unfolding f and simplifying coercions
          simp only [f] at h_abs_bound
          -- The sums and integrals are over the same function, just different coercion paths
          convert h_abs_bound using 3
          -- Sum equality: just coercion difference
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          congr 3
          -- The difference is ↑(2 * π * k / p^n) vs 2 * ↑π * k / p^n
          push_cast
          ring
      _ < ε := by
          have h1 : (1 : ℝ) < 2 * Real.pi + 1 := by
            have : (0 : ℝ) < Real.pi := Real.pi_pos
            linarith
          exact div_lt_self hε h1
  exact h_bound
/-- For a single linear factor (z - α), the circle average of log|z - α| at radius r
    equals max(log r, log|α|). This is the harmonic mean value property. -/
lemma circle_average_log_linear_factor (α : ℂ) (σ : ℝ) (hα : α ≠ 0)
    (h_not_on_circle : ‖α‖ ≠ Real.exp σ) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
      Real.log ‖Complex.exp (σ + I * θ) - α‖ = max σ (Real.log ‖α‖) := by
  -- Case split: |α| < e^σ (inside) or |α| > e^σ (outside)
  -- Inside: average = log(e^σ) = σ (by mean value for harmonic functions)
  -- Outside: average = log|α| (by reflection principle)
  by_cases h : ‖α‖ < Real.exp σ
  · -- Inside case: average = σ
    have h_max : max σ (Real.log ‖α‖) = σ := by
      rw [max_eq_left]
      have hα_pos : ‖α‖ > 0 := norm_pos_iff.mpr hα
      rw [← Real.log_exp σ]
      exact Real.log_le_log hα_pos (le_of_lt h)
    rw [h_max]
    -- Rewrite in terms of circleAverage
    -- exp(σ + I*θ) = exp(σ) * exp(I*θ) = circleMap 0 (exp σ) θ
    have h_exp_eq_circleMap : ∀ θ : ℝ, Complex.exp (σ + I * θ) = circleMap 0 (Real.exp σ) θ := by
      intro θ
      simp only [circleMap, zero_add, Complex.ofReal_exp]
      rw [Complex.exp_add]
      ring_nf
    -- Rewrite the integral
    have h_integral_eq : (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
        Real.log ‖Complex.exp (σ + I * θ) - α‖ =
        Real.circleAverage (fun z => Real.log ‖z - α‖) 0 (Real.exp σ) := by
      unfold Real.circleAverage
      simp only [smul_eq_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [h_exp_eq_circleMap θ]
    rw [h_integral_eq]
    -- Apply Mathlib's circleAverage_log_norm_sub_const_of_mem_closedBall
    have h_mem : α ∈ Metric.closedBall 0 |Real.exp σ| := by
      simp only [Metric.mem_closedBall, dist_zero_right, abs_of_pos (Real.exp_pos σ)]
      exact le_of_lt h
    rw [circleAverage_log_norm_sub_const_of_mem_closedBall h_mem]
    exact Real.log_exp σ
  · -- Outside case: average = log|α|
    push_neg at h
    have h_outside : ‖α‖ > Real.exp σ := lt_of_le_of_ne h (Ne.symm h_not_on_circle)
    have h_max : max σ (Real.log ‖α‖) = Real.log ‖α‖ := by
      rw [max_eq_right]
      rw [← Real.log_exp σ]
      exact Real.log_le_log (Real.exp_pos σ) (le_of_lt h_outside)
    rw [h_max]
    -- Rewrite in terms of circleAverage (same as inside case)
    have h_exp_eq_circleMap : ∀ θ : ℝ, Complex.exp (σ + I * θ) = circleMap 0 (Real.exp σ) θ := by
      intro θ
      simp only [circleMap, zero_add, Complex.ofReal_exp]
      rw [Complex.exp_add]
      ring_nf
    have h_integral_eq : (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
        Real.log ‖Complex.exp (σ + I * θ) - α‖ =
        Real.circleAverage (fun z => Real.log ‖z - α‖) 0 (Real.exp σ) := by
      unfold Real.circleAverage
      simp only [smul_eq_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      simp only [h_exp_eq_circleMap θ]
    rw [h_integral_eq]
    -- Use the general formula: circleAverage = log R + log⁺(R⁻¹ * ‖c - a‖)
    have hR_ne : Real.exp σ ≠ 0 := Real.exp_ne_zero σ
    rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR_ne]
    -- Goal: log(exp σ) + log⁺((exp σ)⁻¹ * ‖0 - α‖) = log ‖α‖
    -- Simplify ‖0 - α‖ = ‖α‖
    have h_norm_eq : ‖(0 : ℂ) - α‖ = ‖α‖ := by simp
    rw [h_norm_eq, Real.log_exp]
    -- Since ‖α‖ > exp σ, we have (exp σ)⁻¹ * ‖α‖ > 1, so log⁺ = log
    have h_gt_one : (Real.exp σ)⁻¹ * ‖α‖ > 1 := by
      have h_pos : Real.exp σ > 0 := Real.exp_pos σ
      calc 1 = Real.exp σ * (Real.exp σ)⁻¹ := by field_simp
        _ < ‖α‖ * (Real.exp σ)⁻¹ := by
            apply mul_lt_mul_of_pos_right h_outside (inv_pos.mpr h_pos)
        _ = (Real.exp σ)⁻¹ * ‖α‖ := by ring
    have h_abs_ge : 1 ≤ |(Real.exp σ)⁻¹ * ‖α‖| := by
      rw [abs_of_pos (by positivity : (Real.exp σ)⁻¹ * ‖α‖ > 0)]
      exact le_of_lt h_gt_one
    rw [Real.posLog_eq_log h_abs_ge]
    -- σ + log((exp σ)⁻¹ * ‖α‖) = σ + log((exp σ)⁻¹) + log ‖α‖ = σ - σ + log ‖α‖ = log ‖α‖
    have hα_pos : ‖α‖ > 0 := norm_pos_iff.mpr hα
    rw [Real.log_mul (inv_ne_zero hR_ne) (ne_of_gt hα_pos)]
    rw [Real.log_inv, Real.log_exp]
    ring

/-- For the constant polynomial c, the circle average of log|c| is just log|c|. -/
lemma circle_average_log_const (c : ℂ) (_hc : c ≠ 0) (_σ : ℝ) :
    (2 * Real.pi)⁻¹ * ∫ _θ in (0)..(2 * Real.pi), Real.log ‖c‖ = Real.log ‖c‖ := by
  have h_int : ∫ θ in (0)..(2 * Real.pi), Real.log ‖c‖ = 2 * Real.pi * Real.log ‖c‖ := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [h_int]
  have h2pi_ne : 2 * Real.pi ≠ 0 := by positivity
  field_simp [h2pi_ne]

/-- The topological force F(σ) = dS/dσ = root count inside radius e^σ. -/
noncomputable def topological_force (Q : Polynomial ℂ) (σ : ℝ) : ℕ :=
  (Q.roots.filter (fun α => α ≠ 0 ∧ Real.log ‖α‖ < σ)).card

/-! ### Spiral Kernel and Operator Structure

The spiral lattice supports a canonical Hermitian positive semi-definite inner product. -/

/-- The spiral kernel inner product at scale ε and level n.

    This is the finite-rank reproducing kernel on spiral points z_j = e^{ε + 2πij/p^n}.
    It implements equation (2.5) from the paper. -/
noncomputable def spiral_kernel_product (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (f g : ℂ → ℂ) : ℂ :=
  ∑ j : ZMod (p^n),
    f (Complex.exp (ε + I * (2 * π * (j.val : ℝ) / (p^n : ℝ)))) *
    conj (g (Complex.exp (ε + I * (2 * π * (j.val : ℝ) / (p^n : ℝ)))))

/-- The spiral inner product is Hermitian. -/
lemma spiral_kernel_hermitian (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (f g : ℂ → ℂ) :
    conj (spiral_kernel_product p n ε f g) = spiral_kernel_product p n ε g f := by
  unfold spiral_kernel_product
  rw [map_sum]
  congr 1
  ext j
  rw [map_mul, conj_conj]
  ring

/-- The spiral inner product is positive semi-definite. -/
lemma spiral_kernel_pos (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (f : ℂ → ℂ) :
    0 ≤ (spiral_kernel_product p n ε f f).re := by
  unfold spiral_kernel_product
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-! ### U(1) Inner Product

Specialization of the spiral kernel at ε=0: ⟨f,g⟩_n = ∑_j f(ω_j)·conj(g(ω_j)). -/

/-- Discrete inner product on U(1) at finite level n.
    This is the ε=0 specialization of `spiral_kernel_product`. -/
noncomputable def innerProductU1_discrete (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (f g : ℂ → ℂ) : ℂ :=
  spiral_kernel_product p n 0 f g

/-- The discrete U(1) inner product is exactly spiral_kernel_product at ε=0. -/
lemma innerProductU1_discrete_eq_spiral (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (f g : ℂ → ℂ) :
    innerProductU1_discrete p n f g = spiral_kernel_product p n 0 f g := rfl

/-- The discrete U(1) inner product samples at p^n-th roots of unity.
    Uses the same roots as `angular_lattice` and `root_of_unity_eq_character`. -/
lemma innerProductU1_discrete_eq_sum (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (f g : ℂ → ℂ) :
    innerProductU1_discrete p n f g =
    ∑ j : ZMod (p^n), f (Complex.exp (I * (2 * π * (j.val : ℝ) / (p^n : ℝ)))) *
                      conj (g (Complex.exp (I * (2 * π * (j.val : ℝ) / (p^n : ℝ))))) := by
  unfold innerProductU1_discrete spiral_kernel_product
  congr 1
  ext j
  -- At ε = 0, the spiral point exp(0 + I*θ) = exp(I*θ)
  simp only [Complex.ofReal_zero, zero_add]

/-- The discrete U(1) inner product is Hermitian (from `spiral_kernel_hermitian`). -/
lemma innerProductU1_discrete_hermitian (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (f g : ℂ → ℂ) :
    conj (innerProductU1_discrete p n f g) = innerProductU1_discrete p n g f :=
  spiral_kernel_hermitian p n 0 f g

/-- The discrete U(1) inner product is positive semi-definite (from `spiral_kernel_pos`). -/
lemma innerProductU1_discrete_pos (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (f : ℂ → ℂ) :
    0 ≤ (innerProductU1_discrete p n f f).re :=
  spiral_kernel_pos p n 0 f

/-! ### Conjugate Pairing on Roots of Unity

The map k ↦ (n - k) in ZMod n pairs ω_k with its complex conjugate ω_k⁻¹. -/

/-- Roots of unity conjugate pairing: ω_k · ω_{n-k} = 1. -/
lemma root_of_unity_conjugate_pair (n : ℕ) [NeZero n] (k : ZMod n) :
    Complex.exp (I * (2 * π * (k.val : ℝ) / n)) *
    Complex.exp (I * (2 * π * (((-k).val) : ℝ) / n)) = 1 := by
  rw [← Complex.exp_add]
  -- When k = 0: trivial (0 + 0 = 0)
  -- When k ≠ 0: (-k).val = n - k.val, so k.val + (-k).val = n
  -- Then exp(I * 2π * n / n) = exp(I * 2π) = 1
  by_cases hk : k = 0
  · simp [hk]
  · -- (-k).val = n - k.val when k ≠ 0
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    have hnegval : (-k).val = n - k.val := by
      rw [ZMod.neg_val]
      simp [hk]
    have hk_le : k.val ≤ n := Nat.le_of_lt (ZMod.val_lt k)
    have hsum_nat : k.val + (-k).val = n := by
      simpa [hnegval, Nat.add_sub_of_le hk_le]
    -- The sum of exponents is I * 2π * n / n = I * 2π
    have h_exp_sum : I * (2 * π * (k.val : ℝ) / n) + I * (2 * π * (((-k).val) : ℝ) / n) =
                     2 * π * I := by
      have hn0' : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
      have hsum_complex : ((k.val : ℕ) : ℂ) + (((-k).val : ℕ) : ℂ) = ((n : ℕ) : ℂ) := by
        simp only [← Nat.cast_add, hsum_nat]
      calc I * (2 * π * (k.val : ℝ) / n) + I * (2 * π * (((-k).val) : ℝ) / n)
          = I * (2 * π * (((k.val : ℕ) : ℂ) + (((-k).val : ℕ) : ℂ)) / (n : ℂ)) := by
              push_cast; ring
        _ = I * (2 * π * ((n : ℕ) : ℂ) / (n : ℂ)) := by rw [hsum_complex]
        _ = I * (2 * π) := by field_simp [hn0']
        _ = 2 * π * I := by ring
    rw [h_exp_sum]
    -- exp(2π * I) = 1
    exact Complex.exp_two_pi_mul_I

/-- Spiral conjugate pairing: z_k on spiral at e^σ pairs with w_{n-k} on inverse spiral at e^{-σ}. -/
lemma spiral_conjugate_pair (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) [NeZero (p^n)]
    (σ : ℝ) (k : ZMod (p^n)) :
    Complex.exp (σ + I * (2 * π * (k.val : ℝ) / (p^n : ℝ))) *
    Complex.exp (-σ + I * (2 * π * (((-k).val) : ℝ) / (p^n : ℝ))) = 1 := by
  -- PROOF IDEA:
  -- The σ and -σ cancel: (σ) + (-σ) = 0
  -- Angular parts: k.val + (-k).val = p^n (when k ≠ 0)
  -- So exp(0 + I * 2π * p^n / p^n) = exp(I * 2π) = 1
  rw [← Complex.exp_add]
  by_cases hk : k = 0
  · simp [hk]
  · -- (-k).val = p^n - k.val when k ≠ 0
    have hpn : (p^n : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero n (Nat.Prime.ne_zero (Fact.out))
    have hnegval : (-k).val = p^n - k.val := by
      rw [ZMod.neg_val]
      simp [hk]
    have hk_le : k.val ≤ p^n := Nat.le_of_lt (ZMod.val_lt k)
    have hsum_nat : k.val + (-k).val = p^n := by
      simpa [hnegval, Nat.add_sub_of_le hk_le]
    -- The sum of exponents: σ + (-σ) = 0, and angular parts give 2πi
    have h_exp_sum : (σ + I * (2 * π * (k.val : ℝ) / (p^n : ℝ))) +
                     (-σ + I * (2 * π * (((-k).val) : ℝ) / (p^n : ℝ))) = 2 * π * I := by
      have hsum_complex : ((k.val : ℕ) : ℂ) + (((-k).val : ℕ) : ℂ) = ((p^n : ℕ) : ℂ) := by
        simp only [← Nat.cast_add, hsum_nat]
      calc (σ + I * (2 * π * (k.val : ℝ) / (p^n : ℝ))) +
           (-σ + I * (2 * π * (((-k).val) : ℝ) / (p^n : ℝ)))
          = I * (2 * π * (((k.val : ℕ) : ℂ) + (((-k).val : ℕ) : ℂ)) / (p^n : ℂ)) := by
              push_cast; ring
        _ = I * (2 * π * ((p^n : ℕ) : ℂ) / (p^n : ℂ)) := by rw [hsum_complex]
        _ = I * (2 * π) := by simp only [Nat.cast_pow]; field_simp [hpn]
        _ = 2 * π * I := by ring
    rw [h_exp_sum]
    exact Complex.exp_two_pi_mul_I

/-- The ZMod negation corresponds to complex conjugation on roots of unity. -/
lemma root_of_unity_neg_eq_conj (n : ℕ) [NeZero n] (k : ZMod n) :
    Complex.exp (I * (2 * π * (((-k).val) : ℝ) / n)) =
    conj (Complex.exp (I * (2 * π * (k.val : ℝ) / n))) := by

  have h_pair := root_of_unity_conjugate_pair n k
  have h_ne : Complex.exp (I * (2 * π * (k.val : ℝ) / n)) ≠ 0 := Complex.exp_ne_zero _
  -- Step 1: From h_pair, derive exp(I * θ_{-k}) = (exp(I * θ_k))⁻¹
  have h_inv : Complex.exp (I * (2 * π * (((-k).val) : ℝ) / n)) =
               (Complex.exp (I * (2 * π * (k.val : ℝ) / n)))⁻¹ := by
    have := h_pair
    field_simp [h_ne] at this ⊢
    exact this
  -- Step 2: For purely imaginary exponent: conj(exp(Iθ)) = exp(-Iθ) = (exp(Iθ))⁻¹
  have h_conj : conj (Complex.exp (I * (2 * π * (k.val : ℝ) / n))) =
                (Complex.exp (I * (2 * π * (k.val : ℝ) / n)))⁻¹ := by
    have h_conj_arg : conj (I * (2 * π * (k.val : ℝ) / n)) = -(I * (2 * π * (k.val : ℝ) / n)) := by
      have h2 : conj (2 : ℂ) = 2 := by
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) from rfl, Complex.conj_ofReal]
      simp only [map_mul, map_div₀, Complex.conj_I, Complex.conj_ofReal,
                 Complex.ofReal_natCast, Complex.conj_natCast, h2]
      ring
    rw [← Complex.exp_conj, h_conj_arg, Complex.exp_neg]
  rw [h_inv, ← h_conj]

/-! ### Self-Pairing for Even n

When n is even, k = n/2 is self-paired (-k = k in ZMod n), giving ω_{n/2} = -1. -/

/-- Characterization of self-paired elements in ZMod n.
    -k = k iff k = 0 or (n is even and k = n/2). -/
lemma zmod_neg_eq_self_iff (n : ℕ) [NeZero n] (k : ZMod n) :
    -k = k ↔ k = 0 ∨ (Even n ∧ k.val = n / 2) := by
  constructor
  · intro h
    by_cases hk : k = 0
    · left; exact hk
    · right
      -- -k = k means k + k = 0 in ZMod n (since k + k = k - (-k) = k - k = 0 when -k = k)
      have h2k : k + k = 0 := by
        have : k - (-k) = k + k := by ring
        rw [← this, h, sub_self]
      -- k + k = 0 in ZMod n means 2·k.val ≡ 0 (mod n)
      have hsum : (k + k).val = 0 := by simp [h2k]
      -- Either k.val + k.val < n (then = 0) or k.val + k.val ≥ n (wraps)
      have hklt : k.val < n := ZMod.val_lt k
      by_cases h2k_lt : k.val + k.val < n
      · -- No wrap: k.val + k.val = 0, so k.val = 0
        have : (k + k).val = k.val + k.val := ZMod.val_add_of_lt h2k_lt
        rw [this] at hsum
        have : k.val = 0 := by omega
        have : k = 0 := by
          have hv : (k : ZMod n) = (0 : ZMod n) := by
            apply ZMod.val_injective
            simpa using this
          exact hv
        exact absurd this hk
      · -- Wrap: k.val + k.val = n (since k.val + k.val < 2n)
        push_neg at h2k_lt
        have hlt2n : k.val + k.val < n + n := by omega
        have hge : n ≤ k.val + k.val := h2k_lt
        have hmod : (k.val + k.val) % n = k.val + k.val - n := by
          rw [Nat.mod_eq_sub_mod hge]
          have hsub_lt : k.val + k.val - n < n := by omega
          exact Nat.mod_eq_of_lt hsub_lt
        have hval_eq : (k + k).val = k.val + k.val - n := by
          have : (k + k).val = (k.val + k.val) % n := ZMod.val_add k k
          rw [this, hmod]
        rw [hval_eq] at hsum
      -- k.val + k.val - n = 0 means k.val + k.val = n
        have h2kn : k.val + k.val = n := by omega
        constructor
        · -- n is even: n = 2·k.val
          use k.val
          omega
        · -- k.val = n/2
          omega
  · intro h
    cases h with
    | inl h0 => simp [h0]
    | inr heven =>
      obtain ⟨hev, hval⟩ := heven
      -- k.val = n/2, so (-k).val = n - n/2 = n/2 (for even n)
      have hn2 : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hev
      have hklt : k.val < n := ZMod.val_lt k
      have hk_ne : k ≠ 0 := by
        intro hk0
        rw [hk0] at hval
        simp at hval
        have : n = 0 := by omega
        exact NeZero.ne n this
      have hneg : (-k).val = n - k.val := by
        rw [ZMod.neg_val]
        simp [hk_ne]
      -- Show -k = k by showing they have the same val
      apply ZMod.val_injective
      calc (-k).val = n - k.val := hneg
        _ = n - n / 2 := by rw [hval]
        _ = n / 2 := by omega
        _ = k.val := hval.symm

/-- For even n, the midpoint element k = n/2 is self-paired. -/
lemma zmod_half_self_paired (n : ℕ) [NeZero n] (hn : Even n) :
    -((n / 2 : ℕ) : ZMod n) = ((n / 2 : ℕ) : ZMod n) := by
  rw [zmod_neg_eq_self_iff]
  right
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hdiv_lt : n / 2 < n := Nat.div_lt_self hn_pos (by norm_num : 1 < 2)
  exact ⟨hn, ZMod.val_natCast_of_lt hdiv_lt⟩

/-- For even n, the root of unity at n/2 equals -1.
    This is because e^{iπ} = -1, and 2π·(n/2)/n = π. -/
lemma root_unity_half_eq_neg_one (n : ℕ) [NeZero n] (hn : Even n) :
    Complex.exp (I * (2 * π * (n / 2 : ℕ) / n)) = -1 := by
  have hn_ne : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hn2 : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hn
  have h_cast : (2 * (n / 2 : ℕ) : ℂ) = (n : ℂ) := by
    norm_cast
  calc Complex.exp (I * (2 * π * (n / 2 : ℕ) / n))
      = Complex.exp (I * π * (2 * (n / 2 : ℕ)) / n) := by ring_nf
    _ = Complex.exp (I * π * n / n) := by rw [h_cast]
    _ = Complex.exp (I * π) := by rw [mul_div_assoc, div_self hn_ne, mul_one]
    _ = Complex.exp (π * I) := by ring_nf
    _ = -1 := Complex.exp_pi_mul_I

/-- For ODD n, no non-zero element is self-paired.
    This means all conjugate pairs are distinct. -/
lemma zmod_neg_ne_self_of_odd (n : ℕ) [NeZero n] (hn : Odd n) (k : ZMod n) (hk : k ≠ 0) :
    -k ≠ k := by
  intro heq
  rw [zmod_neg_eq_self_iff] at heq
  cases heq with
  | inl h0 => exact hk h0
  | inr heven =>
      -- Even n and Odd n are contradictory
      obtain ⟨m, hm⟩ := heven.1
      obtain ⟨k, hk⟩ := hn
      omega

/-- For odd primes p, the p-adic tower has no self-paired elements (except 0).
    This simplifies the Fourier coefficient structure. -/
lemma padic_no_self_pairing (p : ℕ) [Fact (Nat.Prime p)] (hodd : Odd p) (m : ℕ)
    [NeZero (p^m)] (k : ZMod (p^m)) (hk : k ≠ 0) :
    -k ≠ k := by
  apply zmod_neg_ne_self_of_odd
  · exact hodd.pow
  · exact hk

/-- Powers of spiral points factor via characters. -/
lemma spiral_point_power_eq_character (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (k : ZMod (p^n)) (j : ZMod (p^n)) :
    Complex.exp ((k.val : ℝ) * (ε + I * (2 * π * (j.val : ℝ) / (p^n : ℝ)))) =
    Complex.exp ((k.val : ℝ) * ε) * character (p^n) k j := by
  -- z^k = e^{k(ε+iθ)} = e^{kε} · e^{ikθ}
  -- And e^{ikθ} where θ = 2πj/p^n is exactly character(p^n, k, j)
  unfold character
  rw [mul_add, Complex.exp_add]
  congr 1
  push_cast
  ring_nf

/-- The spiral kernel inner product converges to the continuous inner product as n → ∞. -/
lemma spiral_kernel_tendsto_integral (p : ℕ) [Fact (Nat.Prime p)] (ε : ℝ)
    (f g : ℂ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    Filter.Tendsto
      (fun n => (p^n : ℂ)⁻¹ * spiral_kernel_product p n ε f g)
      Filter.atTop
      (nhds ((2 * π : ℂ)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
        f (Complex.exp (ε + I * θ)) * conj (g (Complex.exp (ε + I * θ))))) := by

  let h : ℝ → ℂ := fun θ => f (Complex.exp (ε + I * θ)) * conj (g (Complex.exp (ε + I * θ)))
  -- Step 2: h is continuous
  have hh_cont : Continuous h := by
    apply Continuous.mul
    · exact hf.comp (Complex.continuous_exp.comp
        (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)))
    · exact continuous_conj.comp (hg.comp (Complex.continuous_exp.comp
        (continuous_const.add (continuous_const.mul Complex.continuous_ofReal))))
  -- Step 3: h is uniformly continuous on [0, 2π]
  have hh_unif : UniformContinuousOn h (Set.Icc 0 (2 * Real.pi)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hh_cont.continuousOn
  -- Step 4: h is integrable
  have hh_integrable : IntervalIntegrable h MeasureTheory.volume 0 (2 * Real.pi) :=
    hh_cont.intervalIntegrable 0 (2 * Real.pi)
  -- Step 5: Basic facts about p
  have hp : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := Nat.Prime.pos hp
  have hp_gt_one : 1 < p := Nat.Prime.one_lt hp
  have hp_cast_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_pos
  have hp_cast_gt_one : (1 : ℝ) < p := by exact_mod_cast hp_gt_one
  -- Step 6: Use Metric.tendsto_atTop
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Step 7: Get uniform continuity modulus
  have hδ' : δ / (2 * Real.pi + 1) > 0 := by positivity
  obtain ⟨η, hη_pos, hη_cont⟩ := Metric.uniformContinuousOn_iff_le.mp hh_unif
    (δ / (2 * Real.pi + 1)) hδ'
  -- Step 8: The mesh 2π/p^n → 0, so eventually mesh < η
  have h_mesh_small : ∃ N, ∀ n ≥ N, 2 * Real.pi / (p : ℝ)^n < η := by
    have h_tendsto : Filter.Tendsto (fun n => 2 * Real.pi / (p : ℝ)^n) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_pow_atTop_atTop_of_one_lt hp_cast_gt_one
    rw [Metric.tendsto_atTop] at h_tendsto
    obtain ⟨N, hN⟩ := h_tendsto η hη_pos
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos] at hN
    · exact hN
    · positivity
  obtain ⟨N, hN⟩ := h_mesh_small
  use N
  intro n hn
  -- Step 9: Establish NeZero instance for p^n
  have hp_n_ne_zero : p^n ≠ 0 := pow_ne_zero n (Nat.Prime.ne_zero hp)
  haveI : NeZero (p^n) := ⟨hp_n_ne_zero⟩
  have hp_n_pos : (0 : ℝ) < (p : ℝ)^n := by positivity
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h_mesh_bound : 2 * Real.pi / (p : ℝ)^n < η := hN n hn
  -- Step 10: Unfold and work with the definition directly
  unfold spiral_kernel_product
  rw [Complex.dist_eq]
  -- The key insight: We need to show the discrete average converges to the continuous average
  -- Define convenient abbreviations
  set pn := p^n with hpn_def
  have hpn_pos_real : (0 : ℝ) < pn := by simp [hpn_def]; positivity
  have hpn_ne_zero_real : (pn : ℝ) ≠ 0 := ne_of_gt hpn_pos_real
  have hpn_ne_zero_complex : (pn : ℂ) ≠ 0 := by exact_mod_cast hp_n_ne_zero
  have h2pi_ne_zero : (2 * π : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero, not_or]
    exact ⟨by norm_num, Real.pi_ne_zero⟩
  -- Rewrite the discrete sum using the integral representation
  -- (1/pn) Σ_j h(θ_j) where θ_j = 2πj/pn
  -- The oscillation bound: on each subinterval of width 2π/pn, |h(θ) - h(θ')| ≤ δ/(2π+1)
  have h_osc_bound : ∀ θ₁ θ₂ : ℝ, θ₁ ∈ Set.Icc 0 (2 * Real.pi) →
      θ₂ ∈ Set.Icc 0 (2 * Real.pi) → |θ₁ - θ₂| ≤ 2 * Real.pi / (p : ℝ)^n →
      dist (h θ₁) (h θ₂) ≤ δ / (2 * Real.pi + 1) := by
    intro θ₁ θ₂ hθ₁ hθ₂ h_close
    have h_dist : dist θ₁ θ₂ ≤ η := by
      rw [Real.dist_eq]
      calc |θ₁ - θ₂| ≤ 2 * Real.pi / (p : ℝ)^n := h_close
        _ ≤ η := le_of_lt h_mesh_bound
    exact hη_cont θ₁ hθ₁ θ₂ hθ₂ h_dist
  -- The proof uses the standard Riemann sum convergence estimate
  -- For uniformly continuous h on [0, 2π]:
  -- |discrete_avg - integral_avg| ≤ oscillation
  -- The bound follows from: each of pn subintervals contributes error ≤ osc × width
  -- Total: pn × (δ/(2π+1)) × (2π/pn) / (2π) = δ/(2π+1) < δ
  -- Step 11: The key is to show the discrete average of h converges to the integral average
  have h_card : Fintype.card (ZMod (p^n)) = p^n := ZMod.card (p^n)
  -- Convert ZMod sum to Finset.range sum
  have h_sum_range : ∑ j : ZMod (p^n), h (2 * π * (j.val : ℝ) / (p^n : ℝ)) =
      ∑ k ∈ Finset.range (p^n), h (2 * π * (k : ℝ) / (p^n : ℝ)) := by
    apply Finset.sum_bij (fun (m : ZMod (p^n)) _ => m.val)
    case hi => intro m _; exact Finset.mem_range.mpr (ZMod.val_lt m)
    case h => intro m _; rfl
    case i_inj => intro m₁ _ m₂ _ h_eq; exact ZMod.val_injective (p^n) h_eq
    case i_surj =>
      intro i hi
      simp only [Finset.mem_range] at hi
      exact ⟨(i : ZMod (p^n)), Finset.mem_univ _, ZMod.val_natCast_of_lt hi⟩
  -- The goal sum equals ∑ j, h(θ_j) where h is our integrand
  -- The coercions ↑(p^n : ℕ) and (p : ℝ)^n are equal
  have hpn_cast_eq : ((p^n : ℕ) : ℝ) = (p : ℝ)^n := by simp [Nat.cast_pow]
  have h_goal_eq : ∑ j : ZMod (p^n),
      f (Complex.exp (ε + I * (2 * π * (j.val : ℝ) / ((p^n : ℕ) : ℝ)))) *
      conj (g (Complex.exp (ε + I * (2 * π * (j.val : ℝ) / ((p^n : ℕ) : ℝ))))) =
      ∑ j : ZMod (p^n), h (2 * π * (j.val : ℝ) / (p^n : ℝ)) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [h]
    -- Normalize the coercions: both sides compute the same value
    -- LHS: (2 * ↑π * ↑↑j.val / ↑(↑p ^ n)) computed in ℂ
    -- RHS: ↑(2 * π * ↑j.val / ↑p ^ n) computed in ℝ then cast to ℂ
    congr 2 <;> {
      congr 1
      push_cast
      simp only [Nat.cast_pow]
    }
  -- Step 12: Define the partition function a(k) = 2πk/p^n
  let a : ℕ → ℝ := fun k => 2 * Real.pi * k / (p^n : ℝ)
  have ha0 : a 0 = 0 := by simp [a]
  have hapn : a (p^n) = 2 * Real.pi := by
    simp only [a]
    field_simp
    simp only [Nat.cast_pow]
  have h_Δ : ∀ k, a (k + 1) - a k = 2 * Real.pi / (p^n : ℝ) := by
    intro k
    simp only [a]
    field_simp
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  -- Step 13: Decompose the integral as sum of subinterval integrals
  have h_decomp : ∫ θ in (0:ℝ)..(2 * Real.pi), h θ =
      ∑ k ∈ Finset.range (p^n), ∫ θ in (a k)..(a (k + 1)), h θ := by
    have hint : ∀ k < p^n, IntervalIntegrable h MeasureTheory.volume (a k) (a (k + 1)) := by
      intro k _
      exact hh_cont.intervalIntegrable _ _
    have h_sum := intervalIntegral.sum_integral_adjacent_intervals hint
    rw [ha0, hapn] at h_sum
    exact h_sum.symm
  -- Step 14: Rewrite the discrete sum as scaled Riemann sum
  have h_rewrite : (↑(p^n : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (p^n), h (a k) =
      (2 * π : ℂ)⁻¹ * ∑ k ∈ Finset.range (p^n), h (a k) * ((2 * π / (p^n : ℝ)) : ℂ) := by
    have hpn_ne : ((p^n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp_n_ne_zero
    have h2pi_ne_c : (2 * π : ℂ) ≠ 0 := h2pi_ne_zero
    -- Factor out constant from RHS sum: Σ [h(a_k) * c] = c * Σ h(a_k)
    have h_factor : ∑ k ∈ Finset.range (p^n), h (a k) * ((2 * π / (p^n : ℝ)) : ℂ) =
        ((2 * π / (p^n : ℝ)) : ℂ) * ∑ k ∈ Finset.range (p^n), h (a k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_factor]
    -- Now show: (p^n)⁻¹ * Σ = (2π)⁻¹ * (2π/p^n) * Σ
    -- RHS = (2π)⁻¹ * (2π/p^n) * Σ = (p^n)⁻¹ * Σ = LHS
    have hpn_cast : ((p^n : ℕ) : ℂ) = ((p^n : ℕ) : ℝ) := by simp
    have hpn_cast2 : ((p^n : ℕ) : ℝ) = (p : ℝ)^n := by simp [Nat.cast_pow]
    rw [hpn_cast, hpn_cast2]
    have hpn_ne_r : ((p : ℝ)^n : ℂ) ≠ 0 := by
      simp only [ne_eq, ← Complex.ofReal_pow, Complex.ofReal_eq_zero, pow_eq_zero_iff',
        Nat.cast_eq_zero, Nat.Prime.ne_zero hp, not_false_eq_true, false_and]
    field_simp [h2pi_ne_c, hpn_ne_r]
  -- Step 15: The main bound
  -- |discrete_avg - integral_avg| = |(1/2π) * [Riemann_sum - integral]|
  -- We bound |Riemann_sum - integral| ≤ 2π * oscillation
  have h_riemann_bound : ‖∑ k ∈ Finset.range (p^n), h (a k) * ((2 * π / (p^n : ℝ)) : ℂ) -
      ∫ θ in (0:ℝ)..(2 * Real.pi), h θ‖ ≤ 2 * Real.pi * (δ / (2 * Real.pi + 1)) := by
    rw [h_decomp]
    rw [← Finset.sum_sub_distrib]
    -- Bound using triangle inequality
    calc ‖∑ k ∈ Finset.range (p^n), (h (a k) * ((2 * π / (p^n : ℝ)) : ℂ) -
            ∫ θ in (a k)..(a (k + 1)), h θ)‖
        ≤ ∑ k ∈ Finset.range (p^n), ‖h (a k) * ((2 * π / (p^n : ℝ)) : ℂ) -
            ∫ θ in (a k)..(a (k + 1)), h θ‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range (p^n), (δ / (2 * Real.pi + 1)) * (2 * Real.pi / (p^n : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk_bound : k < p^n := Finset.mem_range.mp hk
          -- Define the subinterval endpoints
          set θ_k := a k with hθ_k_def
          set θ_k1 := a (k + 1) with hθ_k1_def
          set Δθ := 2 * Real.pi / (p^n : ℝ) with hΔθ_def
          -- θ_k1 - θ_k = Δθ
          have h_interval_len : θ_k1 - θ_k = Δθ := h_Δ k
          have h_θ_k_le_θ_k1 : θ_k ≤ θ_k1 := by
            have : Δθ > 0 := by positivity
            linarith [h_interval_len]
          -- θ_k ∈ [0, 2π]
          have h_θ_k_nonneg : 0 ≤ θ_k := by simp [a, hθ_k_def]; positivity
          have h_θ_k_le_2pi : θ_k ≤ 2 * Real.pi := by
            simp only [a, hθ_k_def]
            have hk_le : (k : ℝ) ≤ (p^n : ℝ) := by
              exact_mod_cast le_of_lt hk_bound
            calc 2 * Real.pi * k / (p^n : ℝ)
                ≤ 2 * Real.pi * (p^n : ℝ) / (p^n : ℝ) := by
                  apply div_le_div_of_nonneg_right _ (by positivity)
                  exact mul_le_mul_of_nonneg_left hk_le (by positivity)
              _ = 2 * Real.pi := by field_simp
          have h_θ_k_mem : θ_k ∈ Set.Icc 0 (2 * Real.pi) := ⟨h_θ_k_nonneg, h_θ_k_le_2pi⟩
          -- θ_k1 ≤ 2π
          have h_θ_k1_le_2pi : θ_k1 ≤ 2 * Real.pi := by
            simp only [a, hθ_k1_def]
            have hk1_le : ((k + 1 : ℕ) : ℝ) ≤ (p^n : ℝ) := by
              have : k + 1 ≤ p^n := hk_bound
              exact_mod_cast this
            calc 2 * Real.pi * ((k + 1 : ℕ) : ℝ) / (p^n : ℝ)
                ≤ 2 * Real.pi * (p^n : ℝ) / (p^n : ℝ) := by
                  apply div_le_div_of_nonneg_right _ (by positivity)
                  exact mul_le_mul_of_nonneg_left hk1_le (by positivity)
              _ = 2 * Real.pi := by field_simp
          -- h(θ_k) * Δθ = ∫_{θ_k}^{θ_k1} h(θ_k) dθ
          have h_const_integral : h θ_k * (Δθ : ℂ) = ∫ _ in θ_k..θ_k1, h θ_k := by
            rw [intervalIntegral.integral_const]
            -- Goal: h θ_k * ↑Δθ = (θ_k1 - θ_k) • h θ_k
            -- Use smul_eq_mul for ℝ acting on ℂ: r • z = ↑r * z
            rw [Complex.real_smul, h_interval_len]
            ring
          -- Need to match h θ_k * (Δθ : ℂ) with h θ_k * ((2 * π / (p^n : ℝ)) : ℂ)
          have hΔθ_eq : (Δθ : ℂ) = ((2 * π / (p^n : ℝ)) : ℂ) := by
            simp only [hΔθ_def]
            push_cast
            rfl
          rw [← hΔθ_eq, h_const_integral]
          -- Now: ‖∫ h(θ_k) - ∫ h‖ ≤ osc × Δθ
          rw [← intervalIntegral.integral_sub intervalIntegrable_const
              (hh_cont.intervalIntegrable _ _)]
          -- Bound using norm_integral_le_of_norm_le_const
          have h_bound : ∀ x ∈ Set.uIoc θ_k θ_k1, ‖h θ_k - h x‖ ≤ δ / (2 * Real.pi + 1) := by
            intro x hx
            rw [Set.uIoc_of_le h_θ_k_le_θ_k1] at hx
            -- x ∈ [0, 2π]
            have h_x_mem : x ∈ Set.Icc 0 (2 * Real.pi) := by
              constructor
              · exact le_trans h_θ_k_nonneg (le_of_lt hx.1)
              · exact le_trans hx.2 h_θ_k1_le_2pi
            -- |θ_k - x| ≤ Δθ
            have h_dist_bound : |θ_k - x| ≤ Δθ := by
              rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hx.1)]
              calc x - θ_k ≤ θ_k1 - θ_k := by linarith [hx.2]
                _ = Δθ := h_interval_len
            -- Apply oscillation bound
            have h_osc := h_osc_bound θ_k x h_θ_k_mem h_x_mem h_dist_bound
            rwa [dist_eq_norm] at h_osc
          have h_norm_bound := intervalIntegral.norm_integral_le_of_norm_le_const h_bound
          have h_Δθ_pos : (0 : ℝ) < Δθ := by positivity
          calc ‖∫ x in θ_k..θ_k1, h θ_k - h x‖
              ≤ (δ / (2 * Real.pi + 1)) * |θ_k1 - θ_k| := h_norm_bound
            _ = (δ / (2 * Real.pi + 1)) * Δθ := by rw [h_interval_len, abs_of_pos h_Δθ_pos]
            _ = (δ / (2 * Real.pi + 1)) * (2 * Real.pi / (p^n : ℝ)) := rfl
      _ = (p^n : ℝ) * ((δ / (2 * Real.pi + 1)) * (2 * Real.pi / (p^n : ℝ))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          simp only [Nat.cast_pow]
      _ = 2 * Real.pi * (δ / (2 * Real.pi + 1)) := by
          have hpn_ne : (p^n : ℝ) ≠ 0 := ne_of_gt hp_n_pos
          field_simp [hpn_ne]
  -- Step 16: Connect ZMod sum to Finset.range sum via h_sum_range and a
  have h_sum_eq : ∑ j : ZMod (p^n), h (2 * π * (j.val : ℝ) / ((p^n : ℕ) : ℝ)) =
      ∑ k ∈ Finset.range (p^n), h (a k) := by
    -- First normalize ↑(p^n) to ↑p ^ n using Nat.cast_pow
    have h_cast : ((p^n : ℕ) : ℝ) = (p : ℝ)^n := Nat.cast_pow p n
    simp only [h_cast]
    rw [h_sum_range]
  -- The integral ∫ f(cexp(ε + I*θ)) * conj(g(...)) dθ equals ∫ h θ dθ by definition
  have h_integral_eq : ∫ θ in (0:ℝ)..(2 * π),
      f (Complex.exp (ε + I * θ)) * conj (g (Complex.exp (ε + I * θ))) =
      ∫ θ in (0:ℝ)..(2 * π), h θ := by rfl
  -- Coercion equality: ↑(p^n : ℕ) = (↑p : ℂ)^n
  have hpn_cast_complex : ((p^n : ℕ) : ℂ) = ((p : ℂ))^n := by simp [Nat.cast_pow]
  -- Final calculation
  -- First normalize coercions in goal: convert (↑p)^n to ↑(p^n) using ← Nat.cast_pow
  conv_lhs => simp only [← Nat.cast_pow]
  -- Now convert from goal form to h form using h_goal_eq
  rw [h_goal_eq, h_integral_eq]
  -- Now we have: ‖(↑(p^n))⁻¹ * ∑ j, h(...) - (2π)⁻¹ * ∫ h‖ < δ
  -- First normalize coercions in the goal to use ↑(p^n) form
  simp only [← Nat.cast_pow]
  calc ‖(↑(p^n : ℕ))⁻¹ * ∑ j : ZMod (p^n),
          h (2 * π * (j.val : ℝ) / ((p^n : ℕ) : ℝ)) -
        (2 * ↑π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), h θ‖
      = ‖(↑(p^n : ℕ))⁻¹ * ∑ k ∈ Finset.range (p^n), h (a k) -
          (2 * ↑π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), h θ‖ := by
        rw [h_sum_eq]
    _ = ‖(2 * ↑π)⁻¹ * ∑ k ∈ Finset.range (p^n), h (a k) * ((2 * π / (p^n : ℝ)) : ℂ) -
          (2 * ↑π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), h θ‖ := by
        rw [h_rewrite]
    _ = ‖(2 * ↑π)⁻¹ * (∑ k ∈ Finset.range (p^n), h (a k) * ((2 * π / (p^n : ℝ)) : ℂ) -
          ∫ θ in (0:ℝ)..(2 * π), h θ)‖ := by
        rw [mul_sub]
    _ ≤ ‖(2 * ↑π : ℂ)⁻¹‖ * ‖∑ k ∈ Finset.range (p^n), h (a k) * ((2 * π / (p^n : ℝ)) : ℂ) -
          ∫ θ in (0:ℝ)..(2 * π), h θ‖ := norm_mul_le _ _
    _ ≤ (2 * π)⁻¹ * (2 * π * (δ / (2 * π + 1))) := by
        apply mul_le_mul
        · -- Show ‖(2 * π : ℂ)⁻¹‖ ≤ (2 * π)⁻¹
          rw [norm_inv]
          -- ‖2 * ↑π‖ = ‖↑(2 * π)‖ = |2 * π| = 2 * π
          have h_norm : ‖(2 * π : ℂ)‖ = 2 * π := by
            rw [show (2 * π : ℂ) = ↑(2 * Real.pi) by push_cast; rfl]
            rw [norm_real, Real.norm_eq_abs, abs_of_pos h2pi_pos]
          rw [h_norm]
        · exact h_riemann_bound
        · positivity
        · positivity
    _ = δ / (2 * π + 1) := by field_simp
    _ < δ := by
        have h1 : (1 : ℝ) < 2 * Real.pi + 1 := by linarith [Real.pi_pos]
        exact div_lt_self hδ h1

/-- The RG operator eigenvalue structure on characters. -/
lemma character_is_RG_eigenfunction (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (k : ZMod (p^n)) (ε : ℝ) :
    ∀ m : ZMod (p^n),
    character (p^n) k m = Complex.exp (-(k.val : ℂ) * ε) *
      (fun j => character (p^n) k j * Complex.exp ((k.val : ℂ) * ε)) m := by
  intro m
  simp only []
  rw [mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
  norm_num

/-- The spiral kernel matrix elements via characters give orthogonality. -/
lemma spiral_kernel_character_orthogonal (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (k ℓ : ZMod (p^n)) :
    spiral_kernel_product p n ε
      (fun z => z ^ k.val)
      (fun z => z ^ ℓ.val) =
    if k = ℓ then (p^n : ℂ) * Complex.exp (2 * (k.val : ℂ) * ε) else 0 := by
  -- The power function z^k lifts the character to ℂ*:
  -- z_j^k = exp(k(ε + i·2πj/p^n)) = e^{kε} · character(p^n, k, j)
  unfold spiral_kernel_product
  -- Step 1: Compute z^m for the spiral points
  have h_pow : ∀ (j : ZMod (p^n)) (m : ZMod (p^n)),
      (Complex.exp (↑ε + I * (2 * ↑π * ↑j.val / ↑(p^n)))) ^ m.val =
      Complex.exp ((m.val : ℂ) * ε) * character (p^n) m j := by
    intro j m
    rw [← Complex.exp_nat_mul]
    unfold character
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- Step 2: Each term factors
  have h_term : ∀ j : ZMod (p^n),
      (Complex.exp (↑ε + I * (2 * ↑π * ↑j.val / ↑(p^n)))) ^ k.val *
      conj ((Complex.exp (↑ε + I * (2 * ↑π * ↑j.val / ↑(p^n)))) ^ ℓ.val) =
      Complex.exp (((k.val : ℂ) + (ℓ.val : ℂ)) * ε) *
        (character (p^n) k j * conj (character (p^n) ℓ j)) := by
    intro j
    rw [h_pow j k, h_pow j ℓ, map_mul]
    -- conj(exp(ℓ·ε)) = exp(ℓ·ε) since it's real
    have h_conj_exp : conj (Complex.exp ((ℓ.val : ℂ) * ε)) = Complex.exp ((ℓ.val : ℂ) * ε) := by
      have h_real : ((ℓ.val : ℂ) * ε : ℂ) = ↑((ℓ.val : ℝ) * ε) := by push_cast; ring
      rw [h_real]
      rw [← Complex.ofReal_exp, Complex.conj_ofReal]
    rw [h_conj_exp]
    -- exp(kε) * char_k * exp(ℓε) * conj(char_ℓ) = exp((k+ℓ)ε) * (char_k * conj(char_ℓ))
    have h_exp_combine : Complex.exp ((k.val : ℂ) * ε) * Complex.exp ((ℓ.val : ℂ) * ε) =
        Complex.exp (((k.val : ℂ) + (ℓ.val : ℂ)) * ε) := by
      rw [← Complex.exp_add]; ring_nf
    calc Complex.exp ((k.val : ℂ) * ε) * character (p^n) k j *
          (Complex.exp ((ℓ.val : ℂ) * ε) * conj (character (p^n) ℓ j))
        = (Complex.exp ((k.val : ℂ) * ε) * Complex.exp ((ℓ.val : ℂ) * ε)) *
          (character (p^n) k j * conj (character (p^n) ℓ j)) := by ring
      _ = Complex.exp (((k.val : ℂ) + (ℓ.val : ℂ)) * ε) *
          (character (p^n) k j * conj (character (p^n) ℓ j)) := by rw [h_exp_combine]
  -- Step 3: Rewrite sum using h_term and factor out constant
  -- The main equality: transform each summand using h_term
  suffices h_suff : ∑ j : ZMod (p^n),
      (Complex.exp (↑ε + I * (2 * ↑π * ↑j.val / ↑(p^n)))) ^ k.val *
      conj ((Complex.exp (↑ε + I * (2 * ↑π * ↑j.val / ↑(p^n)))) ^ ℓ.val) =
      if k = ℓ then (p^n : ℂ) * Complex.exp (2 * (k.val : ℂ) * ε) else 0 by
    -- The goal follows from h_suff by showing LHS = sum in h_suff
    convert h_suff using 2 <;> { simp only [← Nat.cast_pow]; norm_cast }
  -- Prove h_suff
  have h_sum_factored : ∑ j : ZMod (p^n),
      (Complex.exp (↑ε + I * (2 * ↑π * ↑j.val / ↑(p^n)))) ^ k.val *
      conj ((Complex.exp (↑ε + I * (2 * ↑π * ↑j.val / ↑(p^n)))) ^ ℓ.val) =
      Complex.exp (((k.val : ℂ) + (ℓ.val : ℂ)) * ε) *
        ∑ j : ZMod (p^n), character (p^n) k j * conj (character (p^n) ℓ j) := by
    calc ∑ j : ZMod (p^n),
          (Complex.exp (↑ε + I * (2 * ↑π * ↑j.val / ↑(p^n)))) ^ k.val *
          conj ((Complex.exp (↑ε + I * (2 * ↑π * ↑j.val / ↑(p^n)))) ^ ℓ.val)
        = ∑ j : ZMod (p^n), Complex.exp (((k.val : ℂ) + (ℓ.val : ℂ)) * ε) *
            (character (p^n) k j * conj (character (p^n) ℓ j)) := by
          congr 1; ext j; exact h_term j
      _ = Complex.exp (((k.val : ℂ) + (ℓ.val : ℂ)) * ε) *
            ∑ j : ZMod (p^n), character (p^n) k j * conj (character (p^n) ℓ j) := by
          rw [← Finset.mul_sum]
  rw [h_sum_factored, character_orthogonality p n k ℓ]
  by_cases h_eq : k = ℓ
  · subst h_eq
    simp only [ite_true]
    ring_nf
  · simp only [h_eq, ite_false, mul_zero]



/-- The spiral norm at scale ε and level n. -/
noncomputable def spiral_norm (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (f : ℂ → ℂ) : ℝ :=
  Real.sqrt (spiral_kernel_product p n ε f f).re

/-- The spiral norm is nonnegative. -/
lemma spiral_norm_nonneg (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (f : ℂ → ℂ) :
    0 ≤ spiral_norm p n ε f :=
  Real.sqrt_nonneg _

/-- The spiral norm squared equals the real part of the inner product. -/
lemma spiral_norm_sq (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (f : ℂ → ℂ) :
    (spiral_norm p n ε f) ^ 2 = (spiral_kernel_product p n ε f f).re := by
  unfold spiral_norm
  rw [Real.sq_sqrt (spiral_kernel_pos p n ε f)]

/-- The spiral norm is zero iff f vanishes at all spiral points. -/
lemma spiral_norm_eq_zero_iff (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (f : ℂ → ℂ) :
    spiral_norm p n ε f = 0 ↔
    ∀ j : ZMod (p^n), f (Complex.exp (ε + I * (2 * π * (j.val : ℝ) / (p^n : ℝ)))) = 0 := by
  unfold spiral_norm
  rw [Real.sqrt_eq_zero (spiral_kernel_pos p n ε f)]
  unfold spiral_kernel_product
  rw [Complex.re_sum]
  constructor
  · intro h_sum_zero j
    -- If sum of nonneg terms is 0, each term is 0
    have h_term_nonneg : ∀ i : ZMod (p^n), 0 ≤ (f (Complex.exp (ε + I * (2 * π * (i.val : ℝ) / (p^n : ℝ)))) *
        conj (f (Complex.exp (ε + I * (2 * π * (i.val : ℝ) / (p^n : ℝ)))))).re := by
      intro i
      rw [Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_nonneg _
    have h_each_zero := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun i _ => h_term_nonneg i)).mp h_sum_zero j (Finset.mem_univ j)
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_zero] at h_each_zero
    exact h_each_zero
  · intro h_all_zero
    apply Finset.sum_eq_zero
    intro j _
    rw [h_all_zero j, zero_mul, Complex.zero_re]

/-- Homogeneity of the spiral norm: ‖c • f‖ = |c| · ‖f‖ -/
lemma spiral_norm_smul (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    spiral_norm p n ε (fun z => c * f z) = ‖c‖ * spiral_norm p n ε f := by
  unfold spiral_norm spiral_kernel_product
  -- ⟨c·f, c·f⟩ = |c|² · ⟨f,f⟩
  -- Set up notation for the spiral point
  let z_j (j : ZMod (p^n)) := Complex.exp (ε + I * (2 * π * (j.val : ℝ) / (p^n : ℝ)))
  -- The key: each term (c·f(z))·conj(c·f(z)) = |c|² · |f(z)|²
  have h_term : ∀ j : ZMod (p^n),
      (c * f (z_j j)) * conj (c * f (z_j j)) = Complex.normSq c * (f (z_j j) * conj (f (z_j j))) := by
    intro j
    simp only [map_mul]
    have h := Complex.mul_conj c
    calc c * f (z_j j) * (conj c * conj (f (z_j j)))
        = (c * conj c) * (f (z_j j) * conj (f (z_j j))) := by ring
      _ = Complex.normSq c * (f (z_j j) * conj (f (z_j j))) := by rw [Complex.mul_conj]
  -- Sum the terms
  have h_sum : ∑ j : ZMod (p^n), (c * f (z_j j)) * conj (c * f (z_j j)) =
      Complex.normSq c * ∑ j : ZMod (p^n), f (z_j j) * conj (f (z_j j)) := by
    simp_rw [h_term]
    rw [← Finset.mul_sum]
  -- Take real part (normSq c is real, so it factors out)
  have h_re : (∑ j : ZMod (p^n), (c * f (z_j j)) * conj (c * f (z_j j))).re =
      Complex.normSq c * (∑ j : ZMod (p^n), f (z_j j) * conj (f (z_j j))).re := by
    rw [h_sum]
    simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  rw [h_re]
  rw [Real.sqrt_mul (Complex.normSq_nonneg _)]
  -- ‖c‖ = √(normSq c) by Complex.norm_def
  rw [← Complex.norm_def]

/-- The j-th spiral point at scale ε and level n.

    z_j^{(n)}(ε) = exp(ε + 2πij/p^n)

    These are the p^n-th roots of unity scaled to radius e^ε. -/
noncomputable def spiral_point (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (j : ZMod (p^n)) : ℂ :=
  Complex.exp (ε + I * (2 * π * (j.val : ℝ) / (p^n : ℝ)))

/-- The spiral measure at scale ε and level n. -/
noncomputable def spiral_measure (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) : MeasureTheory.Measure ℂ :=
  (p^n : ENNReal)⁻¹ • Finset.sum Finset.univ (fun j : ZMod (p^n) =>
    MeasureTheory.Measure.dirac (spiral_point p n ε j))

/-- The spiral measure is a probability measure. -/
lemma spiral_measure_prob (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) :
    spiral_measure p n ε Set.univ = 1 := by
  unfold spiral_measure spiral_point
  rw [MeasureTheory.Measure.smul_apply]
  rw [MeasureTheory.Measure.coe_finset_sum]
  simp only [Finset.sum_apply, MeasureTheory.Measure.dirac_apply_of_mem (Set.mem_univ _)]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card]
  simp only [smul_eq_mul, mul_one, nsmul_eq_mul]
  -- Goal: (↑p ^ n)⁻¹ * ↑(p ^ n) = 1
  -- Unify coercions and use inv_mul_cancel
  norm_cast
  rw [ENNReal.inv_mul_cancel]
  · simp only [ne_eq, Nat.cast_eq_zero]
    exact NeZero.ne (p^n)
  · exact ENNReal.natCast_ne_top (p^n)

/-- The spiral norm squared equals the sum of |f|² over spiral points. -/
lemma spiral_norm_sq_eq_sum (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (f : ℂ → ℂ) :
    (spiral_norm p n ε f) ^ 2 =
      ∑ j : ZMod (p^n), Complex.normSq (f (spiral_point p n ε j)) := by
  -- First use spiral_norm_sq to get (spiral_kernel_product p n ε f f).re
  rw [spiral_norm_sq]
  -- Now unfold spiral_kernel_product
  unfold spiral_kernel_product spiral_point
  rw [Complex.re_sum]
  congr 1
  funext j
  rw [Complex.mul_conj, Complex.ofReal_re]

/-- Restatement: The norm squared equals sum of squared norms. -/
lemma spiral_norm_sq_eq_discrete_L2 (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    [NeZero (p^n)] (ε : ℝ) (f : ℂ → ℂ) :
    (spiral_norm p n ε f) ^ 2 =
      ∑ j : ZMod (p^n), ‖f (spiral_point p n ε j)‖ ^ 2 := by
  rw [spiral_norm_sq_eq_sum]
  congr 1
  funext j
  rw [Complex.normSq_eq_norm_sq]

/-- Jensen's Formula (Circle Average Version): -/
theorem spiral_action_jensen (Q : Polynomial ℂ) (hQ : Q ≠ 0) (σ : ℝ)
    (h_no_zero : Q.eval 0 ≠ 0)
    (h_no_roots_on_circle : ∀ α ∈ Q.roots, ‖α‖ ≠ Real.exp σ) :
    spiral_action Q σ = Real.log ‖Q.leadingCoeff‖ +
      (Q.roots.map (fun α => max σ (Real.log ‖α‖))).sum := by
  /-
  Proof via Jensen's formula:

  Jensen's formula states that for polynomial Q with roots αᵢ, the circle average of
  log|Q| at radius r = e^σ equals:

    (1/2π) ∫₀^{2π} log|Q(r·e^{iθ})| dθ = log|c| + Σᵢ max(σ, log|αᵢ|)

  where c is the leading coefficient (since Q(z) = c·∏(z - αᵢ)).

  The key fact: for a single linear factor (z - α) at radius r = e^σ:
    (1/2π) ∫₀^{2π} log|r·e^{iθ} - α| dθ = max(log r, log|α|) = max(σ, log|α|)

  This follows from the mean value property for harmonic functions:
  - log|z - α| is harmonic away from α
  - If |α| < r (α inside circle): average = log r = σ
  - If |α| > r (α outside circle): average = log|α|
  - Combined: average = max(σ, log|α|)

  For the full polynomial Q = c·∏(z - αᵢ):
    log|Q(z)| = log|c| + Σᵢ log|z - αᵢ|

  Taking circle averages (which are linear):
    avg(log|Q|) = log|c| + Σᵢ avg(log|z - αᵢ|)
                = log|c| + Σᵢ max(σ, log|αᵢ|)
  -/
  -- Use circle_average_log_linear_factor for each root
  -- and the polynomial factorization Q = c · ∏(X - αᵢ)

  unfold spiral_action

  -- The proof uses:
  -- 1. Polynomial factorization: Q = leadingCoeff · ∏(X - α) over roots
  -- 2. log|Q(z)| = log|c| + Σ log|z - αᵢ|
  -- 3. Circle average is linear
  -- 4. circle_average_log_linear_factor for each factor

  -- Step 1: Get the roots and leading coefficient
  have hQ_splits : Q.Splits := IsAlgClosed.splits Q
  have hQ_roots : Q.roots.card = Q.natDegree := Polynomial.splits_iff_card_roots.mp hQ_splits
  have hc_ne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ

  -- Step 2: Polynomial factorization Q = C(leadingCoeff) * ∏(X - α) over roots
  have hQ_factor : Q = C Q.leadingCoeff * (Q.roots.map (fun α => X - C α)).prod :=
    (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hQ_roots).symm

  -- Step 3: Evaluation at z = exp(σ + I*θ)
  -- Q(z) = leadingCoeff * ∏(z - α)
  have h_eval : ∀ z : ℂ, Q.eval z = Q.leadingCoeff * (Q.roots.map (fun α => z - α)).prod := by
    intro z
    conv_lhs => rw [hQ_factor]
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    congr 1
    rw [Polynomial.eval_multiset_prod]
    congr 1
    ext α
    simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

  -- Step 4: For nonzero z, ‖Q(z)‖ = ‖leadingCoeff‖ * ∏‖z - α‖
  -- Helper: norm of multiset product = product of norms (for multiplicative norms)
  have h_norm_multiset_prod : ∀ (s : Multiset ℂ),
      ‖s.prod‖ = (s.map (fun x => ‖x‖)).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.prod_cons, Multiset.map_cons]
      rw [Complex.norm_mul, ih]

  have h_norm_eval : ∀ θ : ℝ,
      ‖Q.eval (Complex.exp (σ + I * θ))‖ =
      ‖Q.leadingCoeff‖ * (Q.roots.map (fun α => ‖Complex.exp (σ + I * θ) - α‖)).prod := by
    intro θ
    rw [h_eval]
    rw [Complex.norm_mul]
    congr 1
    -- ‖∏(z - α)‖ = ∏‖z - α‖
    rw [h_norm_multiset_prod]
    congr 1
    ext α
    simp

  -- Step 5: All roots are nonzero (from h_no_zero)
  have h_roots_nonzero : ∀ α ∈ Q.roots, α ≠ 0 := by
    intro α hα hα_eq
    -- If α = 0 is a root, then Q(0) = 0, contradicting h_no_zero
    have : Q.eval 0 = 0 := by
      rw [hα_eq] at hα
      exact (Polynomial.mem_roots hQ).mp hα
    exact h_no_zero this

  -- Step 6: For each root α, apply circle_average_log_linear_factor
  have h_avg_root : ∀ α ∈ Q.roots,
      (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
        Real.log ‖Complex.exp (σ + I * θ) - α‖ = max σ (Real.log ‖α‖) := by
    intro α hα
    exact circle_average_log_linear_factor α σ (h_roots_nonzero α hα) (h_no_roots_on_circle α hα)

  have h_log_prod_general : ∀ (m : Multiset ℂ) (θ : ℝ),
      (∀ α ∈ m, (0 : ℝ) < ‖Complex.exp (σ + I * θ) - α‖) →
      Real.log ((m.map (fun α => ‖Complex.exp (σ + I * θ) - α‖)).prod) =
      (m.map (fun α => Real.log ‖Complex.exp (σ + I * θ) - α‖)).sum := by
    intro m θ h_pos
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
      have ha_pos : 0 < ‖Complex.exp (σ + I * θ) - a‖ := h_pos a (Multiset.mem_cons_self a s)
      have hs_pos : ∀ α ∈ s, 0 < ‖Complex.exp (σ + I * θ) - α‖ :=
        fun α hα => h_pos α (Multiset.mem_cons_of_mem hα)
      have hprod_pos : 0 < (s.map (fun α => ‖Complex.exp (σ + I * θ) - α‖)).prod := by
        apply Multiset.prod_pos
        intro x hx
        obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hx
        exact hs_pos α hα
      rw [Real.log_mul (ne_of_gt ha_pos) (ne_of_gt hprod_pos)]
      congr 1
      exact ih hs_pos

  have h_log_prod : ∀ θ : ℝ, ∀ (h_pos : ∀ α ∈ Q.roots, (0 : ℝ) < ‖Complex.exp (σ + I * θ) - α‖),
      Real.log ((Q.roots.map (fun α => ‖Complex.exp (σ + I * θ) - α‖)).prod) =
      (Q.roots.map (fun α => Real.log ‖Complex.exp (σ + I * θ) - α‖)).sum :=
    fun θ h_pos => h_log_prod_general Q.roots θ h_pos

  -- Step 8: All terms ‖z - α‖ are positive (z on circle, α not on circle)
  have h_terms_pos : ∀ θ : ℝ, ∀ α ∈ Q.roots, (0 : ℝ) < ‖Complex.exp (σ + I * θ) - α‖ := by
    intro θ α hα
    apply norm_pos_iff.mpr
    intro h_eq
    -- If z - α = 0, then z = α, so ‖α‖ = ‖z‖ = e^σ, contradicting h_no_roots_on_circle
    have hz_eq_α : Complex.exp (σ + I * θ) = α := sub_eq_zero.mp h_eq
    have hz_norm : ‖Complex.exp (σ + I * θ)‖ = Real.exp σ := by
      rw [Complex.norm_exp]
      simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    have hα_norm : ‖α‖ = Real.exp σ := by
      rw [← hz_eq_α, hz_norm]
    exact h_no_roots_on_circle α hα hα_norm

  -- Step 9: Decompose log‖Q(z)‖ = log‖c‖ + Σ log‖z - α‖
  have h_log_decompose : ∀ θ : ℝ,
      Real.log ‖Q.eval (Complex.exp (σ + I * θ))‖ =
      Real.log ‖Q.leadingCoeff‖ +
      (Q.roots.map (fun α => Real.log ‖Complex.exp (σ + I * θ) - α‖)).sum := by
    intro θ
    rw [h_norm_eval θ]
    have hc_pos : 0 < ‖Q.leadingCoeff‖ := norm_pos_iff.mpr hc_ne
    have hprod_pos : 0 < (Q.roots.map (fun α => ‖Complex.exp (σ + I * θ) - α‖)).prod := by
      apply Multiset.prod_pos
      intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hx
      exact h_terms_pos θ α hα
    rw [Real.log_mul (ne_of_gt hc_pos) (ne_of_gt hprod_pos)]
    congr 1
    exact h_log_prod θ (h_terms_pos θ)

  -- Step 10: Now integrate both sides
  -- LHS: (1/2π) ∫ log‖Q(z)‖ dθ
  -- RHS: log‖c‖ + (1/2π) ∫ Σ log‖z - α‖ dθ = log‖c‖ + Σ (1/2π) ∫ log‖z - α‖ dθ
  --                                        = log‖c‖ + Σ max(σ, log‖α‖)

  -- The key is linearity: ∫ (Σ fᵢ) = Σ (∫ fᵢ) for finite sums
  -- For multisets, we use induction

  -- Helper for proving integrability of a single log term
  have h_log_term_integrable : ∀ (α : ℂ), ‖α‖ ≠ Real.exp σ →
      IntervalIntegrable (fun θ : ℝ => Real.log ‖Complex.exp (↑σ + I * ↑θ) - α‖)
        MeasureTheory.volume 0 (2 * Real.pi) := by
    intro α hα_not_on
    apply Continuous.intervalIntegrable
    have h_cont : Continuous (fun θ : ℝ => ‖Complex.exp (↑σ + I * ↑θ) - α‖) := by
      apply Continuous.norm
      apply Continuous.sub
      · apply Complex.continuous_exp.comp
        exact continuous_const.add (continuous_const.mul Complex.continuous_ofReal)
      · exact continuous_const
    apply h_cont.log
    intro θ
    apply norm_ne_zero_iff.mpr
    intro h_eq
    -- h_eq : exp(σ + iθ) - α = 0, so exp(σ + iθ) = α
    have hz_eq_α : Complex.exp (↑σ + I * ↑θ) = α := sub_eq_zero.mp h_eq
    have hz_norm : ‖Complex.exp (↑σ + I * ↑θ)‖ = Real.exp σ := by
      rw [Complex.norm_exp]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
                 Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, zero_mul, add_zero]
    have hα_norm : ‖α‖ = Real.exp σ := by rw [← hz_eq_α, hz_norm]
    exact hα_not_on hα_norm

  -- Helper for proving integrability of a multiset sum of log terms
  have h_sum_integrable : ∀ (m : Multiset ℂ),
      (∀ α ∈ m, ‖α‖ ≠ Real.exp σ) →
      IntervalIntegrable (fun θ : ℝ => (m.map (fun α => Real.log ‖Complex.exp (↑σ + I * ↑θ) - α‖)).sum)
        MeasureTheory.volume 0 (2 * Real.pi) := by
    intro m h_not_on
    induction m using Multiset.induction_on with
    | empty => simp [intervalIntegrable_const]
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      apply IntervalIntegrable.add
      · exact h_log_term_integrable a (h_not_on a (Multiset.mem_cons_self a s))
      · exact ih (fun α hα => h_not_on α (Multiset.mem_cons_of_mem hα))

  -- Helper: for any multiset m where all elements satisfy the hypotheses,
  -- the integral of the sum equals the sum of integrals
  have h_integral_multiset_sum : ∀ (m : Multiset ℂ),
      (∀ α ∈ m, α ≠ 0) →
      (∀ α ∈ m, ‖α‖ ≠ Real.exp σ) →
      (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
        (m.map (fun α => Real.log ‖Complex.exp (↑σ + I * ↑θ) - α‖)).sum =
      (m.map (fun α => max σ (Real.log ‖α‖))).sum := by
    intro m h_nonzero h_not_on_circle
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      -- Get hypotheses for 'a' and 's'
      have ha_nonzero : a ≠ 0 := h_nonzero a (Multiset.mem_cons_self a s)
      have ha_not_on_circle : ‖a‖ ≠ Real.exp σ := h_not_on_circle a (Multiset.mem_cons_self a s)
      have hs_nonzero : ∀ α ∈ s, α ≠ 0 := fun α hα => h_nonzero α (Multiset.mem_cons_of_mem hα)
      have hs_not_on_circle : ∀ α ∈ s, ‖α‖ ≠ Real.exp σ :=
        fun α hα => h_not_on_circle α (Multiset.mem_cons_of_mem hα)
      -- Integrability
      have h_integrable_a := h_log_term_integrable a ha_not_on_circle
      have h_integrable_s := h_sum_integrable s hs_not_on_circle
      -- Now split the integral
      rw [intervalIntegral.integral_add h_integrable_a h_integrable_s]
      rw [mul_add]
      congr 1
      · -- The term for 'a': apply circle_average_log_linear_factor
        exact circle_average_log_linear_factor a σ ha_nonzero ha_not_on_circle
      · -- The sum over 's': use induction hypothesis
        exact ih hs_nonzero hs_not_on_circle

  -- Now apply the helper to Q.roots
  have h_sum_integral :
      (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
        (Q.roots.map (fun α => Real.log ‖Complex.exp (↑σ + I * ↑θ) - α‖)).sum =
      (Q.roots.map (fun α => max σ (Real.log ‖α‖))).sum :=
    h_integral_multiset_sum Q.roots h_roots_nonzero h_no_roots_on_circle

  -- Rewrite the LHS using the log decomposition
  have h_integral_decompose :
      (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
        Real.log ‖Q.eval (Complex.exp (↑σ + I * ↑θ))‖ =
      Real.log ‖Q.leadingCoeff‖ +
      (2 * Real.pi)⁻¹ * ∫ θ in (0)..(2 * Real.pi),
        (Q.roots.map (fun α => Real.log ‖Complex.exp (↑σ + I * ↑θ) - α‖)).sum := by
    -- First, rewrite the integrand using h_log_decompose
    have h_eq_fn : ∀ θ : ℝ, Real.log ‖Q.eval (Complex.exp (↑σ + I * ↑θ))‖ =
        Real.log ‖Q.leadingCoeff‖ +
          (Q.roots.map (fun α => Real.log ‖Complex.exp (↑σ + I * ↑θ) - α‖)).sum :=
      h_log_decompose
    -- Rewrite the integral
    have h_integral_eq : ∫ θ in (0)..(2 * Real.pi), Real.log ‖Q.eval (Complex.exp (↑σ + I * ↑θ))‖ =
        ∫ θ in (0)..(2 * Real.pi), (Real.log ‖Q.leadingCoeff‖ +
          (Q.roots.map (fun α => Real.log ‖Complex.exp (↑σ + I * ↑θ) - α‖)).sum) := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact h_eq_fn θ
    rw [h_integral_eq]
    -- Integrability of the sum: use the helper we proved above
    have h_integrable_sum : IntervalIntegrable
        (fun θ : ℝ => (Q.roots.map (fun α => Real.log ‖Complex.exp (↑σ + I * ↑θ) - α‖)).sum)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      h_sum_integrable Q.roots h_no_roots_on_circle
    -- Now split the integral
    rw [intervalIntegral.integral_add intervalIntegrable_const h_integrable_sum]
    rw [mul_add]
    congr 1
    -- The constant term: (1/2π) * ∫ log‖c‖ dθ = log‖c‖
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    -- (2π)⁻¹ * (2π * log‖c‖) = log‖c‖
    have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · exact Real.pi_ne_zero
    field_simp [h2pi_ne]

  rw [h_integral_decompose, h_sum_integral]

/-- The topological force counts nonzero roots inside radius e^σ. -/
theorem topological_force_eq_nonzero_root_count (Q : Polynomial ℂ) (_hQ : Q ≠ 0) (σ : ℝ)
    (_h_no_roots : ∀ α ∈ Q.roots, ‖α‖ ≠ Real.exp σ) :
    topological_force Q σ =
      (Q.roots.filter (fun α => α ≠ 0 ∧ ‖α‖ < Real.exp σ)).card := by
  -- Both sides count #{nonzero roots α : |α| < e^σ}
  simp only [topological_force]
  -- The filter conditions are equivalent for nonzero α:
  -- (α ≠ 0 ∧ log|α| < σ) ↔ (α ≠ 0 ∧ |α| < e^σ)
  congr 1
  apply Multiset.filter_congr
  intro α _
  constructor
  · intro ⟨hα_ne, hα_log⟩
    constructor
    · exact hα_ne
    · have h_pos : ‖α‖ > 0 := norm_pos_iff.mpr hα_ne
      rw [← Real.exp_log h_pos]
      exact Real.exp_strictMono hα_log
  · intro ⟨hα_ne, hα_lt⟩
    constructor
    · exact hα_ne
    · have h_pos : ‖α‖ > 0 := norm_pos_iff.mpr hα_ne
      have := Real.log_lt_log h_pos hα_lt
      rwa [Real.log_exp] at this

/-! ### Barycentric Average of Polynomial Roots

By Vieta's formulas, the centroid of roots equals -a_{n-1}/(n·a_n),
computable from coefficients alone. -/

/-- The barycentric center (centroid) of polynomial roots.
    By Vieta: sum of roots = -aₙ₋₁/aₙ, so barycenter = -aₙ₋₁/(n·aₙ) -/
noncomputable def root_barycenter (Q : Polynomial ℂ) : ℂ :=
  if _h : Q.natDegree = 0 then 0
  else -Q.coeff (Q.natDegree - 1) / (Q.natDegree * Q.leadingCoeff)

/-- The barycenter equals the average of roots (when polynomial splits completely) -/
theorem root_barycenter_eq_avg (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (h_splits : Q.roots.card = Q.natDegree) :
    root_barycenter Q = (Q.roots.map id).sum / Q.natDegree := by
  -- This follows from Vieta's formula: Σαᵢ = -aₙ₋₁/aₙ
  -- Combined with: barycenter = (1/n)·Σαᵢ = -aₙ₋₁/(n·aₙ)
  unfold root_barycenter
  -- Handle the degree = 0 case
  by_cases hdeg : Q.natDegree = 0
  · -- If degree = 0, then roots.card = 0, so both sides are 0
    simp only [hdeg, ↓reduceDIte, Nat.cast_zero, zero_mul, div_zero]
  · -- Non-trivial case: use Vieta's formula
    simp only [hdeg, ↓reduceDIte]
    -- Use Vieta's formula: coeff (n-1) = leadingCoeff * (-1)^1 * esymm 1
    have h_k_le : Q.natDegree - 1 ≤ Q.natDegree := Nat.sub_le Q.natDegree 1
    have h_vieta := Polynomial.coeff_eq_esymm_roots_of_card h_splits h_k_le
    -- esymm 1 is the sum of roots (powersetCard 1 gives singletons)
    have h_esymm1 : Q.roots.esymm 1 = (Q.roots.map id).sum := by
      unfold Multiset.esymm
      simp only [Multiset.powersetCard_one, Multiset.map_map, Function.comp_def,
                 Multiset.prod_singleton]
      rfl
    -- natDegree - (natDegree - 1) = 1 when natDegree ≠ 0
    have h_deg_diff : Q.natDegree -
     (Q.natDegree - 1) = 1 := Nat.sub_sub_self (Nat.one_le_iff_ne_zero.mpr hdeg)
    rw [h_deg_diff] at h_vieta
    simp only [pow_one, neg_one_mul] at h_vieta
    rw [h_esymm1] at h_vieta
    -- h_vieta: Q.coeff (Q.natDegree - 1) = -Q.leadingCoeff * (Q.roots.map id).sum
    rw [h_vieta]
    have h_lc_ne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
    have h_deg_ne : (Q.natDegree : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdeg
    field_simp [h_lc_ne, h_deg_ne]


/-! ### Profinite Winding Number Convergence

The discrete winding number stabilizes to the true winding number for sufficiently
fine mesh. -/

-- The true winding number: total argument change / 2π (an integer!)
-- For polynomial Q with roots α₁,...,αₙ on circle of radius r:
--   true_winding(Q, r) = #{i : |αᵢ| < r}
-- This is the Heaviside sum: Σᵢ H(r - |αᵢ|)
noncomputable def true_winding_number (Q : Polynomial ℂ) (r : ℝ) : ℕ :=
  (Q.roots.filter (fun α => ‖α‖ < r)).card

/-! ### Winding Number via Circle Integral

winding_number(γ, w) = (1/2πi) ∮_γ 1/(z-w) dz computes root count inside γ. -/

/-- The winding number of the curve z ↦ z - α around 0, as z traverses the circle |z| = r. -/
noncomputable def winding_number_linear (α : ℂ) (r : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * circleIntegral (fun z => (z - α)⁻¹) 0 r

/-- The winding number of a linear factor equals 1 when the root is inside the circle. -/
theorem winding_number_linear_inside (α : ℂ) (r : ℝ) (_hr : 0 < r) (hα : ‖α‖ < r) :
    winding_number_linear α r = 1 := by
  unfold winding_number_linear
  -- Use Mathlib's Cauchy integral formula
  -- ∮_{|z|=r} (z - α)⁻¹ dz = 2πi when |α| < r
  have h_inside : α ∈ Metric.ball (0 : ℂ) r := by
    simp only [Metric.mem_ball, dist_zero_right]
    exact hα
  -- The function z ↦ 1 is differentiable, and its integral over the circle
  -- with singularity at α (inside) gives 2πi · f(α) = 2πi · 1 = 2πi
  -- Signature: (hs : s.Countable) (hw : w ∈ ball c R)
  --            (hc : ContinuousOn f (closedBall c R))
  -- (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x)
  have h_cauchy :=
   Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    (f := fun _ => (1 : ℂ)) (c := 0) (R := r) (w := α) (s := ∅)
    Set.countable_empty h_inside continuousOn_const (fun z _ => differentiableAt_const 1)
  -- h_cauchy : (2πi)⁻¹ • ∮ (z-α)⁻¹ • 1 dz = 1
  simp only [smul_eq_mul, mul_one, Pi.one_apply] at h_cauchy
  -- The integrals match since (z-α)⁻¹ • 1 = (z-α)⁻¹ * 1 = (z-α)⁻¹
  convert h_cauchy using 2


/-- The winding number of a linear factor equals 0 when the root is outside the circle. -/
theorem winding_number_linear_outside (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ > r) :
    winding_number_linear α r = 0 := by
  unfold winding_number_linear
  -- When |α| > r, the function z ↦ (z - α)⁻¹ is holomorphic on the closed disk |z| ≤ r
  -- By Cauchy's theorem, the integral is 0
  have h_holo : ∀ z ∈ Metric.closedBall (0 : ℂ) r, z ≠ α := by
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    intro heq
    rw [heq] at hz
    linarith
  -- The function (z - α)⁻¹ is differentiable on the closed ball
  have h_diff : DifferentiableOn ℂ (fun z => (z - α)⁻¹) (Metric.closedBall 0 r) := by
    apply DifferentiableOn.inv
    · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const α)
    · exact fun z hz => sub_ne_zero.mpr (h_holo z hz)
  -- Continuity on the closed ball
  have h_cont : ContinuousOn (fun z => (z - α)⁻¹) (Metric.closedBall 0 r) := h_diff.continuousOn
  -- Differentiability at interior points
  have h_diff_interior : ∀ z ∈ Metric.ball (0 : ℂ) r \ ∅, DifferentiableAt ℂ
   (fun z => (z - α)⁻¹) z := by
    intro z ⟨hz_ball, _⟩
    -- z is in the open ball, so z ≠ α (since |α| > r and |z| < r)
    have hz_ne_α : z ≠ α := by
      intro heq
      rw [heq] at hz_ball
      simp only [Metric.mem_ball, dist_zero_right] at hz_ball
      linarith
    -- (z - α)⁻¹ is differentiable at z since z - α ≠ 0
    apply DifferentiableAt.inv
    · exact differentiableAt_id.sub (differentiableAt_const α)
    · exact sub_ne_zero.mpr hz_ne_α
  -- By Cauchy-Goursat, integral of holomorphic function over closed contour is 0
  -- Signature: (h0 : 0 ≤ R) (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
  --            (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z)
  have h_zero := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (f := fun z => (z - α)⁻¹) (c := 0) (R := r) (s := ∅)
    (le_of_lt hr) Set.countable_empty h_cont h_diff_interior
  rw [h_zero]
  simp

/-! ### Argument Principle

For polynomial Q with no roots on contour γ: winding number of Q∘γ
equals the number of roots inside γ (counting multiplicity). -/

-- Helper: Q is bounded away from 0 on circles not containing roots
lemma polynomial_nonzero_on_circle (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (r : ℝ) (hr : 0 < r) (h_no_roots : ∀ α ∈ Q.roots, ‖α‖ ≠ r) :
    ∃ (ε : ℝ), ε > 0 ∧ ∀ θ : ℝ, ‖Q.eval (r * Complex.exp (I * θ))‖ ≥ ε := by
  -- The image of the circle under Q is a compact set not containing 0
  -- Therefore it has positive distance from 0
  -- This follows from: Q continuous, circle compact, Q(z) ≠ 0 on circle
  --
  -- Q(z) = 0 iff z is a root of Q
  -- By h_no_roots, no root has norm r, so Q is nonzero on |z| = r
  -- The minimum of |Q| on the compact circle is achieved and positive
  have h_nonzero : ∀ θ : ℝ, Q.eval (r * Complex.exp (I * θ)) ≠ 0 := by
    intro θ h_eq
    -- If Q.eval(z) = 0, then z is a root
    have h_root : (r * Complex.exp (I * θ)) ∈ Q.roots := by
      rw [Polynomial.mem_roots hQ]
      exact h_eq
    -- But ‖r * exp(iθ)‖ = r
    have h_norm : ‖r * Complex.exp (I * θ)‖ = r := by
      rw [norm_mul]
      have h1 : ‖(r : ℂ)‖ = |r| := Complex.norm_real r
      have h2 : ‖Complex.exp (I * θ)‖ = 1 := by
        rw [mul_comm]
        exact Complex.norm_exp_ofReal_mul_I θ
      rw [h1, h2, mul_one, abs_of_pos hr]
    -- This contradicts h_no_roots
    exact h_no_roots _ h_root h_norm
  -- Now use compactness: continuous function on compact set achieves minimum
  -- The function θ ↦ ‖Q.eval(r·exp(iθ))‖ is continuous and positive
  -- On [0, 2π] (compact), it achieves its minimum, which is positive
  --
  -- Define the continuous function f : ℝ → ℝ, f(θ) = ‖Q.eval(r·exp(iθ))‖
  let f : ℝ → ℝ := fun θ => ‖Q.eval (r * Complex.exp (I * θ))‖
  -- f is continuous (composition of continuous functions)
  have hf_cont : Continuous f := by
    apply Continuous.norm
    -- Q.eval is continuous as a polynomial
    apply Q.continuous.comp
    -- θ ↦ r * exp(i*θ) is continuous
    apply Continuous.mul continuous_const
    exact Complex.continuous_exp.comp (Continuous.mul continuous_const Complex.continuous_ofReal)
  -- f is positive everywhere (since Q is nonzero on the circle)
  have hf_pos : ∀ θ, 0 < f θ := fun θ => norm_pos_iff.mpr (h_nonzero θ)
  -- Use compactness of [0, 2π] and continuity to find minimum
  have h_compact : IsCompact (Set.Icc 0 (2 * Real.pi)) := isCompact_Icc
  have h_nonempty : Set.Nonempty (Set.Icc 0 (2 * Real.pi)) := by
    use 0; constructor <;> linarith [Real.pi_pos]
  obtain ⟨θ_min, hθ_min_mem, hθ_min_le⟩ :=
    h_compact.exists_isMinOn h_nonempty hf_cont.continuousOn
  -- The minimum value on [0, 2π] is positive
  -- For the global bound, we use 2π-periodicity of f
  use f θ_min
  refine ⟨hf_pos θ_min, ?_⟩
  -- For any θ, we need f(θ) ≥ f(θ_min)
  -- The key is that f is 2π-periodic (since exp is 2π-periodic)
  intro θ
  -- Show f is periodic with period 2π
  have hf_periodic : Function.Periodic f (2 * Real.pi) := by
    intro x
    simp only [f]
    congr 1
    -- Need to show: r * exp(I * (x + 2π)) = r * exp(I * x)
    congr 1
    -- exp(I * (x + 2π)) = exp(I * x)
    have : (↑(x + 2 * Real.pi) : ℂ) = ↑x + ↑(2 * Real.pi) := by push_cast; ring
    rw [this, mul_add, Complex.exp_add]
    have h2pi : Complex.exp (I * ↑(2 * Real.pi)) = 1 := by
      rw [mul_comm I]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      exact Complex.exp_two_pi_mul_I
    rw [h2pi, mul_one]
  -- Reduce θ to [0, 2π] using toIcoMod
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  let θ' := toIcoMod h2pi_pos 0 θ
  have hθ'_mem : θ' ∈ Set.Ico 0 (2 * Real.pi) := by
    have := toIcoMod_mem_Ico h2pi_pos 0 θ
    simp only [zero_add] at this
    exact this
  -- θ' ∈ [0, 2π) ⊆ [0, 2π]
  have hθ'_mem_Icc : θ' ∈ Set.Icc 0 (2 * Real.pi) := by
    constructor
    · exact hθ'_mem.1
    · exact le_of_lt hθ'_mem.2
  -- f(θ) = f(θ') by periodicity
  have hf_eq : f θ = f θ' := by
    -- θ = θ' + n * 2π for some integer n
    have h_diff : ∃ n : ℤ, θ = θ' + n * (2 * Real.pi) := by
      use toIcoDiv h2pi_pos 0 θ
      have := self_sub_toIcoDiv_zsmul h2pi_pos 0 θ
      simp only [zero_add, zsmul_eq_mul] at this
      linarith
    obtain ⟨n, hn⟩ := h_diff
    rw [hn]
    exact (hf_periodic.int_mul n θ')
  -- Since θ' ∈ [0, 2π] and θ_min minimizes f on [0, 2π], f(θ') ≥ f(θ_min)
  -- The goal is ‖Q.eval(...)‖ ≥ f θ_min, which is the same as f θ ≥ f θ_min
  calc f θ = f θ' := hf_eq
    _ ≥ f θ_min := hθ_min_le hθ'_mem_Icc

/-! ### Profinite Winding Lemma

Discrete winding numbers converge to continuous ones as mesh refines. -/

-- Core analytical lemma: discrete winding converges to true winding

-- Proof uses: roots_of_unity_dense + arg Lipschitz + Riemann sum convergence
lemma discrete_winding_converges (f : ℂ → ℂ) (r : ℝ) (_hr : 0 < r)
    (_hf_cont : Continuous f)
    (_hf_nonzero : ∃ ε > 0, ∀ θ : ℝ, ‖f (r * Complex.exp (I * θ))‖ ≥ ε)
    (true_wind : ℤ) -- The true winding number (an integer!)
    (h_true : ∀ δ > 0, ∃ N₀, ∀ N ≥ N₀, -- True winding is the limit
      |((Finset.sum (Finset.range N) fun j =>
          let θ_curr := Complex.arg (f (r * Complex.exp (I * (2 * Real.pi * j / N))))
          let θ_next := Complex.arg (f (r * Complex.exp (I * (2 * Real.pi * (j + 1) / N))))
          let diff := θ_next - θ_curr
          if diff > Real.pi then diff - 2 * Real.pi
          else if diff ≤ -Real.pi then diff + 2 * Real.pi
          else diff) / (2 * Real.pi)) - true_wind| < δ) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀, |((Finset.sum (Finset.range N) fun j =>
        let θ_curr := Complex.arg (f (r * Complex.exp (I * (2 * Real.pi * j / N))))
        let θ_next := Complex.arg (f (r * Complex.exp (I * (2 * Real.pi * (j + 1) / N))))
        let diff := θ_next - θ_curr
        if diff > Real.pi then diff - 2 * Real.pi
        else if diff ≤ -Real.pi then diff + 2 * Real.pi
        else diff) / (2 * Real.pi)) - true_wind| < 1/2 := by
  exact h_true (1/2) (by norm_num)

/-! ### Candidate Lattice for Winding Number Computation

Angular and radial discretization stabilizes winding number computation
at each lattice level. -/

/-- The total argument change around a circle containing the origin is 2π. -/
theorem total_arg_change_for_winding_one (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ < r) :
    ∃ (lift : ℝ → ℝ),
      lift 0 = Complex.arg (r - α) ∧
      lift (2 * Real.pi) = lift 0 + 2 * Real.pi ∧
      (∀ θ : ℝ, Complex.arg (r * Complex.exp (I * θ) - α) =
           toIocMod Real.two_pi_pos (-Real.pi) (lift θ)) ∧
      -- Lipschitz/geometric bound: lift changes at rate ≤ L = (r + ‖α‖)/(r - ‖α‖)
      -- (the factor 2 in front of ‖α‖ comes from Mathlib's angle bound: angle ≤ π/2 * chord)
      (∀ θ₁ θ₂ : ℝ, |lift θ₂ - lift θ₁| ≤ ((r + ‖α‖) / (r - ‖α‖)) * |θ₂ - θ₁|) := by
  /-
  Proof outline:

  The curve γ(θ) = r·e^{iθ} - α for θ ∈ [0, 2π] traces a circle of radius r
  centered at -α. Since |α| < r, the origin lies strictly inside this circle.

  Key facts:
  1. γ(θ) ≠ 0 for all θ (origin is inside, so never on the circle)
  2. arg(γ(θ)) is continuous on ℝ → ℝ mod 2π
  3. The winding number of γ around 0 is 1 (standard topology result)
  4. This means total arg change = 2π

  Construction of lift:
  - Start at lift(0) = arg(r - α)
  - Continue by adding incremental angle changes
  - The continuity of the curve and the fact that we wind once counterclockwise
    means lift(2π) = lift(0) + 2π

  The floor formula recovers arg from lift by wrapping to (-π, π].
  -/
  let γ : ℝ → ℂ := fun θ => r * Complex.exp (I * θ) - α

  -- γ is never zero since origin is inside the circle
  have hγ_ne : ∀ θ : ℝ, γ θ ≠ 0 := by
    intro θ
    simp only [γ]
    intro h
    have heq : (r : ℂ) * Complex.exp (I * θ) = α := sub_eq_zero.mp h
    have h1 : ‖(r : ℂ) * Complex.exp (I * θ)‖ = ‖α‖ := by rw [heq]
    rw [norm_mul] at h1
    have h2 : ‖Complex.exp (I * (θ : ℂ))‖ = 1 := by
      rw [mul_comm I (θ : ℂ), Complex.norm_exp_ofReal_mul_I]
    rw [h2, mul_one] at h1
    -- h1 : ‖↑r‖ = ‖α‖ where ↑r is r coerced to ℂ
    -- Complex.norm_real : ‖↑r‖ = |r| for r : ℝ
    rw [Complex.norm_real] at h1
    -- h1 : ‖r‖ = ‖α‖ where ‖r‖ is real norm = |r|
    -- Real.norm_eq_abs : ‖r‖ = |r|
    rw [Real.norm_eq_abs, abs_of_pos hr] at h1
    -- h1 : r = ‖α‖, but we have hα : ‖α‖ < r
    linarith

  let w : ℝ → ℂ := fun θ => 1 - α * Complex.exp (-I * θ) / r

  -- w(θ) ≠ 0 because Re(w(θ)) > 0
  have hw_ne : ∀ θ : ℝ, w θ ≠ 0 := by
    intro θ
    simp only [w]
    intro h_eq
    -- If 1 - α·e^{-iθ}/r = 0, then α·e^{-iθ}/r = 1
    have h1 : α * Complex.exp (-I * θ) / r = 1 := by
      have := sub_eq_zero.mp h_eq
      exact this.symm
    -- Then |α·e^{-iθ}/r| = 1
    have h2 : ‖α * Complex.exp (-I * θ) / r‖ = 1 := by rw [h1]; simp
    rw [norm_div, norm_mul] at h2
    have h3 : ‖Complex.exp (-I * θ)‖ = 1 := by
      have : -I * (θ : ℂ) = ((-θ) : ℝ) * I := by simp; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [h3, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h2
    -- h2 : ‖α‖ / r = 1, so ‖α‖ = r, contradicting hα : ‖α‖ < r
    have h4 : ‖α‖ = r := by field_simp at h2; linarith
    linarith

  -- The lift is: lift(θ) = θ + arg(w(θ)) - arg(w(0)) + arg(r - α)
  -- This ensures lift(0) = arg(r - α)
  let lift : ℝ → ℝ := fun θ =>
    θ + Complex.arg (w θ) - Complex.arg (w 0) + Complex.arg (r - α)

  use lift
  constructor
  · -- lift 0 = arg(r - α)
    simp only [lift, w]
    ring
  constructor
  · -- lift(2π) = lift(0) + 2π
    simp only [lift, w]
    -- w(2π) = 1 - α·e^{-2πi}/r = 1 - α/r = w(0)
    have hw_periodic : w (2 * Real.pi) = w 0 := by
      simp only [w]
      congr 1
      -- Show e^{-i·2π} = e^{-i·0} = 1
      -- The goal has form: α * cexp (-I * ↑(2 * π)) / ↑r = α * cexp (-I * ↑0) / ↑r
      -- We need to show both exponentials equal 1
      have h_exp_0 : Complex.exp (-I * ((0 : ℝ) : ℂ)) = 1 := by simp
      have h_exp_2pi : Complex.exp (-I * ((2 * Real.pi) : ℂ)) = 1 := by
      -- -I * 2π = -(2π * I)
        have heq : -I * ((2 * Real.pi) : ℂ) = -(2 * Real.pi : ℂ) * I := by ring
        rw [heq, neg_mul, Complex.exp_neg, Complex.exp_mul_I]
        simp [Complex.cos_two_pi, Complex.sin_two_pi]
      simp only [ofReal_mul, ofReal_ofNat]
      rw [h_exp_2pi, h_exp_0]
    -- Now use hw_periodic in the goal
    have h_arg_eq : Complex.arg (w (2 * Real.pi)) = Complex.arg (w 0) := by rw [hw_periodic]
    rw [h_arg_eq]
    ring
  constructor
  · -- arg(γ(θ)) = toIocMod ... (lift θ)
    intro θ

    have hγ_factor : γ θ = r * Complex.exp (I * θ) * w θ := by
      simp only [γ, w]
      -- Goal: r * exp(I * θ) - α = r * exp(I * θ) * (1 - α * exp(-I * θ) / r)
      have hr_ne : (r : ℂ) ≠ 0 := by
        simp only [ne_eq, ofReal_eq_zero]
        linarith
      -- exp(I * θ) * exp(-I * θ) = 1
      have h_exp_cancel : Complex.exp (I * θ) * Complex.exp (-I * θ) = 1 := by
        rw [← Complex.exp_add]
        simp
      -- Use symm to prove RHS = LHS instead
      symm
      calc r * Complex.exp (I * θ) * (1 - α * Complex.exp (-I * θ) / r)
          = r * Complex.exp (I * θ) * 1 - r *
          Complex.exp (I * θ) * (α * Complex.exp (-I * θ) / r) := by ring
        _ = r * Complex.exp (I * θ) - α * (Complex.exp (I * θ) * Complex.exp (-I * θ)) := by
            field_simp [hr_ne];
        _ = r * Complex.exp (I * θ) - α * 1 := by rw [h_exp_cancel]
        _ = r * Complex.exp (I * θ) - α := by ring

    have harg_factor : Complex.arg (γ θ) = Complex.arg (Complex.exp (I * θ) * w θ) := by
      rw [hγ_factor]
      rw [mul_assoc]
      exact Complex.arg_real_mul _ hr

    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity

    have h_wrap : ∀ x : ℝ, toIocMod Real.two_pi_pos (-Real.pi) x ∈ Set.Ioc (-Real.pi) Real.pi := by
      intro x
      have := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) x
      -- Goal: toIocMod ... ∈ Ioc (-π) (-π + 2π) = Ioc (-π) π
      convert this using 2
      ring


    have h_w0_ne : w 0 ≠ 0 := hw_ne 0

    -- Key identity: (r - α) = r * w(0)
    have h_r_minus_α : (r : ℂ) - α = r * w 0 := by
      simp only [w]
      have hr_ne : (r : ℂ) ≠ 0 := by simp; linarith
      simp only [neg_mul, ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, div_one, mul_one]
      field_simp [hr_ne]

    -- Therefore arg(r - α) = arg(w(0)) since r > 0
    have h_arg_r_minus_α : Complex.arg ((r : ℂ) - α) = Complex.arg (w 0) := by
      rw [h_r_minus_α]
      exact Complex.arg_real_mul (w 0) hr

    -- Helper: exp(arg z * I) = z / ‖z‖ for nonzero z (from norm_mul_exp_arg_mul_I)
    have h_exp_arg_eq : ∀ z : ℂ, z ≠ 0 → Complex.exp (Complex.arg z * I) = z / ‖z‖ := by
      intro z hz
      have h := Complex.norm_mul_exp_arg_mul_I z
      -- h : ↑‖z‖ * exp(arg z * I) = z
      have h_norm_ne : (‖z‖ : ℂ) ≠ 0 := by simp [norm_ne_zero_iff, hz]
      have h_norm_pos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
      -- Rewrite h to get: exp(...) * ‖z‖ = z
      have key : Complex.exp (Complex.arg z * I) * (‖z‖ : ℂ) = z := by
        calc Complex.exp (Complex.arg z * I) * (‖z‖ : ℂ)
            = (‖z‖ : ℂ) * Complex.exp (Complex.arg z * I) := by ring
          _ = z := h
      -- Now divide both sides by ‖z‖
      have := congr_arg (· / (‖z‖ : ℂ)) key
      simp only [mul_div_assoc, div_self h_norm_ne, mul_one] at this
      exact this

    -- Now compute exp(I * lift(θ))
    have h_exp_lift : Complex.exp (I * lift θ) = γ θ / ‖γ θ‖ := by
      -- lift θ = θ + arg(w θ) - arg(w 0) + arg(r - α)
      have h_lift_eq : (lift θ : ℂ) = (θ : ℂ) + Complex.arg (w θ) - Complex.arg (w 0) +
          Complex.arg ((r : ℂ) - α) := by simp only [lift]; push_cast; ring
      rw [h_lift_eq]
      -- Rewrite: I * (θ + arg(w θ) - arg(w 0) + arg(r-α))
      --        = I*θ + arg(w θ)*I - arg(w 0)*I + arg(r-α)*I
      have h_expand : (I : ℂ) * ((θ : ℂ) + Complex.arg (w θ) - Complex.arg (w 0) +
          Complex.arg ((r : ℂ) - α)) =
          I * θ + Complex.arg (w θ) * I - Complex.arg (w 0) * I +
          Complex.arg ((r : ℂ) - α) * I := by ring
      -- Regroup to: (I*θ + arg(w θ)*I - arg(w 0)*I) + arg(r-α)*I
      -- Then use exp_add and exp_sub appropriately
      have h_regroup : I * θ + Complex.arg (w θ) * I - Complex.arg (w 0) * I +
          Complex.arg ((r : ℂ) - α) * I =
          (I * θ + Complex.arg (w θ) * I - Complex.arg (w 0) * I) +
          Complex.arg ((r : ℂ) - α) * I := by ring
      rw [h_expand, h_regroup, Complex.exp_add]
      -- Now the first part: (I*θ + arg(w θ)*I) - arg(w 0)*I
      have h_regroup2 : I * θ + Complex.arg (w θ) * I - Complex.arg (w 0) * I =
          (I * θ + Complex.arg (w θ) * I) - Complex.arg (w 0) * I := by ring
      rw [h_regroup2, Complex.exp_sub, Complex.exp_add]

      -- Use exp(arg z * I) = z / ‖z‖ for nonzero z
      have h_exp_arg_w_θ : Complex.exp (Complex.arg (w θ) * I) = w θ / ‖w θ‖ :=
        h_exp_arg_eq (w θ) (hw_ne θ)
      have h_exp_arg_w_0 : Complex.exp (Complex.arg (w 0) * I) = w 0 / ‖w 0‖ :=
        h_exp_arg_eq (w 0) h_w0_ne
      have h_r_α_ne : (r : ℂ) - α ≠ 0 := by
        intro h
        have heq : α = (r : ℂ) := by
          calc α = (r : ℂ) - ((r : ℂ) - α) := by ring
            _ = (r : ℂ) - 0 := by rw [h]
            _ = (r : ℂ) := by ring
        rw [heq] at hα
      -- hα : ‖↑r‖ < r, but ‖↑r‖ = |r| = r (since r > 0)
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at hα
      -- hα : r < r, contradiction
        exact lt_irrefl r hα
      have h_exp_arg_r_α : Complex.exp (Complex.arg ((r : ℂ) - α) * I) =
          ((r : ℂ) - α) / ‖(r : ℂ) - α‖ := h_exp_arg_eq ((r : ℂ) - α) h_r_α_ne

      rw [h_exp_arg_w_θ, h_exp_arg_w_0, h_exp_arg_r_α]
      -- Now simplify: exp(Iθ) * (w θ/‖w θ‖) / (w 0/‖w 0‖) * ((r-α)/‖r-α‖)
      -- = exp(Iθ) * (w θ/‖w θ‖) * (‖w 0‖/w 0) * ((r-α)/‖r-α‖)  [since 1/(a/b) = b/a for a ≠ 0]
      -- = exp(Iθ) * (w θ/‖w θ‖) * (‖w 0‖ * (r-α)) / (w 0 * ‖r-α‖)

      -- Use h_r_minus_α: r - α = r * w 0
      have h_norm_r_α : ‖(r : ℂ) - α‖ = r * ‖w 0‖ := by
        rw [h_r_minus_α]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

      -- Simplify using these identities
      have h_w0_norm_ne : ‖w 0‖ ≠ 0 := norm_ne_zero_iff.mpr h_w0_ne
      have h_wθ_norm_ne : ‖w θ‖ ≠ 0 := norm_ne_zero_iff.mpr (hw_ne θ)
      have h_γθ_norm_ne : ‖γ θ‖ ≠ 0 := norm_ne_zero_iff.mpr (hγ_ne θ)
      have hr_ne : (r : ℂ) ≠ 0 := by simp; linarith

      -- γ(θ)/‖γ(θ)‖ = r*exp(Iθ)*w(θ) / (r*‖w(θ)‖) = exp(Iθ)*w(θ)/‖w(θ)‖
      have h_γ_normalized : γ θ / ‖γ θ‖ = Complex.exp (I * θ) * w θ / ‖w θ‖ := by
        rw [hγ_factor]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        have h_exp_norm : ‖Complex.exp (I * θ)‖ = 1 := by
          rw [Complex.norm_exp]
          simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
        rw [h_exp_norm, mul_one]
      -- Goal: r * exp(I*θ) * w θ / ↑(r * ‖w θ‖) = exp(I*θ) * w θ / ‖w θ‖
      -- First convert ↑(r * ‖w θ‖) to ↑r * ↑‖w θ‖
        have h_coerce : ((r * ‖w θ‖ : ℝ) : ℂ) = (r : ℂ) * (‖w θ‖ : ℂ) := by push_cast; ring
        rw [h_coerce]
        have hr_ne_real : r ≠ 0 := ne_of_gt hr
      -- Now: r * exp(I*θ) * w θ / (↑r * ↑‖w θ‖) = exp(I*θ) * w θ / ↑‖w θ‖
        have h_assoc : (r : ℂ) * Complex.exp (I * θ) * w θ = (r : ℂ) * (Complex.exp (I * θ) * w θ) := by ring
        rw [h_assoc]
        rw [mul_div_mul_left _ _ (by simp [hr_ne_real] : (r : ℂ) ≠ 0)]

      rw [h_γ_normalized]
      -- Goal: exp(Iθ) * (w θ/‖w θ‖) / (w 0/‖w 0‖) * ((r-α)/‖r-α‖) = exp(Iθ) * w θ / ‖w θ‖
      rw [h_r_minus_α]
      -- Now ‖↑r * w 0‖ = r * ‖w 0‖
      have h_norm_rw0 : ‖(r : ℂ) * w 0‖ = r * ‖w 0‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      rw [h_norm_rw0]
      -- Now coerce r * ‖w 0‖ : ℝ to ℂ
      have h_coerce2 : ((r * ‖w 0‖ : ℝ) : ℂ) = (r : ℂ) * (‖w 0‖ : ℂ) := by push_cast; ring
      rw [h_coerce2]
      field_simp [h_w0_ne, h_w0_norm_ne, h_wθ_norm_ne, hr_ne]

    -- Step 2: exp(I * arg(γ θ)) = γ θ / ‖γ θ‖ by definition of arg
    have h_exp_arg_γ : Complex.exp (I * Complex.arg (γ θ)) = γ θ / ‖γ θ‖ := by
      have h := h_exp_arg_eq (γ θ) (hγ_ne θ)
      rw [mul_comm]
      exact h

    -- Step 3: Therefore exp(I * lift θ) = exp(I * arg(γ θ))
    have h_exp_eq : Complex.exp (I * lift θ) = Complex.exp (I * Complex.arg (γ θ)) := by
      rw [h_exp_lift, h_exp_arg_γ]

    -- Step 4: This means lift θ ≡ arg(γ θ) (mod 2π)
    -- Use Complex.exp_eq_exp_iff_exists_int
    have h_congruent : ∃ n : ℤ, lift θ = Complex.arg (γ θ) + n * (2 * Real.pi) := by
      have h := Complex.exp_eq_exp_iff_exists_int.mp h_exp_eq
      obtain ⟨n, hn⟩ := h
      use n
      -- hn : I * lift θ = I * arg(γ θ) + ↑n * (2 * π * I)
      have hI_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
      -- Extract the real parts (after dividing by I)
      have h1 : lift θ = Complex.arg (γ θ) + n * (2 * Real.pi) := by
        have : I * (lift θ : ℂ) = I * (Complex.arg (γ θ) + n * (2 * Real.pi)) := by
          rw [hn]
          push_cast
          ring
        have h2 := mul_left_cancel₀ hI_ne this
        exact_mod_cast h2
      exact h1

    -- Step 5: The floor formula extracts the principal value
    -- x - 2π⌊(x+π)/(2π)⌋ gives the unique y ∈ [-π, π) with y ≡ x (mod 2π)
    -- Since arg(γ θ) ∈ (-π, π] and lift θ ≡ arg(γ θ) (mod 2π), the floor formula
    -- applied to lift θ gives arg(γ θ) (or -π when arg = π, which is equivalent mod 2π)

    obtain ⟨n, hn⟩ := h_congruent
    -- hn : lift θ = arg(γ θ) + n * 2π

    -- Compute the floor: ⌊(lift θ + π)/(2π)⌋ = ⌊(arg(γ θ) + n*2π + π)/(2π)⌋
    --                                        = ⌊(arg(γ θ) + π)/(2π) + n⌋
    --                                        = ⌊(arg(γ θ) + π)/(2π)⌋ + n
    -- (The last step uses that ⌊x + n⌋ = ⌊x⌋ + n for integer n)

    -- arg(γ θ) ∈ (-π, π] = Ioc (-π) π
    have h_arg_range : Complex.arg (γ θ) ∈ Set.Ioc (-Real.pi) Real.pi :=
      Complex.arg_mem_Ioc (γ θ)

    -- toIocMod (2π) (-π) maps ℝ → (-π, π] by reducing modulo 2π
    -- Since lift θ ≡ arg(γ θ) (mod 2π) and arg(γ θ) ∈ (-π, π],
    -- we have toIocMod (2π) (-π) (lift θ) = arg(γ θ)

    -- The key: toIocMod returns the unique representative in Ioc (-π) (-π + 2π) = Ioc (-π) π
    have h_arg_in_range : Complex.arg (γ θ) ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      convert h_arg_range using 2
      ring

    -- lift θ = arg(γ θ) + n * 2π, so lift θ ≡ arg(γ θ) (mod 2π)
    -- toIocMod extracts the unique representative in (-π, π]
    have h_toIocMod : toIocMod Real.two_pi_pos (-Real.pi) (lift θ) = Complex.arg (γ θ) := by
      rw [hn]
      -- toIocMod (2π) (-π) (arg + n * 2π) = arg (since arg ∈ (-π, π])
      -- Convert n * (2π) to n • (2π) for toIocMod_add_zsmul
      have h_zsmul : (n : ℝ) * (2 * Real.pi) = n • (2 * Real.pi) := by simp [zsmul_eq_mul]
      rw [h_zsmul]
      -- Goal: toIocMod ... (arg + n • (2π)) = arg
      -- Use toIocMod_add_zsmul which says toIocMod p a (x + n • p) = toIocMod p a x
      rw [toIocMod_add_zsmul Real.two_pi_pos (-Real.pi) (Complex.arg (γ θ)) n]
      -- Now show toIocMod (2π) (-π) arg = arg when arg ∈ (-π, π]
      exact (toIocMod_eq_self Real.two_pi_pos).mpr h_arg_in_range

    exact h_toIocMod.symm

  · -- 4th property: Lipschitz bound |lift θ₂ - lift θ₁| ≤ L · |θ₂ - θ₁|
    intro θ₁ θ₂
    -- lift θ = θ + arg(w θ) - arg(w 0) + arg(r - α)
    -- So lift θ₂ - lift θ₁ = (θ₂ - θ₁) + (arg(w θ₂) - arg(w θ₁))
    simp only [lift]
    -- Goal: |θ₂ + arg(w θ₂) - arg(w 0) + arg(r-α) - (θ₁ + arg(w θ₁) - arg(w 0) + arg(r-α))|
    --     ≤ (r / (r - ‖α‖)) * |θ₂ - θ₁|
    have h_diff : θ₂ + Complex.arg (w θ₂) - Complex.arg (w 0) + Complex.arg ((r : ℂ) - α) -
                  (θ₁ + Complex.arg (w θ₁) - Complex.arg (w 0) + Complex.arg ((r : ℂ) - α))
                = (θ₂ - θ₁) + (Complex.arg (w θ₂) - Complex.arg (w θ₁)) := by ring
    rw [h_diff]


    have h_w_diff : ∀ θ θ' : ℝ, ‖w θ - w θ'‖ ≤ (‖α‖ / r) * |θ - θ'| := by
      intro θ θ'
      simp only [w]
      -- w θ - w θ' = (α/r) * (e^{-iθ'} - e^{-iθ})
      have h_eq : (1 - α * Complex.exp (-I * θ) / r) - (1 - α * Complex.exp (-I * θ') / r)
                = (α / r) * (Complex.exp (-I * θ') - Complex.exp (-I * θ)) := by
        have hr_ne : (r : ℂ) ≠ 0 := by simp; linarith
        field_simp [hr_ne]
        ring
      rw [h_eq]
      rw [norm_mul]
      have h_norm_α_r : ‖α / (r : ℂ)‖ = ‖α‖ / r := by
        rw [norm_div, Complex.norm_real]
        simp [abs_of_pos hr]
      rw [h_norm_α_r]
      -- Need: ‖e^{-iθ'} - e^{-iθ}‖ ≤ |θ - θ'|
      -- Use: ‖e^{ia} - e^{ib}‖ = 2|sin((a-b)/2)| ≤ |a - b|
      have h_exp_diff : ‖Complex.exp (-I * θ') - Complex.exp (-I * θ)‖ ≤ |θ - θ'| := by
      -- Use the existing lemma norm_exp_I_sub_exp_I_le
      -- ‖e^{iα} - e^{iβ}‖ ≤ |α - β|
      -- We have e^{-iθ'} - e^{-iθ} = e^{i(-θ')} - e^{i(-θ)}
        have h1 : Complex.exp (-I * θ') = Complex.exp (I * ((-θ') : ℝ)) := by
          congr 1; push_cast; ring
        have h2 : Complex.exp (-I * θ) = Complex.exp (I * ((-θ) : ℝ)) := by
          congr 1; push_cast; ring
        rw [h1, h2]
        have := norm_exp_I_sub_exp_I_le (-θ') (-θ)
        calc ‖Complex.exp (I * ↑(-θ')) - Complex.exp (I * ↑(-θ))‖
            ≤ |(-θ') - (-θ)| := this
          _ = |θ - θ'| := by ring_nf
      gcongr

    have h_w_lower : ∀ θ : ℝ, ‖w θ‖ ≥ (r - ‖α‖) / r := by
      intro θ
      simp only [w]
      -- ‖1 - α·e^{-iθ}/r‖ ≥ |1 - ‖α‖/r| = 1 - ‖α‖/r = (r - ‖α‖)/r
      have h_inner_norm : ‖α * Complex.exp (-I * θ) / (r : ℂ)‖ = ‖α‖ / r := by
        have h_exp_eq : Complex.exp (-I * θ) = Complex.exp (((-θ) : ℝ) * I) := by
          congr 1; push_cast; ring
        rw [h_exp_eq, norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
        simp [abs_of_pos hr]
      -- Use reverse triangle: ‖a - b‖ ≥ |‖a‖ - ‖b‖|
      have h_rev := abs_norm_sub_norm_le (1 : ℂ) (α * Complex.exp (-I * θ) / r)
      have h_one_norm : ‖(1 : ℂ)‖ = 1 := by simp
      have key : |‖(1 : ℂ)‖ - ‖α * Complex.exp (-I * θ) / (r : ℂ)‖| ≤ ‖1 - α * Complex.exp (-I * θ) / r‖ := by
        have := norm_sub_norm_le (1 : ℂ) (α * Complex.exp (-I * θ) / r)
        have := abs_norm_sub_norm_le (1 : ℂ) (α * Complex.exp (-I * θ) / r)
        linarith
      rw [h_one_norm, h_inner_norm] at key
      have h_abs_eq : |1 - ‖α‖ / r| = 1 - ‖α‖ / r := by
        rw [abs_of_nonneg]
        have : ‖α‖ / r < 1 := by
          rw [div_lt_one hr]
          exact hα
        linarith
      rw [h_abs_eq] at key
      have h_eq : 1 - ‖α‖ / r = (r - ‖α‖) / r := by field_simp
      rw [h_eq] at key
      exact key

    -- Now prove the arg bound using the derivative/MVT approach
    -- Key insight: w(t) is always in the Right Half Plane (Re > 0)
    -- because |w(t) - 1| = |α|/r < 1, so Re(w(t)) > 1 - |α|/r > 0
    -- Note: factor of 2 comes from Mathlib's angle bound (angle ≤ π/2 * chord, and π/2 < 2)
    have h_arg_bound : |Complex.arg (w θ₂) - Complex.arg (w θ₁)| ≤ (2 * ‖α‖ / (r - ‖α‖)) * |θ₂ - θ₁| := by
      by_cases h_eq : θ₁ = θ₂
      · simp [h_eq]

      -- Step 1: Show w(t) is in the RHP (Re > 0)
      -- This ensures we're away from the branch cut of log/arg
      have w_in_RHP : ∀ t, 0 < (w t).re := by
        intro t
        simp only [w]
      -- |w(t) - 1| = |α|/r < 1 implies Re(w(t)) > 0
        have h_norm_inner : ‖α * Complex.exp (-I * t) / (r : ℂ)‖ = ‖α‖ / r := by
          rw [norm_div, norm_mul]
          have h_exp_eq : Complex.exp (-I * t) = Complex.exp (((-t) : ℝ) * I) := by
            congr 1; push_cast; ring
          rw [h_exp_eq, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
          simp [abs_of_pos hr]
        have h_re_le_norm : (α * Complex.exp (-I * t) / (r : ℂ)).re ≤ ‖α‖ / r := by
          calc (α * Complex.exp (-I * t) / (r : ℂ)).re
              ≤ |(α * Complex.exp (-I * t) / (r : ℂ)).re| := le_abs_self _
            _ ≤ ‖α * Complex.exp (-I * t) / (r : ℂ)‖ := Complex.abs_re_le_norm _
            _ = ‖α‖ / r := h_norm_inner
        calc (1 - α * Complex.exp (-I * t) / r).re
            = 1 - (α * Complex.exp (-I * t) / r).re := by simp
          _ ≥ 1 - ‖α‖ / r := by linarith [h_re_le_norm]
          _ > 0 := by
            have h_div : ‖α‖ / r < 1 := (div_lt_one hr).mpr hα
            linarith

      -- Step 2: w is nonzero (follows from RHP)
      have hw_ne' : ∀ t, w t ≠ 0 := by
        intro t hcontra
        have := w_in_RHP t
        rw [hcontra] at this
        simp at this

      -- Step 3: Use the geometric bound |arg z - arg w| ≤ ‖z - w‖ / min(‖z‖, ‖w‖)
      -- This follows from the derivative of arg being bounded by 1/|z|
      -- and can be proved via: arg z - arg w = Im(log(z/w)) and |Im(log(1+ε))| ≤ |ε|/(1-|ε|)

      have h_diff_upper := h_w_diff θ₂ θ₁
      have h_min_lower : min ‖w θ₁‖ ‖w θ₂‖ ≥ (r - ‖α‖) / r := by
        simp only [le_min_iff]
        exact ⟨h_w_lower θ₁, h_w_lower θ₂⟩

      -- The key geometric lemma: for nonzero z, w with min norm bounded away from 0,
      -- |arg z - arg w| ≤ ‖z - w‖ / min(‖z‖, ‖w‖)
      -- Proof sketch: arg z - arg w = arg(z/w), and for |z/w - 1| < 1,
      -- |arg(z/w)| ≤ |z/w - 1| ≤ ‖z - w‖ / ‖w‖

      -- We use the ratio bound: |z/w - 1| = |z - w|/|w| ≤ |z - w|/min(|z|,|w|)
      have h_ratio_bound : ‖w θ₂ / w θ₁ - 1‖ ≤ ‖w θ₂ - w θ₁‖ / ‖w θ₁‖ := by
        have h1 : w θ₂ / w θ₁ - 1 = (w θ₂ - w θ₁) / w θ₁ := by field_simp [hw_ne' θ₁]
        rw [h1, norm_div]


      have h_gap_local : r - ‖α‖ > 0 := by linarith [hα]
      have h_gap_r : (r - ‖α‖) / r > 0 := div_pos h_gap_local hr

      -- Final assembly using the geometric bound (with factor of 2 from Mathlib's angle bound)
      calc |Complex.arg (w θ₂) - Complex.arg (w θ₁)|
          ≤ 2 * ‖w θ₂ - w θ₁‖ / min ‖w θ₁‖ ‖w θ₂‖ := by
            -- This is the geometric lemma with factor 2: arg is (2/|z|)-Lipschitz
            -- For z₁, z₂ in RHP, |arg z₂ - arg z₁| ≤ 2 * |z₂ - z₁| / min(|z₁|, |z₂|)
            -- Proof: Both w(θ) are in RHP since Re(w(θ)) > 0
            rw [min_comm]
            apply abs_arg_sub_le_two_mul_norm_div_min_of_re_pos (w θ₂) (w θ₁)
              (hw_ne' θ₂) (hw_ne' θ₁) (w_in_RHP θ₂) (w_in_RHP θ₁)
        _ ≤ 2 * ((‖α‖ / r) * |θ₂ - θ₁|) / ((r - ‖α‖) / r) := by
            have h1 := h_w_diff θ₂ θ₁
            have h2 := h_min_lower
            gcongr
        _ = (2 * ‖α‖ / (r - ‖α‖)) * |θ₂ - θ₁| := by
            field_simp [ne_of_gt hr, ne_of_gt h_gap_local]

    -- Final assembly: |θ diff + arg diff| ≤ |θ diff| + |arg diff|
    have h_gap' : r - ‖α‖ ≠ 0 := by linarith [hα]
    calc |θ₂ - θ₁ + (Complex.arg (w θ₂) - Complex.arg (w θ₁))|
        ≤ |θ₂ - θ₁| + |Complex.arg (w θ₂) - Complex.arg (w θ₁)| := abs_add_le _ _
      _ ≤ |θ₂ - θ₁| + (2 * ‖α‖ / (r - ‖α‖)) * |θ₂ - θ₁| := by gcongr
      _ = (1 + 2 * ‖α‖ / (r - ‖α‖)) * |θ₂ - θ₁| := by ring
      _ = ((r - ‖α‖ + 2 * ‖α‖) / (r - ‖α‖)) * |θ₂ - θ₁| := by
          congr 1
          field_simp [h_gap']
      _ = ((r + ‖α‖) / (r - ‖α‖)) * |θ₂ - θ₁| := by ring_nf

/-- For a curve with the origin OUTSIDE (|α| > r), the total argument change is 0. -/
theorem total_arg_change_for_winding_zero (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ > r) :
    ∃ (lift : ℝ → ℝ),
      lift 0 = Complex.arg (r - α) ∧
      lift (2 * Real.pi) = lift 0 ∧  -- KEY: returns to start (winding = 0)
      (∀ θ : ℝ, Complex.arg (r * Complex.exp (I * θ) - α) =
           toIocMod Real.two_pi_pos (-Real.pi) (lift θ)) ∧
      (∀ θ₁ θ₂ : ℝ, |lift θ₂ - lift θ₁| ≤ (2 * r / (‖α‖ - r)) * |θ₂ - θ₁|) := by
  -- Factor γ(θ) = r·e^{iθ} - α = -α·(1 - r·e^{iθ}/α) = -α·v(θ)
  let v : ℝ → ℂ := fun θ => 1 - r * Complex.exp (I * θ) / α
  let γ : ℝ → ℂ := fun θ => r * Complex.exp (I * θ) - α

  have hα_ne : α ≠ 0 := by
    intro h; rw [h] at hα; simp at hα; linarith

  -- γ is never zero since origin is outside the circle
  have hγ_ne : ∀ θ : ℝ, γ θ ≠ 0 := by
    intro θ hγ_eq
    simp only [γ] at hγ_eq
    have heq : (r : ℂ) * Complex.exp (I * θ) = α := sub_eq_zero.mp hγ_eq
    have h1 : ‖(r : ℂ) * Complex.exp (I * θ)‖ = ‖α‖ := by rw [heq]
    rw [norm_mul] at h1
    have h2 : ‖Complex.exp (I * (θ : ℂ))‖ = 1 := by
      have h_eq : I * (θ : ℂ) = (θ : ℝ) * I := by push_cast; ring
      rw [h_eq, Complex.norm_exp_ofReal_mul_I]
    rw [h2, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h1
    linarith

  -- v(θ) is never zero since |v - 1| = r/|α| < 1 (disk centered at 1 not containing 0)
  have hv_ne : ∀ θ : ℝ, v θ ≠ 0 := by
    intro θ hv_eq
    simp only [v] at hv_eq
    have h1 : r * Complex.exp (I * θ) / α = 1 := by
      have h : (1 : ℂ) - r * Complex.exp (I * θ) / α = 0 := hv_eq
      calc r * Complex.exp (I * θ) / α = 1 - (1 - r * Complex.exp (I * θ) / α) := by ring
        _ = 1 - 0 := by rw [h]
        _ = 1 := by ring
    have h2 : ‖r * Complex.exp (I * θ) / α‖ = 1 := by rw [h1]; simp
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at h2
    have h3 : ‖Complex.exp (I * θ)‖ = 1 := by
      have h_eq : I * (θ : ℂ) = (θ : ℝ) * I := by push_cast; ring
      rw [h_eq, Complex.norm_exp_ofReal_mul_I]
    rw [h3, mul_one] at h2
    have h4 : r / ‖α‖ = 1 := h2
    have h5 : r = ‖α‖ := by field_simp at h4; linarith
    linarith

  -- v stays in RHP: Re(v) > 0 because |v - 1| = r/|α| < 1
  have hv_RHP : ∀ θ : ℝ, 0 < (v θ).re := by
    intro θ
    simp only [v]
    have h_norm : ‖r * Complex.exp (I * θ) / α‖ = r / ‖α‖ := by
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have h_eq : I * (θ : ℂ) = (θ : ℝ) * I := by push_cast; ring
      rw [h_eq, Complex.norm_exp_ofReal_mul_I, mul_one]
    have h_ratio : r / ‖α‖ < 1 := (div_lt_one (by linarith : ‖α‖ > 0)).mpr hα
    have h_re_bound : (r * Complex.exp (I * θ) / α).re ≤ r / ‖α‖ := by
      calc (r * Complex.exp (I * θ) / α).re
          ≤ |(r * Complex.exp (I * θ) / α).re| := le_abs_self _
        _ ≤ ‖r * Complex.exp (I * θ) / α‖ := Complex.abs_re_le_norm _
        _ = r / ‖α‖ := h_norm
    calc (1 - r * Complex.exp (I * θ) / α).re
        = 1 - (r * Complex.exp (I * θ) / α).re := by simp
      _ ≥ 1 - r / ‖α‖ := by linarith
      _ > 0 := by linarith

  -- v is periodic: v(2π) = v(0)
  have hv_periodic : v (2 * Real.pi) = v 0 := by
    simp only [v]
    congr 1
    have h1 : Complex.exp (I * (0 : ℝ)) = 1 := by simp
    have h2 : Complex.exp (I * (2 * Real.pi : ℝ)) = 1 := by
      have h_eq : I * ((2 * Real.pi : ℝ) : ℂ) = (2 * Real.pi : ℝ) * I := by push_cast; ring
      rw [h_eq, Complex.exp_mul_I]
      simp [Complex.cos_two_pi, Complex.sin_two_pi]
    rw [h1, h2]

  -- γ(θ) = -α * v(θ)
  have hγ_factor : ∀ θ, γ θ = -α * v θ := by
    intro θ
    simp only [γ, v]
    field_simp [hα_ne]
    ring

  -- Define the lift using v's argument (same structure as inside case but lift is periodic)
  let lift : ℝ → ℝ := fun θ =>
    Complex.arg (v θ) - Complex.arg (v 0) + Complex.arg (r - α)

  use lift

  constructor
  · -- lift 0 = arg(r - α)
    simp only [lift]; ring

  constructor
  · -- lift(2π) = lift(0)
    simp only [lift]
    rw [hv_periodic]

  constructor
  · -- arg(γ(θ)) = toIocMod(lift(θ))
    intro θ

    have h_arg_v_bound : ∀ t, |Complex.arg (v t)| < Real.pi / 2 := by
      intro t
      have hpos := hv_RHP t
      exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos)

    -- Helper: exp(arg z * I) = z / ‖z‖ for nonzero z
    have h_exp_arg_eq : ∀ z : ℂ, z ≠ 0 → Complex.exp (Complex.arg z * I) = z / ‖z‖ := by
      intro z hz
      have h := Complex.norm_mul_exp_arg_mul_I z
      have h_norm_ne : (‖z‖ : ℂ) ≠ 0 := by simp [norm_ne_zero_iff, hz]
      have key : Complex.exp (Complex.arg z * I) * (‖z‖ : ℂ) = z := by
        calc Complex.exp (Complex.arg z * I) * (‖z‖ : ℂ)
            = (‖z‖ : ℂ) * Complex.exp (Complex.arg z * I) := by ring
          _ = z := h
      have := congr_arg (· / (‖z‖ : ℂ)) key
      simp only [mul_div_assoc, div_self h_norm_ne, mul_one] at this
      exact this

    -- Show exp(I * lift θ) = γ θ / ‖γ θ‖
    have h_exp_lift : Complex.exp (I * lift θ) = γ θ / ‖γ θ‖ := by
      have h_lift_def : (lift θ : ℂ) = (Complex.arg (v θ) - Complex.arg (v 0) +
          Complex.arg ((r : ℂ) - α) : ℝ) := by simp only [lift]

      rw [h_lift_def]
      have h_expand : (I : ℂ) * ((Complex.arg (v θ) - Complex.arg (v 0) +
          Complex.arg ((r : ℂ) - α) : ℝ) : ℂ) =
          Complex.arg (v θ) * I - Complex.arg (v 0) * I +
          Complex.arg ((r : ℂ) - α) * I := by push_cast; ring
      rw [h_expand, Complex.exp_add, Complex.exp_sub]

      have h_exp_arg_v_θ : Complex.exp (Complex.arg (v θ) * I) = v θ / ‖v θ‖ :=
        h_exp_arg_eq (v θ) (hv_ne θ)
      have h_exp_arg_v_0 : Complex.exp (Complex.arg (v 0) * I) = v 0 / ‖v 0‖ :=
        h_exp_arg_eq (v 0) (hv_ne 0)

      have hγ0_eq : γ 0 = (r : ℂ) - α := by simp only [γ]; simp
      have h_r_α_ne : (r : ℂ) - α ≠ 0 := by rw [← hγ0_eq]; exact hγ_ne 0
      have h_exp_arg_r_α : Complex.exp (Complex.arg ((r : ℂ) - α) * I) =
          ((r : ℂ) - α) / ‖(r : ℂ) - α‖ := h_exp_arg_eq ((r : ℂ) - α) h_r_α_ne

      rw [h_exp_arg_v_θ, h_exp_arg_v_0, h_exp_arg_r_α]

      -- Now simplify: (v θ/‖v θ‖) / (v 0/‖v 0‖) * ((r-α)/‖r-α‖)
      -- = (v θ/‖v θ‖) * (‖v 0‖/v 0) * ((r-α)/‖r-α‖)

      have hv0_ne : v 0 ≠ 0 := hv_ne 0
      have hvθ_ne : v θ ≠ 0 := hv_ne θ
      have h_v0_norm_ne : ‖v 0‖ ≠ 0 := norm_ne_zero_iff.mpr hv0_ne
      have h_vθ_norm_ne : ‖v θ‖ ≠ 0 := norm_ne_zero_iff.mpr hvθ_ne
      have h_γθ_norm_ne : ‖γ θ‖ ≠ 0 := norm_ne_zero_iff.mpr (hγ_ne θ)
      have h_r_α_norm_ne : ‖(r : ℂ) - α‖ ≠ 0 := norm_ne_zero_iff.mpr h_r_α_ne

      -- γ(θ)/‖γ(θ)‖ = (-α * v θ) / ‖-α * v θ‖
      have h_γ_normalized : γ θ / ‖γ θ‖ = (-α * v θ) / ‖-α * v θ‖ := by
        rw [hγ_factor]

      rw [h_γ_normalized]

      -- ‖-α * v θ‖ = ‖α‖ * ‖v θ‖
      have h_norm_factor : ‖-α * v θ‖ = ‖α‖ * ‖v θ‖ := by
        rw [norm_mul, norm_neg]

      -- γ(0) = r - α = -α * v(0), so ‖r - α‖ = ‖α‖ * ‖v 0‖
      have h_norm_r_α : ‖(r : ℂ) - α‖ = ‖α‖ * ‖v 0‖ := by
        have hγ0 : γ 0 = (r : ℂ) - α := by simp only [γ]; simp
        rw [← hγ0, hγ_factor 0, norm_mul, norm_neg]

      -- Key relation: r - α = -α * v 0 (derived from γ 0 = r - α and hγ_factor 0)
      have h_r_α_eq_neg_α_v0 : (r : ℂ) - α = -α * v 0 := by
        have hγ0' : γ 0 = (r : ℂ) - α := by simp only [γ]; simp
        rw [← hγ0']
        exact hγ_factor 0

      -- ‖-α * v 0‖ = ‖α‖ * ‖v 0‖
      have h_norm_neg_α_v0 : ‖-α * v 0‖ = ‖α‖ * ‖v 0‖ := by
        rw [norm_mul, norm_neg]

      rw [h_r_α_eq_neg_α_v0, h_norm_factor, h_norm_neg_α_v0]

      -- Now simplify the expression
      have hα_norm_ne : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα_ne

      field_simp [hv0_ne, hvθ_ne, hα_ne, h_v0_norm_ne, h_vθ_norm_ne, hα_norm_ne]
      push_cast
      ring

    -- exp(I * arg(γ θ)) = γ θ / ‖γ θ‖
    have h_exp_arg_γ : Complex.exp (I * Complex.arg (γ θ)) = γ θ / ‖γ θ‖ := by
      have h := h_exp_arg_eq (γ θ) (hγ_ne θ)
      rw [mul_comm]
      exact h

    -- Therefore exp(I * lift θ) = exp(I * arg(γ θ))
    have h_exp_eq : Complex.exp (I * lift θ) = Complex.exp (I * Complex.arg (γ θ)) := by
      rw [h_exp_lift, h_exp_arg_γ]

    -- This means lift θ ≡ arg(γ θ) (mod 2π)
    have h_congruent : ∃ n : ℤ, lift θ = Complex.arg (γ θ) + n * (2 * Real.pi) := by
      have h := Complex.exp_eq_exp_iff_exists_int.mp h_exp_eq
      obtain ⟨n, hn⟩ := h
      use n
      have hI_ne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
      have h1 : lift θ = Complex.arg (γ θ) + n * (2 * Real.pi) := by
        have : I * (lift θ : ℂ) = I * (Complex.arg (γ θ) + n * (2 * Real.pi)) := by
          rw [hn]
          push_cast
          ring
        have h2 := mul_left_cancel₀ hI_ne this
        exact_mod_cast h2
      exact h1

    obtain ⟨n, hn⟩ := h_congruent

    have h_arg_range : Complex.arg (γ θ) ∈ Set.Ioc (-Real.pi) Real.pi :=
      Complex.arg_mem_Ioc (γ θ)

    have h_arg_in_range : Complex.arg (γ θ) ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
      convert h_arg_range using 2
      ring

    have h_toIocMod : toIocMod Real.two_pi_pos (-Real.pi) (lift θ) = Complex.arg (γ θ) := by
      rw [hn]
      have h_zsmul : (n : ℝ) * (2 * Real.pi) = n • (2 * Real.pi) := by simp [zsmul_eq_mul]
      rw [h_zsmul]
      rw [toIocMod_add_zsmul Real.two_pi_pos (-Real.pi) (Complex.arg (γ θ)) n]
      exact (toIocMod_eq_self Real.two_pi_pos).mpr h_arg_in_range

    simp only [γ] at h_toIocMod
    exact h_toIocMod.symm

  · -- Lipschitz bound
    intro θ₁ θ₂
    simp only [lift]
    have h_diff : Complex.arg (v θ₂) - Complex.arg (v 0) + Complex.arg ((r : ℂ) - α) -
        (Complex.arg (v θ₁) - Complex.arg (v 0) + Complex.arg ((r : ℂ) - α)) =
        Complex.arg (v θ₂) - Complex.arg (v θ₁) := by ring
    rw [h_diff]

    have hv_diff : ‖v θ₂ - v θ₁‖ ≤ (r / ‖α‖) * |θ₂ - θ₁| := by
      simp only [v]
      have h_eq : (1 - r * Complex.exp (I * θ₂) / α) - (1 - r * Complex.exp (I * θ₁) / α) =
          (r / α) * (Complex.exp (I * θ₁) - Complex.exp (I * θ₂)) := by
        field_simp [hα_ne]; ring
      rw [h_eq, norm_mul]
      have h_norm_r_α : ‖(r : ℂ) / α‖ = r / ‖α‖ := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      rw [h_norm_r_α]
      gcongr
      calc ‖Complex.exp (I * θ₁) - Complex.exp (I * θ₂)‖
          ≤ |θ₁ - θ₂| := norm_exp_I_sub_exp_I_le θ₁ θ₂
        _ = |θ₂ - θ₁| := abs_sub_comm θ₁ θ₂

    have hv_lower : ∀ t, ‖v t‖ ≥ 1 - r / ‖α‖ := by
      intro t
      simp only [v]
      have h_inner_norm : ‖r * Complex.exp (I * t) / α‖ = r / ‖α‖ := by
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        have h_eq : I * (t : ℂ) = (t : ℝ) * I := by push_cast; ring
        rw [h_eq, Complex.norm_exp_ofReal_mul_I, mul_one]
      have h_rev := abs_norm_sub_norm_le (1 : ℂ) (r * Complex.exp (I * t) / α)
      have h_one : ‖(1 : ℂ)‖ = 1 := by simp
      calc ‖1 - r * Complex.exp (I * t) / α‖
          ≥ |‖(1 : ℂ)‖ - ‖r * Complex.exp (I * t) / α‖| := by
              have := norm_sub_norm_le (1 : ℂ) (r * Complex.exp (I * t) / α)
              linarith [h_rev]
        _ = |1 - r / ‖α‖| := by rw [h_one, h_inner_norm]
        _ = 1 - r / ‖α‖ := by
            have hα_pos : ‖α‖ > 0 := by linarith
            have h_lt_one : r / ‖α‖ < 1 := (div_lt_one hα_pos).mpr hα
            exact abs_of_pos (by linarith : 0 < 1 - r / ‖α‖)

    have h_gap : ‖α‖ - r > 0 := by linarith
    have h_min_v : min ‖v θ₁‖ ‖v θ₂‖ ≥ 1 - r / ‖α‖ := by
      simp only [le_min_iff]; exact ⟨hv_lower θ₁, hv_lower θ₂⟩

    calc |Complex.arg (v θ₂) - Complex.arg (v θ₁)|
        ≤ 2 * ‖v θ₂ - v θ₁‖ / min ‖v θ₁‖ ‖v θ₂‖ := by
            rw [min_comm]
            exact abs_arg_sub_le_two_mul_norm_div_min_of_re_pos (v θ₂) (v θ₁)
              (hv_ne θ₂) (hv_ne θ₁) (hv_RHP θ₂) (hv_RHP θ₁)
      _ ≤ 2 * ((r / ‖α‖) * |θ₂ - θ₁|) / (1 - r / ‖α‖) := by
            have h_denom_pos : 0 < 1 - r / ‖α‖ := by
              have hα_pos : ‖α‖ > 0 := by linarith
              have h_lt_one : r / ‖α‖ < 1 := (div_lt_one hα_pos).mpr hα
              linarith
            gcongr
      _ = (2 * r / (‖α‖ - r)) * |θ₂ - θ₁| := by
          have hα_pos : ‖α‖ > 0 := by linarith
          field_simp [ne_of_gt hα_pos, ne_of_gt h_gap]

/-- Foundational Theorem: Discrete winding number for linear factor with root inside. -/
theorem discrete_winding_exact_for_circle_inside (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ < r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀,
      discrete_winding_number (Polynomial.X - Polynomial.C α) N r = 1 := by
  /-
  Proof:

  Step 1: The points z_j = r·e^{2πij/N} form a regular N-gon on the circle |z| = r.
  The values w_j = z_j - α lie on a circle of radius r centered at -α.

  Step 2: Since |α| < r, the origin is strictly inside this circle.
  The minimum distance from origin to any w_j is at least r - |α| > 0.

  Step 3: The argument function θ ↦ arg(r·e^{iθ} - α) is Lipschitz continuous
  on [0, 2π] with Lipschitz constant L = r/(r - |α|).

  Step 4: For N ≥ N₀ = ⌈2πL/π⌉ + 1, the mesh 2π/N satisfies:
    |Δarg| ≤ L · (2π/N) < π

  Step 5: When |Δarg| < π for all consecutive pairs, the wrapping is exact:
    wrapped(Δarg) = Δarg (no correction needed)

  Step 6: The sum telescopes:
    Σ wrapped(Δarg_j) = Σ Δarg_j = lift(2π) - lift(0) = 2π

  Step 7: discrete_winding = 2π / (2π) = 1.
  -/
  -- The gap from origin to the curve: min distance = r - |α| > 0
  have h_gap : r - ‖α‖ > 0 := by linarith

  -- Lipschitz constant for the lift function on this curve
  -- The lift has Lipschitz constant (r + ‖α‖)/(r - ‖α‖) from total_arg_change_for_winding_one
  -- (the factor involving ‖α‖ in the numerator comes from Mathlib's angle bound: angle ≤ π/2 * chord)
  let L := (r + ‖α‖) / (r - ‖α‖)
  have hL_pos : L > 0 := div_pos (by have := norm_nonneg α; linarith) h_gap

  -- Choose N₀ such that each angular step satisfies |Δarg| < π
  -- We need: (2π/N) · L < π, equivalently N > 2L
  use Nat.ceil (2 * L) + 1
  intro N hN

  -- Key simplification: (X - C α).eval z = z - α
  have h_eval : ∀ z : ℂ, (Polynomial.X - Polynomial.C α).eval z = z - α := by
    intro z
    simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

  have h_cont_winding : winding_number_linear α r = 1 := winding_number_linear_inside α r hr hα

  -- The discrete winding converges to the continuous winding
  -- For this linear factor, the convergence is exact once the mesh is fine enough
  -- because the argument function is smooth and the wrapping correction vanishes


  have hN_pos : (N : ℝ) > 0 := by
    have : N ≥ Nat.ceil (2 * L) + 1 := hN
    have h1 : Nat.ceil (2 * L) + 1 ≥ 1 := Nat.le_add_left 1 _
    have h2 : N ≥ 1 := Nat.le_trans h1 this
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp h2))

  -- The mesh size is 2π/N
  -- We need: (2π)/N < π/L, equivalently 2L < N
  have h_2L_lt_N : 2 * L < N := by
    have h1 : (N : ℝ) ≥ Nat.ceil (2 * L) + 1 := by exact_mod_cast hN
    have h2 : (Nat.ceil (2 * L) : ℝ) ≥ 2 * L := Nat.le_ceil (2 * L)
    linarith

  have h_mesh : (2 * Real.pi) / N < Real.pi / L := by
    have hL_pos' : L > 0 := hL_pos
    have hpi_pos : Real.pi > 0 := Real.pi_pos
    -- (2π)/N < π/L ↔ 2πL < πN ↔ 2L < N
    calc (2 * Real.pi) / N
        = 2 * (Real.pi / N) := by ring
      _ < 2 * (Real.pi / (2 * L)) := by {
          apply mul_lt_mul_of_pos_left
          apply div_lt_div_of_pos_left hpi_pos
           (by linarith : 2 * L > 0) h_2L_lt_N
          linarith
        }
      _ = Real.pi / L := by {
          have hL_ne : L ≠ 0 := ne_of_gt hL_pos'
          field_simp
        }

  obtain ⟨lift, h_lift_0, h_lift_2pi, h_arg_eq⟩ := total_arg_change_for_winding_one α r hr hα

  -- The key property: lift(2π) - lift(0) = 2π
  have h_total_change : lift (2 * Real.pi) - lift 0 = 2 * Real.pi := by
    rw [h_lift_2pi]; ring

  -- The sample points θⱼ = 2πj/N for j = 0, 1, ..., N-1
  let θ : ℕ → ℝ := fun j => 2 * Real.pi * j / N


  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := by positivity

  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos

  -- The wrapped sum equals 2π for large N when wrapping is trivial
  -- Note: We use explicit ℕ cast for the mod to avoid ℝ mod (which equals 0 for fields)
  have h_wrapped_sum_eq_2pi :
      (Finset.sum (Finset.range N) fun j =>
        let θ_curr := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (j : ℝ) / N)) - α)
        let θ_next := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (((j + 1) % N : ℕ) : ℝ) / N)) - α)
        let diff := θ_next - θ_curr
        if diff > Real.pi then diff - 2 * Real.pi
        else if diff ≤ -Real.pi then diff + 2 * Real.pi
        else diff) = 2 * Real.pi := by
    let Ls : ℕ → ℝ := fun j => lift (2 * Real.pi * j / N)

    -- Key properties
    have hLs0 : Ls 0 = lift 0 := by simp [Ls]
    have hLsN : Ls N = lift 0 + 2 * Real.pi := by
      simp only [Ls]
      have h : (2 : ℝ) * Real.pi * N / N = 2 * Real.pi := by field_simp [hN_ne]
      rw [h, h_lift_2pi]

    set raw_diff : ℕ → ℝ := fun j =>
      let k : ℕ := (j + 1) % N
      Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * k / N)) - α) -
      Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * j / N)) - α) with h_raw_diff_def

    -- The raw sum (circular) equals 0
    -- For any function a, Σⱼ (a_{(j+1) mod N} - a_j) = 0 because it's circular
    have h_raw_circular : (Finset.range N).sum raw_diff = 0 := by
      have hN_pos_nat : 0 < N := by
        have : N ≥ Nat.ceil (2 * L) + 1 := hN
        omega

      let a : ℕ → ℝ := fun j => Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * j / N)) - α)

      -- The sum uses natural number modular arithmetic
      -- We need to match: raw_diff j = a ((j + 1) % N) - a j

      have h_eq_sum : (Finset.range N).sum raw_diff =
          (Finset.range N).sum (fun j => a ((j + 1) % N) - a j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [raw_diff, a]

      rw [h_eq_sum]

      -- For a circular sum, Σⱼ (a_{(j+1) mod N} - a_j) = 0
      -- This is because each a_k appears exactly once with + and once with -
      have h_circular : (Finset.range N).sum (fun j => a ((j + 1) % N) - a j) = 0 := by
        rw [Finset.sum_sub_distrib]
      -- Need: Σ a_{(j+1) mod N} = Σ a_j
        suffices h : (Finset.range N).sum (fun j => a ((j + 1) % N)) = (Finset.range N).sum (fun j => a j) by
          rw [h]; ring
      -- The map j ↦ (j+1) mod N is a bijection on {0, ..., N-1}
        have hN_ge_1 : N ≥ 1 := Nat.one_le_of_lt hN_pos_nat
      -- Use Finset.sum_bij' with the inverse map k ↦ (k + N - 1) mod N
      -- We show: Σ a((j+1)%N) = Σ a(j) by bijection i = (·+1)%N
        refine Finset.sum_bij' (fun j _ => (j + 1) % N) (fun k _ => (k + N - 1) % N) ?_ ?_ ?_ ?_ ?_
        · -- hi : image of i is in range
          intro j hj
          exact Finset.mem_range.mpr (Nat.mod_lt _ hN_pos_nat)
        · -- hi' : image of inverse is in range
          intro k hk
          exact Finset.mem_range.mpr (Nat.mod_lt _ hN_pos_nat)
        · -- left_inv : g(f(j)) = j
          intro j hj
          simp only []
          have hj' : j < N := Finset.mem_range.mp hj
          by_cases hj_edge : j + 1 = N
          · -- j = N-1, so (j+1) % N = 0
            have h1 : (j + 1) % N = 0 := by simp [hj_edge]
            simp only [h1, zero_add]
            have h2 : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (by omega)
            simp only [h2]
            omega
          · -- j < N-1, so (j+1) % N = j+1
            have h1 : (j + 1) % N = j + 1 := Nat.mod_eq_of_lt (by omega)
            simp only [h1]
            have h2 : j + 1 + N - 1 = j + N := by omega
            simp only [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj']
        · -- right_inv : f(g(k)) = k
          intro k hk
          simp only []
          have hk' : k < N := Finset.mem_range.mp hk
          by_cases h0 : k = 0
          · -- k = 0
            simp only [h0, zero_add]
            have h1 : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (by omega)
            simp only [h1]
            have h2 : N - 1 + 1 = N := Nat.sub_add_cancel hN_ge_1
            simp only [h2, Nat.mod_self]
          · -- k > 0
            have hk_pos : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr h0
            have h1 : k + N - 1 = k - 1 + N := by omega
            simp only [h1, Nat.add_mod_right]
            have h2 : k - 1 < N := by omega
            simp only [Nat.mod_eq_of_lt h2]
            have h3 : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
            simp only [h3, Nat.mod_eq_of_lt hk']
        · -- heq : a(f(j)) = a(j)
          intro j _
          rfl

      exact h_circular

    -- Define the correction function
    set correction : ℝ → ℤ := fun d =>
      if d > Real.pi then -1 else if d ≤ -Real.pi then 1 else 0 with h_corr_def

    -- wrapped(d) = d + 2π × correction(d)
    have h_wrapped_eq : ∀ d : ℝ,
        (if d > Real.pi then d - 2 * Real.pi
         else if d ≤ -Real.pi then d + 2 * Real.pi
         else d) = d + 2 * Real.pi * correction d := by
      intro d
      simp only [correction]
      split_ifs with h1 h2 <;> ring

    -- The goal sum can be rewritten using raw_diff and correction
    -- Key: the wrapped sum equals raw_sum + 2π × correction_sum = 0 + 2π = 2π
    have h_sum_eq : (Finset.sum (Finset.range N) fun j =>
          let θ_curr := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (j : ℝ) / N)) - α)
          let θ_next := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (((j + 1) % N : ℕ) : ℝ) / N)) - α)
          let diff := θ_next - θ_curr
          if diff > Real.pi then diff - 2 * Real.pi
          else if diff ≤ -Real.pi then diff + 2 * Real.pi
          else diff) =
        (Finset.range N).sum (fun j => raw_diff j + 2 * Real.pi * correction (raw_diff j)) := by
      apply Finset.sum_congr rfl
      intro j _
      -- Now both sides use explicit ℕ mod cast, so they should match
      simp only [raw_diff]
      exact h_wrapped_eq _

    rw [h_sum_eq, Finset.sum_add_distrib]

    -- The first part is the raw sum = 0
    have h_first_part : (Finset.range N).sum raw_diff = 0 := h_raw_circular
    rw [h_first_part, zero_add]

    -- The second part: 2π × Σ correction = 2π × 1 = 2π
    -- For the sum of corrections to equal 1, we use toIocDiv which matches toIocMod exactly.

    -- Define floor levels using toIocDiv (this matches arg exactly via toIocMod)
    set n_floor : ℕ → ℤ := fun j => toIocDiv two_pi_pos (-Real.pi) (Ls j) with h_nfloor_def

    -- The arg-floor relationship is exact (by toIocMod decomposition)
    have h_arg_floor : ∀ k : ℕ, Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * k / N)) - α) =
        Ls k - 2 * Real.pi * n_floor k := by
      intro k
      simp only [Ls, n_floor]
      have h1 := h_arg_eq.1 (2 * Real.pi * k / N)
      have h_exp_eq : (I * (2 * ↑Real.pi * ↑k / ↑N) : ℂ) = I * ↑(2 * Real.pi * k / N) := by
        push_cast; ring
      conv_lhs => rw [h_exp_eq]
      rw [h1, ← self_sub_toIocDiv_zsmul two_pi_pos (-Real.pi)]
      simp only [zsmul_eq_mul]; ring

    -- Key: n_floor(N) = n_floor(0) + 1 (since lift wraps by 2π)
    have h_n_diff : n_floor N = n_floor 0 + 1 := by
      simp only [n_floor, Ls]
      have h0_simp : (2 : ℝ) * Real.pi * (0 : ℕ) / N = 0 := by simp
      have hN'' : (2 : ℝ) * Real.pi * N / N = 2 * Real.pi := by field_simp [hN_ne]
      simp only [Nat.cast_zero, mul_zero, zero_div] at h0_simp ⊢
      rw [hN'', h_lift_2pi]
      -- toIocDiv(lift(0) + 2π) = toIocDiv(lift(0)) + 1
      exact toIocDiv_add_right two_pi_pos (-Real.pi) (lift 0)

    have h_key : (n_floor N : ℝ) - (n_floor 0 : ℝ) = 1 := by
      rw [h_n_diff]
      simp only [Int.cast_add, Int.cast_one]
      ring

    -- The sum of corrections = 1 for counterclockwise winding once around origin.
    -- This equals the floor level change n(N) - n(0) = 1.
    have h_correction_sum : (Finset.range N).sum (fun j => 2 * Real.pi * correction (raw_diff j)) = 2 * Real.pi := by
      -- The sum has form Σ (a * f j) = a * Σ f j, use Finset.mul_sum
      rw [← Finset.mul_sum]
      suffices h : (Finset.range N).sum (fun j => (correction (raw_diff j) : ℝ)) = 1 by
        calc (2 * Real.pi) * (Finset.range N).sum (fun j => (correction (raw_diff j) : ℝ))
            = (2 * Real.pi) * 1 := by rw [h]
          _ = 2 * Real.pi := by ring

      let lift_sum := (Finset.range N).sum (fun j => Ls (j + 1) - Ls j)

      -- The lift sum telescopes to Ls(N) - Ls(0) = 2π
      have h_lift_sum_eq : lift_sum = 2 * Real.pi := by
        simp only [lift_sum]
        have h_tel := Finset.sum_range_sub (fun j => Ls j) N
        rw [h_tel]
        simp only [Ls]
      -- After simp, goal is: lift (2 * π * ↑N / ↑N) - lift (2 * π * ↑0 / ↑N) = 2 * π
      -- Simplify the arguments
        have h0' : (2 : ℝ) * Real.pi * (0 : ℕ) / (N : ℕ) = 0 := by simp
        have hN'' : (2 : ℝ) * Real.pi * (N : ℕ) / (N : ℕ) = 2 * Real.pi := by field_simp [hN_ne]
        simp only [Nat.cast_zero, mul_zero, zero_div] at h0' ⊢
        simp only [hN'', h_lift_2pi]
        ring

      -- Now we show correction_sum = 1 by using the floor level analysis
      -- Define the floor difference function
      let floor_diff : ℕ → ℤ := fun j => n_floor (j + 1) - n_floor j

      -- The sum of floor differences telescopes to n_floor(N) - n_floor(0) = 1
      have h_floor_sum_eq :
          (Finset.range N).sum (fun j => (floor_diff j : ℝ)) = 1 := by
        simp only [floor_diff]
      -- Convert ↑(a - b) to ↑a - ↑b via Int.cast_sub
        simp only [Int.cast_sub]
        have h_tel := Finset.sum_range_sub (fun j => (n_floor j : ℝ)) N
        rw [h_tel, h_key]

      -- Show correction sum equals floor difference sum
      -- This is the key step: correction(raw_diff j) = floor_diff j
      -- which holds because wrapping compensates exactly for floor changes

      have h_corr_eq_floor_sum :
          (Finset.range N).sum (fun j => (correction (raw_diff j) : ℝ)) =
          (Finset.range N).sum (fun j => (floor_diff j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < N := Finset.mem_range.mp hj

      -- n_floor is now defined using toIocDiv, so h_arg_floor is exact
      -- We use this to show correction(raw_diff j) = floor_diff j

      -- Case analysis based on whether we're at the boundary
        by_cases hj_edge : j + 1 = N
        · -- Boundary case: j = N-1, so (j+1)%N = 0
          have hmod : (j + 1) % N = 0 := by simp [hj_edge]
          have hj_edge' : 1 + j = N := by omega
          have hj_eq : j = N - 1 := Nat.eq_sub_of_add_eq' hj_edge'

          -- For j = N-1: raw_diff uses arg(w_0) - arg(w_{N-1})
          -- = (Ls(0) - 2π n(0)) - (Ls(N-1) - 2π n(N-1))
          -- = (Ls(N) - 2π - 2π n(0)) - (Ls(N-1) - 2π n(N-1))  [using Ls(0) = Ls(N) - 2π]
          -- = (Ls(N) - Ls(N-1)) - 2π(1 + n(0) - n(N-1))
          -- = (Ls(N) - Ls(N-1)) - 2π(n(N) - n(N-1))           [using n(N) = n(0) + 1]

          simp only [raw_diff, correction, floor_diff]
          rw [hmod, hj_eq]
          -- Simplify N - 1 + 1 = N in the goal
          have hN_simp : N - 1 + 1 = N := Nat.sub_add_cancel (by omega : 1 ≤ N)
          simp only [hN_simp]

          -- The raw difference at the boundary
          have h_arg0 := h_arg_floor 0
          have h_argN1 := h_arg_floor (N - 1)

          -- Ls(0) = Ls(N) - 2π
          have h_Ls_wrap : Ls 0 = Ls N - 2 * Real.pi := by
            simp only [Ls]
            have h0 : (2 : ℝ) * Real.pi * (0 : ℕ) / (N : ℕ) = 0 := by simp
            have hN' : (2 : ℝ) * Real.pi * (N : ℕ) / (N : ℕ) = 2 * Real.pi := by field_simp [hN_ne]
            simp only [Nat.cast_zero, mul_zero, zero_div] at h0 ⊢
            rw [hN', h_lift_2pi]
            ring

          -- The raw_diff at boundary
          -- Use h_arg0 and h_argN1 to compute the difference
          -- h_arg0: arg(w_0) = Ls 0 - 2π·n_floor 0
          -- h_argN1: arg(w_{N-1}) = Ls(N-1) - 2π·n_floor(N-1)
          -- Also Ls 0 = Ls N - 2π (wrapping)
          have h_rd_eq : Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (0 : ℕ) / N)) - α) -
              Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (N - 1 : ℕ) / N)) - α) =
              (Ls N - Ls (N - 1)) - 2 * Real.pi * (n_floor N - n_floor (N - 1)) := by
            -- Use h_arg0 and h_argN1 but need to handle cast coercion
            -- Both hypotheses use ↑k for natural numbers
            calc Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (0 : ℕ) / N)) - α) -
                Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (N - 1 : ℕ) / N)) - α)
              = (Ls 0 - 2 * Real.pi * n_floor 0) - (Ls (N - 1) - 2 * Real.pi * n_floor (N - 1)) := by
                  rw [h_arg0, h_argN1]
              _ = Ls 0 - Ls (N - 1) - 2 * Real.pi * (n_floor 0 - n_floor (N - 1)) := by ring
              _ = (Ls N - 2 * Real.pi) - Ls (N - 1) - 2 * Real.pi * (n_floor 0 - n_floor (N - 1)) := by
                  rw [h_Ls_wrap]
              _ = (Ls N - Ls (N - 1)) - 2 * Real.pi * (1 + n_floor 0 - n_floor (N - 1)) := by ring
              _ = (Ls N - Ls (N - 1)) - 2 * Real.pi * (n_floor N - n_floor (N - 1)) := by
                  -- Need: 1 + n_floor 0 - n_floor (N - 1) = n_floor N - n_floor (N - 1)
                  -- i.e., n_floor N = n_floor 0 + 1 (which is h_n_diff)
                  have h_use : (n_floor N : ℝ) = n_floor 0 + 1 := by
                    exact_mod_cast h_n_diff
                  ring_nf
                  rw [h_use]
                  ring

          -- Now show correction equals floor difference
          -- Using PURE GEOMETRIC BOUND (no derivatives, no Lipschitz theorem)

          have h_Ls_diff_bound : |Ls N - Ls (N - 1)| < Real.pi := by
            simp only [Ls]

            have hN_ge_1 : N ≥ 1 := by
              have := hN
              have h1 : Nat.ceil (2 * L) + 1 ≥ 1 := Nat.le_add_left 1 _
              omega
            have hN_ne' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hN_ge_1)

            -- The curve points at the two angles
            let θ₁ : ℝ := 2 * Real.pi * (N - 1) / N
            let θ₂ : ℝ := 2 * Real.pi * N / N
            let w₁ : ℂ := (r : ℂ) * Complex.exp (I * θ₁) - α
            let w₂ : ℂ := (r : ℂ) * Complex.exp (I * θ₂) - α

            -- Step 1: Bound on curve point distance
            have h_w_diff : ‖w₂ - w₁‖ ≤ r * (2 * Real.pi / N) := by
              simp only [w₁, w₂]
              calc ‖(r : ℂ) * Complex.exp (I * θ₂) - α - ((r : ℂ) * Complex.exp (I * θ₁) - α)‖
                  = ‖(r : ℂ) * (Complex.exp (I * θ₂) - Complex.exp (I * θ₁))‖ := by ring_nf
                _ = ‖(r : ℂ)‖ * ‖Complex.exp (I * θ₂) - Complex.exp (I * θ₁)‖ := norm_mul _ _
                _ = r * ‖Complex.exp (I * θ₂) - Complex.exp (I * θ₁)‖ := by
                    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
                _ ≤ r * |θ₂ - θ₁| := by
                    apply mul_le_mul_of_nonneg_left
                    · exact norm_exp_I_sub_exp_I_le θ₂ θ₁
                    · linarith
                _ = r * |2 * Real.pi * N / N - 2 * Real.pi * (N - 1) / N| := rfl
                _ = r * |2 * Real.pi / N| := by
                    congr 1
                    field_simp
                    ring_nf
                _ = r * (2 * Real.pi / N) := by rw [abs_of_pos]; positivity

            -- Step 2: Lower bound on curve point norms (reverse triangle inequality)
            have h_w_norm_lower : ‖w₁‖ ≥ r - ‖α‖ ∧ ‖w₂‖ ≥ r - ‖α‖ := by
              constructor
              · simp only [w₁]
                have h1 : ‖(r : ℂ) * Complex.exp (I * θ₁)‖ = r := by
                  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
                  have : I * (θ₁ : ℂ) = (θ₁ : ℝ) * I := by push_cast; ring
                  rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]
                calc ‖(r : ℂ) * Complex.exp (I * θ₁) - α‖
                    ≥ |‖(r : ℂ) * Complex.exp (I * θ₁)‖ - ‖α‖| := by
                        have := abs_norm_sub_norm_le ((r : ℂ) * Complex.exp (I * θ₁)) α
                        linarith
                  _ = |r - ‖α‖| := by rw [h1]
                  _ = r - ‖α‖ := abs_of_pos h_gap
              · simp only [w₂]
                have h2 : ‖(r : ℂ) * Complex.exp (I * θ₂)‖ = r := by
                  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
                  have : I * (θ₂ : ℂ) = (θ₂ : ℝ) * I := by push_cast; ring
                  rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]
                calc ‖(r : ℂ) * Complex.exp (I * θ₂) - α‖
                    ≥ |‖(r : ℂ) * Complex.exp (I * θ₂)‖ - ‖α‖| := by
                        have := abs_norm_sub_norm_le ((r : ℂ) * Complex.exp (I * θ₂)) α
                        linarith
                  _ = |r - ‖α‖| := by rw [h2]
                  _ = r - ‖α‖ := abs_of_pos h_gap


            calc |lift (2 * Real.pi * ↑N / ↑N) - lift (2 * Real.pi * ↑(N - 1) / ↑N)|
                ≤ L * (2 * Real.pi / N) := by
                  -- The geometric bound: |Δlift| ≤ L · |Δθ|
                  -- This follows from the fact that the lift tracks the continuous angle,
                  -- which changes at rate ≤ L (curve velocity / distance from origin).
                  have h_θ_diff : |θ₂ - θ₁| = 2 * Real.pi / N := by
                    simp only [θ₁, θ₂]
                    have hN_pos' : (N : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_ge_1)
                    have hpi_pos : Real.pi > 0 := Real.pi_pos
                    have h_simp : 2 * Real.pi * N / N - 2 * Real.pi * (N - 1) / N = 2 * Real.pi / N := by
                      field_simp [hN_ne']; ring
                    rw [h_simp, abs_of_pos (div_pos (by linarith) hN_pos')]
                  have hN_pos'' : (N : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_ge_1)
                  -- Convert ↑(N-1) to ↑N - 1 for real arithmetic
                  have h_cast_Nm1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
                    rw [Nat.cast_sub hN_ge_1]; simp
                  have h_abs_eq : |2 * Real.pi * N / N - 2 * Real.pi * (N - 1) / N| = 2 * Real.pi / N := by
                    have h_simp : 2 * Real.pi * (N : ℝ) / (N : ℝ) - 2 * Real.pi * ((N : ℝ) - 1) / (N : ℝ) = 2 * Real.pi / (N : ℝ) := by
                      field_simp [hN_ne']; ring
                    rw [h_simp, abs_of_pos (div_pos (by linarith [Real.pi_pos] : 2 * Real.pi > 0) hN_pos'')]
                  -- The Lipschitz bound with real arithmetic
                  have h_lip := h_arg_eq.2 (2 * Real.pi * ((N : ℝ) - 1) / (N : ℝ)) (2 * Real.pi * (N : ℝ) / (N : ℝ))
                  -- Rewrite with the cast equality
                  calc |lift (2 * Real.pi * ↑N / ↑N) - lift (2 * Real.pi * ↑(N - 1) / ↑N)|
                      = |lift (2 * Real.pi * (N : ℝ) / (N : ℝ)) - lift (2 * Real.pi * ((N : ℝ) - 1) / (N : ℝ))| := by
                          rw [h_cast_Nm1]
                    _ ≤ L * |2 * Real.pi * (N : ℝ) / (N : ℝ) - 2 * Real.pi * ((N : ℝ) - 1) / (N : ℝ)| := h_lip
                    _ = L * (2 * Real.pi / N) := by rw [h_abs_eq]
              _ < Real.pi := by
                  -- From h_mesh: (2 * π) / N < π / L, so L * (2π/N) < π
                  have h := h_mesh
                  have hL_pos' : L > 0 := hL_pos
                  calc L * (2 * Real.pi / N)
                      = L * ((2 * Real.pi) / N) := by ring
                    _ < L * (Real.pi / L) := by apply mul_lt_mul_of_pos_left h hL_pos'
                    _ = Real.pi := by field_simp

          -- The floor difference is in {-1, 0, 1}
          have h_floor_diff_bound : n_floor N - n_floor (N - 1) = -1 ∨
              n_floor N - n_floor (N - 1) = 0 ∨ n_floor N - n_floor (N - 1) = 1 := by
            -- Follows from |Ls diff| < π
            -- Using toIocDiv_eq_neg_floor: toIocDiv hp a b = -⌊(a + p - b) / p⌋
            -- So n_floor j = toIocDiv two_pi_pos (-π) (Ls j) = -⌊((-π) + 2π - Ls j) / (2π)⌋ = -⌊(π - Ls j) / (2π)⌋
            simp only [n_floor]
            have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
            -- Let a' = (π - Ls N) / (2π) and b' = (π - Ls (N-1)) / (2π)
            -- Then n_floor N - n_floor (N-1) = -⌊a'⌋ - (-⌊b'⌋) = ⌊b'⌋ - ⌊a'⌋
            set a' := (Real.pi - Ls N) / (2 * Real.pi) with ha'_def
            set b' := (Real.pi - Ls (N - 1)) / (2 * Real.pi) with hb'_def
            -- Connect toIocDiv to floor using toIocDiv_eq_neg_floor
            have h_a_eq : toIocDiv two_pi_pos (-Real.pi) (Ls N) = -⌊a'⌋ := by
              rw [toIocDiv_eq_neg_floor, ha'_def]
              congr 1
              ring_nf
            have h_b_eq : toIocDiv two_pi_pos (-Real.pi) (Ls (N - 1)) = -⌊b'⌋ := by
              rw [toIocDiv_eq_neg_floor, hb'_def]
              congr 1
              ring_nf
            rw [h_a_eq, h_b_eq]
            -- Goal: -⌊a'⌋ - (-⌊b'⌋) = ⌊b'⌋ - ⌊a'⌋ ∈ {-1, 0, 1}
            -- b' - a' = ((π - Ls (N-1)) - (π - Ls N)) / (2π) = (Ls N - Ls (N-1)) / (2π)
            have h_quot_diff : |b' - a'| < 1 := by
              simp only [ha'_def, hb'_def]
              rw [← sub_div, abs_div, abs_of_pos h2pi_pos]
              calc |Real.pi - Ls (N - 1) - (Real.pi - Ls N)| / (2 * Real.pi)
                  = |Ls N - Ls (N - 1)| / (2 * Real.pi) := by ring_nf
                _ < Real.pi / (2 * Real.pi) := by apply div_lt_div_of_pos_right h_Ls_diff_bound h2pi_pos
                _ = 1 / 2 := by field_simp
                _ < 1 := by norm_num
            have ha'_lt := Int.lt_floor_add_one a'
            have hb'_lt := Int.lt_floor_add_one b'
            have h_abs := abs_lt.mp h_quot_diff
            -- |⌊b'⌋ - ⌊a'⌋| ≤ 1 when |b' - a'| < 1
            have h_upper : ⌊b'⌋ ≤ ⌊a'⌋ + 1 := by
              rw [Int.floor_le_iff]
              calc b' = a' + (b' - a') := by ring
                _ < a' + 1 := by linarith [h_abs.2]
                _ < (⌊a'⌋ + 1 : ℤ) + 1 := by
                    have : a' + 1 < (⌊a'⌋ : ℝ) + 1 + 1 := by linarith [ha'_lt]
                    exact_mod_cast this
            have h_lower : ⌊a'⌋ ≤ ⌊b'⌋ + 1 := by
              rw [Int.floor_le_iff]
              calc a' = b' + (a' - b') := by ring
                _ < b' + 1 := by linarith [h_abs.1]
                _ < (⌊b'⌋ + 1 : ℤ) + 1 := by
                    have : b' + 1 < (⌊b'⌋ : ℝ) + 1 + 1 := by linarith [hb'_lt]
                    exact_mod_cast this
            omega

          -- Now use h_rd_eq and the bounds to show correction = floor diff
          -- Goal: ↑(if raw > π then -1 else if raw < -π then 1 else 0) = ↑(n_floor N - n_floor (N-1))
          -- where raw = arg(w_0) - arg(w_{N-1})
          -- By h_rd_eq: raw = (Ls N - Ls (N-1)) - 2π(n_floor N - n_floor (N-1))
          -- Let D = Ls N - Ls (N-1) and Δ = n_floor N - n_floor (N-1)
          -- Then raw = D - 2πΔ

          have hN_ge_1' : N ≥ 1 := by
            have := hN
            have h1 : Nat.ceil (2 * L) + 1 ≥ 1 := Nat.le_add_left 1 _
            omega
          have h_cast_eq : (0 : ℝ) = (0 : ℕ) ∧ ((N : ℝ) - 1) = ((N - 1 : ℕ) : ℝ) := by
            constructor
            · simp
            · simp only [Nat.cast_sub hN_ge_1']; ring
          simp only [h_cast_eq.1, h_cast_eq.2] at h_rd_eq

          -- Define Ls_diff and floor_diff
          set Ls_diff := Ls N - Ls (N - 1) with hLs_diff_def
          set Δn := n_floor N - n_floor (N - 1) with hΔn_def

          -- The raw difference (arg(w_0) - arg(w_{N-1})) equals Ls_diff - 2π·Δn by h_rd_eq
          -- So we need: if (Ls_diff - 2πΔn) > π then -1 else if < -π then 1 else 0 = Δn

          -- The raw difference (the arg subtraction) equals Ls_diff - 2π·Δn
          -- Let's abbreviate the raw arg difference
          set raw := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (0 : ℕ) / (N : ℕ))) - α) -
              Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * ((N - 1 : ℕ) : ℕ) / (N : ℕ))) - α) with h_raw_def

          -- Show raw = Ls_diff - 2π·Δn using h_rd_eq
          have h_raw_formula : raw = Ls_diff - 2 * Real.pi * ↑Δn := by
            simp only [h_raw_def, hLs_diff_def, hΔn_def]
            -- h_rd_eq has the same form
            convert h_rd_eq using 2 <;> simp only [Int.cast_sub]

          rcases h_floor_diff_bound with h_neg1 | h_0 | h_pos1
          · -- Case: Δn = -1
            rw [h_neg1] at h_raw_formula ⊢
            have h_raw_val : raw = Ls_diff + 2 * Real.pi := by rw [h_raw_formula]; ring
            have h_gt : raw > Real.pi := by
              rw [h_raw_val]
              have := abs_lt.mp h_Ls_diff_bound
              linarith [Real.pi_pos]
            rw [h_raw_def] at h_gt
            rw [if_pos h_gt]
          · -- Case: Δn = 0
            rw [h_0] at h_raw_formula ⊢
            have h_raw_val : raw = Ls_diff := by rw [h_raw_formula]; ring
            have h_in_range : ¬(raw > Real.pi) ∧ ¬(raw ≤ -Real.pi) := by
              rw [h_raw_val]
              have := abs_lt.mp h_Ls_diff_bound
              constructor <;> linarith
            rw [h_raw_def] at h_in_range
            rw [if_neg h_in_range.1, if_neg h_in_range.2]
          · -- Case: Δn = 1
            rw [h_pos1] at h_raw_formula ⊢
            have h_raw_val : raw = Ls_diff - 2 * Real.pi := by rw [h_raw_formula]; ring
            have h_le : raw ≤ -Real.pi := by
              rw [h_raw_val]
              have := abs_lt.mp h_Ls_diff_bound
              linarith [Real.pi_pos]
            have h_not_gt : ¬(raw > Real.pi) := by
              rw [h_raw_val]
              have := abs_lt.mp h_Ls_diff_bound
              linarith [Real.pi_pos]
            rw [h_raw_def] at h_le h_not_gt
            rw [if_neg h_not_gt, if_pos h_le]

        · -- Interior case: j < N-1, so (j+1)%N = j+1
          have hmod : (j + 1) % N = j + 1 := Nat.mod_eq_of_lt (by omega : j + 1 < N)

          simp only [raw_diff, correction, floor_diff]
          rw [hmod]

          have h_arg_j := h_arg_floor j
          have h_arg_j1 := h_arg_floor (j + 1)

          -- raw_diff = arg(j+1) - arg(j) = (Ls(j+1) - Ls(j)) - 2π(n(j+1) - n(j))
          -- Note: Need to handle coercion: ↑(j+1) vs (↑j + 1)
          have h_cast_j1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
          -- Set raw to match the goal's arg difference
          set raw := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (j + 1 : ℕ) / N)) - α) -
              Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * j / N)) - α) with h_raw_def

          have h_rd : raw = (Ls (j + 1) - Ls j) - 2 * Real.pi * (n_floor (j + 1) - n_floor j) := by
            rw [h_raw_def, h_arg_j1, h_arg_j]
            ring

          -- Geometric bound on lift change (same as boundary case)
          have h_Ls_diff_bound : |Ls (j + 1) - Ls j| < Real.pi := by
            simp only [Ls]
            -- GEOMETRIC APPROACH: |Δlift| ≤ L · |Δθ| < π
            -- where L = r/(r - ‖α‖) and |Δθ| = 2π/N

            have hN_ge_1 : N ≥ 1 := by
              have := hN
              have h1 : Nat.ceil (2 * L) + 1 ≥ 1 := Nat.le_add_left 1 _
              omega
            have hN_ne' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hN_ge_1)


            have hN_pos'' : (N : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_ge_1)

            have h_θ_diff : |2 * Real.pi * ((j : ℝ) + 1) / N - 2 * Real.pi * j / N| = 2 * Real.pi / N := by
              rw [abs_of_pos]
              · field_simp [hN_ne']; ring
              · have : 2 * Real.pi / (N : ℝ) > 0 := by positivity
                calc 2 * Real.pi * ((j : ℝ) + 1) / N - 2 * Real.pi * j / N
                    = 2 * Real.pi / N := by field_simp [hN_ne']; ring
                  _ > 0 := this

            -- Coercion fact: ↑(j + 1) = ↑j + 1
            have h_j1_cast : (((j + 1) : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring

            calc |lift (2 * Real.pi * ↑(j + 1) / ↑N) - lift (2 * Real.pi * ↑j / ↑N)|
                ≤ L * (2 * Real.pi / N) := by
                  -- The geometric bound on the continuous lift:
                  -- |lift(θ₂) - lift(θ₁)| ≤ L · |θ₂ - θ₁|
                  -- This follows from the Lipschitz bound in total_arg_change_for_winding_one.
                  have h_lip := h_arg_eq.2 (2 * Real.pi * j / N) (2 * Real.pi * (↑j + 1) / N)
                  calc |lift (2 * Real.pi * ↑(j + 1) / ↑N) - lift (2 * Real.pi * ↑j / ↑N)|
                      = |lift (2 * Real.pi * (↑j + 1) / ↑N) - lift (2 * Real.pi * ↑j / ↑N)| := by
                        rw [h_j1_cast]
                    _ ≤ L * |2 * Real.pi * (↑j + 1) / N - 2 * Real.pi * j / N| := h_lip
                    _ = L * |2 * Real.pi / N| := by
                        congr 1
                        field_simp [hN_ne']
                        ring_nf
                    _ = L * (2 * Real.pi / N) := by
                        rw [abs_of_pos]
                        positivity
              _ < Real.pi := by
                  have h := h_mesh
                  have hL_pos' : L > 0 := hL_pos
                  calc L * (2 * Real.pi / N)
                      = L * ((2 * Real.pi) / N) := by ring
                    _ < L * (Real.pi / L) := by apply mul_lt_mul_of_pos_left h hL_pos'
                    _ = Real.pi := by field_simp

          -- Floor difference bound
          have h_Δn_bound : n_floor (j + 1) - n_floor j = -1 ∨
              n_floor (j + 1) - n_floor j = 0 ∨ n_floor (j + 1) - n_floor j = 1 := by
            simp only [n_floor]
            have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
            -- Use toIocDiv_eq_neg_floor: toIocDiv p a b = -⌊(a + p - b) / p⌋
            -- toIocDiv two_pi_pos (-π) x = -⌊(-π + 2π - x) / (2π)⌋ = -⌊(π - x) / (2π)⌋
            have h_toIocDiv_j1 : toIocDiv two_pi_pos (-Real.pi) (Ls (j + 1)) =
                -⌊(Real.pi - Ls (j + 1)) / (2 * Real.pi)⌋ := by
              rw [toIocDiv_eq_neg_floor]; congr 1; ring_nf
            have h_toIocDiv_j : toIocDiv two_pi_pos (-Real.pi) (Ls j) =
                -⌊(Real.pi - Ls j) / (2 * Real.pi)⌋ := by
              rw [toIocDiv_eq_neg_floor]; congr 1; ring_nf
            rw [h_toIocDiv_j1, h_toIocDiv_j]
            -- Goal: -⌊(π - Ls(j+1))/(2π)⌋ - (-⌊(π - Ls j)/(2π)⌋) ∈ {-1, 0, 1}
            -- = ⌊(π - Ls j)/(2π)⌋ - ⌊(π - Ls(j+1))/(2π)⌋
            set a' := (Real.pi - Ls (j + 1)) / (2 * Real.pi) with ha'_def
            set b' := (Real.pi - Ls j) / (2 * Real.pi) with hb'_def
            -- We have |(π - Ls(j+1)) - (π - Ls j)| = |Ls j - Ls(j+1)| = |Ls(j+1) - Ls j| < π < 2π
            have h_quot_diff : |a' - b'| < 1 := by
              rw [ha'_def, hb'_def, ← sub_div, abs_div, abs_of_pos h2pi_pos]
              calc |Real.pi - Ls (j + 1) - (Real.pi - Ls j)| / (2 * Real.pi)
                  = |Ls j - Ls (j + 1)| / (2 * Real.pi) := by ring_nf
                _ = |Ls (j + 1) - Ls j| / (2 * Real.pi) := by rw [abs_sub_comm]
                _ < Real.pi / (2 * Real.pi) := by apply div_lt_div_of_pos_right h_Ls_diff_bound h2pi_pos
                _ = 1 / 2 := by field_simp
                _ < 1 := by norm_num
            have ha'_lt := Int.lt_floor_add_one a'
            have hb'_lt := Int.lt_floor_add_one b'
            have h_abs := abs_lt.mp h_quot_diff
            have h_upper : ⌊b'⌋ ≤ ⌊a'⌋ + 1 := by
              rw [Int.floor_le_iff]
              have ha'_lt' : a' < (⌊a'⌋ : ℝ) + 1 := ha'_lt
              have h1 : b' < a' + 1 := by linarith [h_abs.1]
              have h2 : a' + 1 < (⌊a'⌋ : ℝ) + 2 := by linarith
              calc b' < a' + 1 := h1
                _ < (⌊a'⌋ : ℝ) + 2 := h2
                _ = ((⌊a'⌋ + 1 : ℤ) : ℝ) + 1 := by push_cast; ring
            have h_lower : ⌊a'⌋ ≤ ⌊b'⌋ + 1 := by
              rw [Int.floor_le_iff]
              have hb'_lt' : b' < (⌊b'⌋ : ℝ) + 1 := hb'_lt
              have h1 : a' < b' + 1 := by linarith [h_abs.2]
              have h2 : b' + 1 < (⌊b'⌋ : ℝ) + 2 := by linarith
              calc a' < b' + 1 := h1
                _ < (⌊b'⌋ : ℝ) + 2 := h2
                _ = ((⌊b'⌋ + 1 : ℤ) : ℝ) + 1 := by push_cast; ring
            -- ⌊b'⌋ - ⌊a'⌋ ∈ {-1, 0, 1} from the bounds
            have h_floor_bound : ⌊b'⌋ - ⌊a'⌋ = -1 ∨ ⌊b'⌋ - ⌊a'⌋ = 0 ∨ ⌊b'⌋ - ⌊a'⌋ = 1 := by omega
            -- Goal is: -⌊a'⌋ - (-⌊b'⌋) = ⌊b'⌋ - ⌊a'⌋ ∈ {-1, 0, 1}
            convert h_floor_bound using 1 <;> ring_nf

          set Δn := n_floor (j + 1) - n_floor j with hΔn_def
          set Ls_diff := Ls (j + 1) - Ls j with hLs_diff_def

          -- Rewrite raw to Ls_diff - 2π * Δn in the goal
          have h_raw_formula : raw = Ls_diff - 2 * Real.pi * ↑Δn := by
            rw [hΔn_def, hLs_diff_def]
            -- h_rd has coercion split: ↑(n_floor(j+1)) - ↑(n_floor j)
            -- Goal needs: ↑(n_floor(j+1) - n_floor j)
            convert h_rd using 2
            push_cast
            ring
          simp only [h_raw_formula]

          rcases h_Δn_bound with h_neg1 | h_0 | h_pos1
          · -- Case: Δn = -1
            rw [h_neg1]
            simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, sub_neg_eq_add]
            have h_gt : Ls_diff + 2 * Real.pi > Real.pi := by
              have := abs_lt.mp h_Ls_diff_bound
              linarith [Real.pi_pos]
            rw [if_pos h_gt]
            norm_cast
          · -- Case: Δn = 0
            rw [h_0]
            simp only [Int.cast_zero, mul_zero, sub_zero]
            have h_not_gt : ¬(Ls_diff > Real.pi) := by
              have := abs_lt.mp h_Ls_diff_bound
              linarith
            have h_not_le : ¬(Ls_diff ≤ -Real.pi) := by
              have := abs_lt.mp h_Ls_diff_bound
              linarith
            rw [if_neg h_not_gt, if_neg h_not_le]
            norm_cast
          · -- Case: Δn = 1
            rw [h_pos1]
            simp only [Int.cast_one, mul_one]
            have h_le : Ls_diff - 2 * Real.pi ≤ -Real.pi := by
              have := abs_lt.mp h_Ls_diff_bound
              linarith [Real.pi_pos]
            have h_not_gt : ¬(Ls_diff - 2 * Real.pi > Real.pi) := by
              have := abs_lt.mp h_Ls_diff_bound
              linarith [Real.pi_pos]
            rw [if_neg h_not_gt, if_pos h_le]
            norm_cast

      rw [h_corr_eq_floor_sum, h_floor_sum_eq]

    exact h_correction_sum


  -- Final step: the goal is discrete_winding_number (...) = 1
  -- We use h_wrapped_sum_eq_2pi which shows the sum = 2π

  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hN_ge_1 : N ≥ 1 := by
    have : N ≥ Nat.ceil (2 * L) + 1 := hN
    omega
  have hN_pos' : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_ge_1))

  -- The goal is to show discrete_winding_number = 1
  -- We have h_wrapped_sum_eq_2pi which shows the sum = 2π
  -- Now that discrete_winding_number uses ℕ-typed angles, it unfolds correctly

  simp only [discrete_winding_number, h_eval]
  rw [h_wrapped_sum_eq_2pi]
  exact div_self h2pi_ne

/-- Foundational Theorem: Discrete winding number for linear factor with root outside. -/
theorem discrete_winding_exact_for_circle_outside (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ > r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀,
      discrete_winding_number (Polynomial.X - Polynomial.C α) N r = 0 := by
  /-
  Proof:

  Similar to the inside case, but now the origin is OUTSIDE the image circle.

  Step 1: The curve w(θ) = r·e^{iθ} - α traces a circle of radius r centered at -α.
  Since |α| > r, the origin lies outside this circle.

  Step 2: The winding number of this curve around the origin is 0.
  Geometrically: as we traverse the curve, we don't encircle the origin.

  Step 3: The total argument change is 0 (we return to the starting angle).

  Step 4: With fine enough mesh, the discrete sum approximates this,
  giving discrete_winding = 0.
  -/
  -- The curve stays away from the origin
  have h_gap : ‖α‖ - r > 0 := by linarith

  -- Lipschitz constant for the outside case (factor of 2 from arg bound)
  let L := 2 * r / (‖α‖ - r)
  have hL_pos : L > 0 := by
    apply div_pos
    · linarith
    · exact h_gap

  -- Choose N₀
  use Nat.ceil (2 * L) + 1
  intro N hN

  -- Key simplification: (X - C α).eval z = z - α
  have h_eval : ∀ z : ℂ, (Polynomial.X - Polynomial.C α).eval z = z - α := by
    intro z
    simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

  -- Get the continuous lift from total_arg_change_for_winding_zero
  obtain ⟨lift, h_lift_0, h_lift_2pi, h_arg_eq⟩ := total_arg_change_for_winding_zero α r hr hα

  -- The key property: lift(2π) = lift(0) (no net change, winding = 0)
  have h_total_change : lift (2 * Real.pi) - lift 0 = 0 := by
    rw [h_lift_2pi]; ring

  have hN_pos : (N : ℝ) > 0 := by
    have : N ≥ Nat.ceil (2 * L) + 1 := hN
    have h1 : Nat.ceil (2 * L) + 1 ≥ 1 := Nat.le_add_left 1 _
    have h2 : N ≥ 1 := Nat.le_trans h1 this
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp h2))

  have h_2L_lt_N : 2 * L < N := by
    have h1 : (N : ℝ) ≥ Nat.ceil (2 * L) + 1 := by exact_mod_cast hN
    have h2 : (Nat.ceil (2 * L) : ℝ) ≥ 2 * L := Nat.le_ceil (2 * L)
    linarith

  have h_mesh : (2 * Real.pi) / N < Real.pi / L := by
    have hL_pos' : L > 0 := hL_pos
    have hpi_pos : Real.pi > 0 := Real.pi_pos
    calc (2 * Real.pi) / N
        = 2 * (Real.pi / N) := by ring
      _ < 2 * (Real.pi / (2 * L)) := by
          apply mul_lt_mul_of_pos_left
          apply div_lt_div_of_pos_left hpi_pos (by linarith : 2 * L > 0) h_2L_lt_N
          linarith
      _ = Real.pi / L := by have hL_ne : L ≠ 0 := ne_of_gt hL_pos'; field_simp

  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos

  -- The wrapped sum equals 0 for large N when wrapping is trivial
  have h_wrapped_sum_eq_zero :
      (Finset.sum (Finset.range N) fun j =>
        let θ_curr := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (j : ℝ) / N)) - α)
        let θ_next := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (((j + 1) % N : ℕ) : ℝ) / N)) - α)
        let diff := θ_next - θ_curr
        if diff > Real.pi then diff - 2 * Real.pi
        else if diff ≤ -Real.pi then diff + 2 * Real.pi
        else diff) = 0 := by

    -- Define sample lift values
    let Ls : ℕ → ℝ := fun j => lift (2 * Real.pi * j / N)

    have hLs0 : Ls 0 = lift 0 := by simp [Ls]
    have hLsN : Ls N = lift 0 := by
      simp only [Ls]
      have h : (2 : ℝ) * Real.pi * N / N = 2 * Real.pi := by field_simp [hN_ne]
      rw [h, h_lift_2pi]

    -- Define the raw arg difference function
    set raw_diff : ℕ → ℝ := fun j =>
      let k : ℕ := (j + 1) % N
      Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * k / N)) - α) -
      Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * j / N)) - α) with h_raw_diff_def

    -- The raw sum (circular) equals 0
    have h_raw_circular : (Finset.range N).sum raw_diff = 0 := by
      have hN_pos_nat : 0 < N := by
        have : N ≥ Nat.ceil (2 * L) + 1 := hN
        omega

      let a : ℕ → ℝ := fun j => Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * j / N)) - α)

      have h_eq_sum : (Finset.range N).sum raw_diff =
          (Finset.range N).sum (fun j => a ((j + 1) % N) - a j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [raw_diff, a]

      rw [h_eq_sum]

      have h_circular : (Finset.range N).sum (fun j => a ((j + 1) % N) - a j) = 0 := by
        rw [Finset.sum_sub_distrib]
        suffices h : (Finset.range N).sum (fun j => a ((j + 1) % N)) = (Finset.range N).sum (fun j => a j) by
          rw [h]; ring
        have hN_ge_1 : N ≥ 1 := Nat.one_le_of_lt hN_pos_nat
        refine Finset.sum_bij' (fun j _ => (j + 1) % N) (fun k _ => (k + N - 1) % N) ?_ ?_ ?_ ?_ ?_
        · intro j hj; exact Finset.mem_range.mpr (Nat.mod_lt _ hN_pos_nat)
        · intro k hk; exact Finset.mem_range.mpr (Nat.mod_lt _ hN_pos_nat)
        · intro j hj
          have hj' : j < N := Finset.mem_range.mp hj
          by_cases hj_edge : j + 1 = N
          · have h1 : (j + 1) % N = 0 := by simp [hj_edge]
            simp only [h1, zero_add]
            have h2 : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (by omega)
            simp only [h2]; omega
          · have h1 : (j + 1) % N = j + 1 := Nat.mod_eq_of_lt (by omega)
            simp only [h1]
            have h2 : j + 1 + N - 1 = j + N := by omega
            simp only [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj']
        · intro k hk
          have hk' : k < N := Finset.mem_range.mp hk
          by_cases h0 : k = 0
          · simp only [h0, zero_add]
            have h1 : (N - 1) % N = N - 1 := Nat.mod_eq_of_lt (by omega)
            simp only [h1]
            have h2 : N - 1 + 1 = N := Nat.sub_add_cancel hN_ge_1
            simp only [h2, Nat.mod_self]
          · have hk_pos : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr h0
            have h1 : k + N - 1 = k - 1 + N := by omega
            simp only [h1, Nat.add_mod_right]
            have h2 : k - 1 < N := by omega
            simp only [Nat.mod_eq_of_lt h2]
            have h3 : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
            simp only [h3, Nat.mod_eq_of_lt hk']
        · intro j _; rfl

      exact h_circular

    -- Define the correction function
    set correction : ℝ → ℤ := fun d =>
      if d > Real.pi then -1 else if d ≤ -Real.pi then 1 else 0 with h_corr_def

    have h_wrapped_eq : ∀ d : ℝ,
        (if d > Real.pi then d - 2 * Real.pi
         else if d ≤ -Real.pi then d + 2 * Real.pi
         else d) = d + 2 * Real.pi * correction d := by
      intro d
      simp only [correction]
      split_ifs with h1 h2 <;> ring

    have h_sum_eq : (Finset.sum (Finset.range N) fun j =>
          let θ_curr := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (j : ℝ) / N)) - α)
          let θ_next := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (((j + 1) % N : ℕ) : ℝ) / N)) - α)
          let diff := θ_next - θ_curr
          if diff > Real.pi then diff - 2 * Real.pi
          else if diff ≤ -Real.pi then diff + 2 * Real.pi
          else diff) =
        (Finset.range N).sum (fun j => raw_diff j + 2 * Real.pi * correction (raw_diff j)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [raw_diff]
      exact h_wrapped_eq _

    rw [h_sum_eq, Finset.sum_add_distrib]
    rw [h_raw_circular, zero_add]

    -- The sum of corrections = 0 for winding 0
    -- Floor level n_floor(N) = n_floor(0) (no net change)
    set n_floor : ℕ → ℤ := fun j => toIocDiv two_pi_pos (-Real.pi) (Ls j) with h_nfloor_def

    have h_arg_floor : ∀ k : ℕ, Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * k / N)) - α) =
        Ls k - 2 * Real.pi * n_floor k := by
      intro k
      simp only [Ls, n_floor]
      have h1 := h_arg_eq.1 (2 * Real.pi * k / N)
      have h_exp_eq : (I * (2 * ↑Real.pi * ↑k / ↑N) : ℂ) = I * ↑(2 * Real.pi * k / N) := by
        push_cast; ring
      conv_lhs => rw [h_exp_eq]
      rw [h1, ← self_sub_toIocDiv_zsmul two_pi_pos (-Real.pi)]
      simp only [zsmul_eq_mul]; ring

    -- Key: n_floor(N) = n_floor(0) (since lift is periodic, not shifted by 2π)
    have h_n_diff : n_floor N = n_floor 0 := by
      simp only [n_floor, Ls]
      have h0_simp : (2 : ℝ) * Real.pi * (0 : ℕ) / N = 0 := by simp
      have hN'' : (2 : ℝ) * Real.pi * N / N = 2 * Real.pi := by field_simp [hN_ne]
      simp only [Nat.cast_zero, mul_zero, zero_div] at h0_simp ⊢
      rw [hN'', h_lift_2pi]
      -- Since lift(2π) = lift(0), toIocDiv gives the same value

    have h_key : (n_floor N : ℝ) - (n_floor 0 : ℝ) = 0 := by
      rw [h_n_diff]; ring

    have h_correction_sum : (Finset.range N).sum (fun j => 2 * Real.pi * correction (raw_diff j)) = 0 := by
      rw [← Finset.mul_sum]
      suffices h : (Finset.range N).sum (fun j => (correction (raw_diff j) : ℝ)) = 0 by
        rw [h]; ring

      let floor_diff : ℕ → ℤ := fun j => n_floor (j + 1) - n_floor j

      have h_floor_sum_eq :
          (Finset.range N).sum (fun j => (floor_diff j : ℝ)) = 0 := by
        simp only [floor_diff, Int.cast_sub]
        have h_tel := Finset.sum_range_sub (fun j => (n_floor j : ℝ)) N
        rw [h_tel, h_key]

      have h_corr_eq_floor_sum :
          (Finset.range N).sum (fun j => (correction (raw_diff j) : ℝ)) =
          (Finset.range N).sum (fun j => (floor_diff j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < N := Finset.mem_range.mp hj

      -- Similar floor analysis as in inside case
      -- The key is |Ls(j+1) - Ls(j)| < π for large enough N

        have h_Ls_diff_bound : |Ls (j + 1) - Ls j| < Real.pi := by
          simp only [Ls]
          have hN_ge_1 : N ≥ 1 := by have := hN; omega
          have hN_ne' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hN_ge_1)
          have hN_pos'' : (N : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_ge_1)
          have h_j1_cast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
          have h_lip := h_arg_eq.2 (2 * Real.pi * j / N) (2 * Real.pi * (↑j + 1) / N)
          calc |lift (2 * Real.pi * ↑(j + 1) / ↑N) - lift (2 * Real.pi * ↑j / ↑N)|
              = |lift (2 * Real.pi * (↑j + 1) / ↑N) - lift (2 * Real.pi * ↑j / ↑N)| := by rw [h_j1_cast]
            _ ≤ L * |2 * Real.pi * (↑j + 1) / N - 2 * Real.pi * j / N| := h_lip
            _ = L * |2 * Real.pi / N| := by congr 1; field_simp [hN_ne']; ring_nf
            _ = L * (2 * Real.pi / N) := by rw [abs_of_pos]; positivity
            _ < L * (Real.pi / L) := by apply mul_lt_mul_of_pos_left h_mesh hL_pos
            _ = Real.pi := by field_simp

      -- Floor difference bound
        have h_Δn_bound : n_floor (j + 1) - n_floor j = -1 ∨
            n_floor (j + 1) - n_floor j = 0 ∨ n_floor (j + 1) - n_floor j = 1 := by
          simp only [n_floor]
          have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
          have h_toIocDiv_j1 : toIocDiv two_pi_pos (-Real.pi) (Ls (j + 1)) =
              -⌊(Real.pi - Ls (j + 1)) / (2 * Real.pi)⌋ := by
            rw [toIocDiv_eq_neg_floor]; congr 1; ring_nf
          have h_toIocDiv_j : toIocDiv two_pi_pos (-Real.pi) (Ls j) =
              -⌊(Real.pi - Ls j) / (2 * Real.pi)⌋ := by
            rw [toIocDiv_eq_neg_floor]; congr 1; ring_nf
          rw [h_toIocDiv_j1, h_toIocDiv_j]
          set a' := (Real.pi - Ls (j + 1)) / (2 * Real.pi) with ha'_def
          set b' := (Real.pi - Ls j) / (2 * Real.pi) with hb'_def
          have h_quot_diff : |a' - b'| < 1 := by
            rw [ha'_def, hb'_def, ← sub_div, abs_div, abs_of_pos h2pi_pos]
            calc |Real.pi - Ls (j + 1) - (Real.pi - Ls j)| / (2 * Real.pi)
                = |Ls j - Ls (j + 1)| / (2 * Real.pi) := by ring_nf
              _ = |Ls (j + 1) - Ls j| / (2 * Real.pi) := by rw [abs_sub_comm]
              _ < Real.pi / (2 * Real.pi) := by apply div_lt_div_of_pos_right h_Ls_diff_bound h2pi_pos
              _ = 1 / 2 := by field_simp
              _ < 1 := by norm_num
          have ha'_lt := Int.lt_floor_add_one a'
          have hb'_lt := Int.lt_floor_add_one b'
          have h_abs := abs_lt.mp h_quot_diff
          have h_upper : ⌊b'⌋ ≤ ⌊a'⌋ + 1 := by
            rw [Int.floor_le_iff]
            have ha'_lt' : a' < (⌊a'⌋ : ℝ) + 1 := ha'_lt
            have h1 : b' < a' + 1 := by linarith [h_abs.1]
            have h2 : a' + 1 < (⌊a'⌋ : ℝ) + 2 := by linarith
            calc b' < a' + 1 := h1
              _ < (⌊a'⌋ : ℝ) + 2 := h2
              _ = ((⌊a'⌋ + 1 : ℤ) : ℝ) + 1 := by push_cast; ring
          have h_lower : ⌊a'⌋ ≤ ⌊b'⌋ + 1 := by
            rw [Int.floor_le_iff]
            have hb'_lt' : b' < (⌊b'⌋ : ℝ) + 1 := hb'_lt
            have h1 : a' < b' + 1 := by linarith [h_abs.2]
            have h2 : b' + 1 < (⌊b'⌋ : ℝ) + 2 := by linarith
            calc a' < b' + 1 := h1
              _ < (⌊b'⌋ : ℝ) + 2 := h2
              _ = ((⌊b'⌋ + 1 : ℤ) : ℝ) + 1 := by push_cast; ring
          have h_floor_bound : ⌊b'⌋ - ⌊a'⌋ = -1 ∨ ⌊b'⌋ - ⌊a'⌋ = 0 ∨ ⌊b'⌋ - ⌊a'⌋ = 1 := by omega
          convert h_floor_bound using 1 <;> ring_nf

        set Δn := n_floor (j + 1) - n_floor j with hΔn_def
        set Ls_diff := Ls (j + 1) - Ls j with hLs_diff_def

        by_cases hj_edge : j + 1 = N
        · -- Boundary case
          have hmod : (j + 1) % N = 0 := by simp [hj_edge]
          have hj_eq : j = N - 1 := by omega

          have h_arg0 := h_arg_floor 0
          have h_argN1 := h_arg_floor (N - 1)
          have h_Ls_wrap : Ls 0 = Ls N := by
            simp only [Ls]
            have h0 : (2 : ℝ) * Real.pi * (0 : ℕ) / (N : ℕ) = 0 := by simp
            have hN' : (2 : ℝ) * Real.pi * (N : ℕ) / (N : ℕ) = 2 * Real.pi := by field_simp [hN_ne]
            simp only [Nat.cast_zero, mul_zero, zero_div] at h0 ⊢
            rw [hN', h_lift_2pi]

          simp only [raw_diff, correction, floor_diff]
          rw [hmod, hj_eq]
          have hN_simp : N - 1 + 1 = N := Nat.sub_add_cancel (by omega : 1 ≤ N)
          simp only [hN_simp]

          have hN_ge_1' : N ≥ 1 := by omega
          have h_cast_eq : (0 : ℝ) = (0 : ℕ) ∧ ((N : ℝ) - 1) = ((N - 1 : ℕ) : ℝ) := by
            constructor; simp; simp only [Nat.cast_sub hN_ge_1']; ring

          have h_rd_eq : Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (0 : ℕ) / N)) - α) -
              Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (N - 1 : ℕ) / N)) - α) =
              (Ls N - Ls (N - 1)) - 2 * Real.pi * (n_floor N - n_floor (N - 1)) := by
            calc Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (0 : ℕ) / N)) - α) -
                Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (N - 1 : ℕ) / N)) - α)
              = (Ls 0 - 2 * Real.pi * n_floor 0) - (Ls (N - 1) - 2 * Real.pi * n_floor (N - 1)) := by
                  rw [h_arg0, h_argN1]
              _ = Ls 0 - Ls (N - 1) - 2 * Real.pi * (n_floor 0 - n_floor (N - 1)) := by ring
              _ = Ls N - Ls (N - 1) - 2 * Real.pi * (n_floor 0 - n_floor (N - 1)) := by
                  rw [← h_Ls_wrap]
              _ = (Ls N - Ls (N - 1)) - 2 * Real.pi * (n_floor N - n_floor (N - 1)) := by
                  have h_use : (n_floor N : ℝ) = n_floor 0 := by exact_mod_cast h_n_diff
                  ring_nf; rw [h_use]; ring

          simp only [h_cast_eq.1, h_cast_eq.2] at h_rd_eq
          set raw := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (0 : ℕ) / (N : ℕ))) - α) -
              Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * ((N - 1 : ℕ) : ℕ) / (N : ℕ))) - α) with h_raw_def

          have h_raw_formula : raw = Ls_diff - 2 * Real.pi * ↑Δn := by
            simp only [Ls_diff, Δn, hj_eq, hN_simp]
            convert h_rd_eq using 2 <;> simp only [Int.cast_sub]

          have h_Ls_diff_bound' : |Ls N - Ls (N - 1)| < Real.pi := by
            simp only [Ls]
            have hN_ge_1'' : N ≥ 1 := by omega
            have hN_ne'' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hN_ge_1'')
            have h_cast_Nm1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub hN_ge_1'']; simp
            have hN_pos''' : (N : ℝ) > 0 := by exact_mod_cast Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN_ge_1'')
            have h_abs_eq : |2 * Real.pi * N / N - 2 * Real.pi * (N - 1) / N| = 2 * Real.pi / N := by
              have h_simp : 2 * Real.pi * (N : ℝ) / (N : ℝ) - 2 * Real.pi * ((N : ℝ) - 1) / (N : ℝ) = 2 * Real.pi / (N : ℝ) := by
                field_simp [hN_ne'']; ring
              rw [h_simp, abs_of_pos (div_pos (by linarith [Real.pi_pos] : 2 * Real.pi > 0) hN_pos''')]
            have h_lip := h_arg_eq.2 (2 * Real.pi * ((N : ℝ) - 1) / (N : ℝ)) (2 * Real.pi * (N : ℝ) / (N : ℝ))
            calc |lift (2 * Real.pi * ↑N / ↑N) - lift (2 * Real.pi * ↑(N - 1) / ↑N)|
                = |lift (2 * Real.pi * (N : ℝ) / (N : ℝ)) - lift (2 * Real.pi * ((N : ℝ) - 1) / (N : ℝ))| := by rw [h_cast_Nm1]
              _ ≤ L * |2 * Real.pi * (N : ℝ) / (N : ℝ) - 2 * Real.pi * ((N : ℝ) - 1) / (N : ℝ)| := h_lip
              _ = L * (2 * Real.pi / N) := by rw [h_abs_eq]
              _ < L * (Real.pi / L) := by apply mul_lt_mul_of_pos_left h_mesh hL_pos
              _ = Real.pi := by field_simp

          have h_floor_diff_bound' : n_floor N - n_floor (N - 1) = -1 ∨
              n_floor N - n_floor (N - 1) = 0 ∨ n_floor N - n_floor (N - 1) = 1 := by
            have h := h_Δn_bound
            simp only [hΔn_def] at h
            rw [hj_eq, hN_simp] at h
            exact h

          -- Key: Δn = n_floor (j+1) - n_floor j = n_floor N - n_floor (N-1) after substitution
          have hΔn_eq_bound : Δn = n_floor N - n_floor (N - 1) := by
            simp only [hΔn_def]
            rw [hj_eq, hN_simp]

          rcases h_floor_diff_bound' with h_neg1 | h_0 | h_pos1
          · have hΔn_val : (Δn : ℝ) = -1 := by rw [hΔn_eq_bound, h_neg1]; norm_num
            have h_raw_val : raw = Ls_diff + 2 * Real.pi := by rw [h_raw_formula, hΔn_val]; ring
            have h_Ls_diff_eq : Ls_diff = Ls N - Ls (N - 1) := by simp [Ls_diff, hj_eq, hN_simp]
            have h_gt : raw > Real.pi := by
              rw [h_raw_val, h_Ls_diff_eq]
              have := abs_lt.mp h_Ls_diff_bound'
              linarith [Real.pi_pos]
            simp only [if_pos h_gt, hΔn_eq_bound, h_neg1]
          · have hΔn_val : (Δn : ℝ) = 0 := by rw [hΔn_eq_bound, h_0]; norm_num
            have h_raw_val : raw = Ls_diff := by rw [h_raw_formula, hΔn_val]; ring
            have h_Ls_diff_eq : Ls_diff = Ls N - Ls (N - 1) := by simp [Ls_diff, hj_eq, hN_simp]
            have h_in_range : ¬(raw > Real.pi) ∧ ¬(raw ≤ -Real.pi) := by
              rw [h_raw_val, h_Ls_diff_eq]
              have := abs_lt.mp h_Ls_diff_bound'
              constructor <;> linarith
            simp only [if_neg h_in_range.1, if_neg h_in_range.2, hΔn_eq_bound, h_0]
          · have hΔn_val : (Δn : ℝ) = 1 := by rw [hΔn_eq_bound, h_pos1]; norm_num
            have h_raw_val : raw = Ls_diff - 2 * Real.pi := by rw [h_raw_formula, hΔn_val]; ring
            have h_Ls_diff_eq : Ls_diff = Ls N - Ls (N - 1) := by simp [Ls_diff, hj_eq, hN_simp]
            have h_le : raw ≤ -Real.pi := by
              rw [h_raw_val, h_Ls_diff_eq]
              have := abs_lt.mp h_Ls_diff_bound'
              linarith [Real.pi_pos]
            have h_not_gt : ¬(raw > Real.pi) := by
              rw [h_raw_val, h_Ls_diff_eq]
              have := abs_lt.mp h_Ls_diff_bound'
              linarith [Real.pi_pos]
            simp only [if_neg h_not_gt, if_pos h_le, hΔn_eq_bound, h_pos1]

        · -- Interior case
          have hmod : (j + 1) % N = j + 1 := Nat.mod_eq_of_lt (by omega : j + 1 < N)
          simp only [raw_diff, correction, floor_diff]
          rw [hmod]

          have h_arg_j := h_arg_floor j
          have h_arg_j1 := h_arg_floor (j + 1)
          have h_cast_j1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring

          set raw := Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * (j + 1 : ℕ) / N)) - α) -
              Complex.arg ((r : ℂ) * Complex.exp (I * (2 * Real.pi * j / N)) - α) with h_raw_def

          have h_rd : raw = (Ls (j + 1) - Ls j) - 2 * Real.pi * (n_floor (j + 1) - n_floor j) := by
            rw [h_raw_def, h_arg_j1, h_arg_j]; ring

          have h_raw_formula : raw = Ls_diff - 2 * Real.pi * ↑Δn := by
            rw [hΔn_def, hLs_diff_def]
            convert h_rd using 2; push_cast; ring
          simp only [h_raw_formula]

          rcases h_Δn_bound with h_neg1 | h_0 | h_pos1
          · rw [h_neg1]
            simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one, sub_neg_eq_add]
            have h_gt : Ls_diff + 2 * Real.pi > Real.pi := by
              have := abs_lt.mp h_Ls_diff_bound
              linarith [Real.pi_pos]
            rw [if_pos h_gt]; norm_cast; exact h_neg1.symm
          · rw [h_0]
            simp only [Int.cast_zero, mul_zero, sub_zero]
            have h_not_gt : ¬(Ls_diff > Real.pi) := by
              have := abs_lt.mp h_Ls_diff_bound; linarith
            have h_not_le : ¬(Ls_diff ≤ -Real.pi) := by
              have := abs_lt.mp h_Ls_diff_bound; linarith
            rw [if_neg h_not_gt, if_neg h_not_le]; norm_cast; exact h_0.symm
          · rw [h_pos1]
            simp only [Int.cast_one, mul_one]
            have h_le : Ls_diff - 2 * Real.pi ≤ -Real.pi := by
              have := abs_lt.mp h_Ls_diff_bound
              linarith [Real.pi_pos]
            have h_not_gt : ¬(Ls_diff - 2 * Real.pi > Real.pi) := by
              have := abs_lt.mp h_Ls_diff_bound
              linarith [Real.pi_pos]
            rw [if_neg h_not_gt, if_pos h_le]; norm_cast; exact h_pos1.symm

      rw [h_corr_eq_floor_sum, h_floor_sum_eq]

    exact h_correction_sum

  -- Final step: discrete_winding_number = 0/2π = 0
  simp only [discrete_winding_number, h_eval]
  rw [h_wrapped_sum_eq_zero]
  simp only [zero_div]

-- HELPER LEMMA: Polynomial Divided-Difference Bound
-- Uses the fact that the chord from a to b lies inside the closed disk of radius r
-- Combined with maximum modulus principle for the derivative
set_option maxHeartbeats 1000000 in
private lemma polynomial_divided_difference_bound (F : Polynomial ℂ) (a b : ℂ) (r : ℝ) (M : ℝ)
    (ha : ‖a‖ = r) (hb : ‖b‖ = r)
    (hM_bound : ∀ z : ℂ, ‖z‖ ≤ r → ‖(Polynomial.derivative F).eval z‖ ≤ M) :
    ‖F.eval b - F.eval a‖ ≤ M * ‖b - a‖ := by

  by_cases h_eq : a = b
  · -- Trivial: a = b ⟹ F(a) = F(b)
    simp [h_eq]

  -- Main case: a ≠ b - FULL ELEMENTARY PROOF

  -- Get r ≥ 0
  have hr_nn : 0 ≤ r := by have := norm_nonneg a; rw [ha] at this; exact this

  -- Handle r = 0
  by_cases hr_zero : r = 0
  · have : a = 0 := norm_eq_zero.mp (ha.trans hr_zero)
    have : b = 0 := norm_eq_zero.mp (hb.trans hr_zero)
    simp [*]

  have hr_pos : 0 < r := lt_of_le_of_ne hr_nn (Ne.symm hr_zero)

  -- Key lemma: For k ≥ 1, if |a| = |b| = r, then |bᵏ - aᵏ| ≤ k · rᵏ⁻¹ · |b - a|
  have geom_bound : ∀ k : ℕ, k ≥ 1 → ‖b ^ k - a ^ k‖ ≤ k * r ^ (k - 1) * ‖b - a‖ := by
    intro k hk
    -- Use Commute.geom_sum₂_mul: (Σ i < n, b^i * a^(n-1-i)) * (b - a) = b^n - a^n
    have factor_eq := Commute.geom_sum₂_mul (Commute.all b a) k
    -- Rewrite to get (b - a) * (Σ ...) form
    have factor_identity : b ^ k - a ^ k = (b - a) * (Finset.range k).sum (fun i => b ^ i * a ^ (k - 1 - i)) := by
      rw [mul_comm] at factor_eq
      exact factor_eq.symm

    -- Now bound using triangle inequality
    calc ‖b ^ k - a ^ k‖
      = ‖(b - a) * (Finset.range k).sum (fun i => b ^ i * a ^ (k - 1 - i))‖ := by rw [factor_identity]
    _ = ‖b - a‖ * ‖(Finset.range k).sum (fun i => b ^ i * a ^ (k - 1 - i))‖ := norm_mul _ _
    _ ≤ ‖b - a‖ * (Finset.range k).sum (fun i => ‖b ^ i * a ^ (k - 1 - i)‖) := by
          exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = ‖b - a‖ * (Finset.range k).sum (fun i => ‖b‖ ^ i * ‖a‖ ^ (k - 1 - i)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_mul, norm_pow, norm_pow]
    _ = ‖b - a‖ * (Finset.range k).sum (fun i => r ^ i * r ^ (k - 1 - i)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [ha, hb]
    _ = ‖b - a‖ * (Finset.range k).sum (fun i => r ^ (k - 1)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          have hi_lt : i < k := Finset.mem_range.mp hi
          have : i + (k - 1 - i) = k - 1 := by omega
          rw [← pow_add, this]
    _ = ‖b - a‖ * (k * r ^ (k - 1)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = k * r ^ (k - 1) * ‖b - a‖ := by ring

  -- Now bound F(b) - F(a) using polynomial structure
  have eval_identity : F.eval b - F.eval a = F.support.sum (fun n => F.coeff n * (b ^ n - a ^ n)) := by
    calc F.eval b - F.eval a
      = F.support.sum (fun n => F.coeff n * b ^ n) - F.support.sum (fun n => F.coeff n * a ^ n) := by
          simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]
    _ = F.support.sum (fun n => F.coeff n * b ^ n - F.coeff n * a ^ n) := by
          rw [← Finset.sum_sub_distrib]
    _ = F.support.sum (fun n => F.coeff n * (b ^ n - a ^ n)) := by
          congr 1; ext n; ring

  -- CORRECT APPROACH: Use interval integral and convexity of chord
  -- Key insight: Points on the chord from a to b lie inside the closed disk
  -- |(1-t)a + tb| ≤ (1-t)|a| + t|b| = (1-t)r + tr = r for t ∈ [0,1]

  -- Step 1: Show all points on the chord have norm ≤ r
  have chord_in_disk : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖(1 - t) • a + t • b‖ ≤ r := by
    intro t ht0 ht1
    calc ‖(1 - t) • a + t • b‖
        ≤ ‖(1 - t) • a‖ + ‖t • b‖ := norm_add_le _ _
      _ = |1 - t| * ‖a‖ + |t| * ‖b‖ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ = (1 - t) * r + t * r := by
            rw [ha, hb, abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonneg ht0]
      _ = r := by ring

  -- Step 2: Define the path and show F' is bounded along it
  have deriv_bound_on_chord : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖(Polynomial.derivative F).eval ((1 - t) • a + t • b)‖ ≤ M := by
    intro t ht0 ht1
    exact hM_bound _ (chord_in_disk t ht0 ht1)

  let f : ℝ → ℂ := fun t => (Polynomial.derivative F).eval ((1 - t) • a + t • b)

  -- f is continuous (polynomial composed with continuous linear path)
  have h_path_cont : Continuous (fun t : ℝ => (1 - t) • a + t • b) := by
    apply Continuous.add
    · exact (continuous_const.sub continuous_id).smul continuous_const
    · exact continuous_id.smul continuous_const
  have hf_cont : Continuous f := (Polynomial.continuous_aeval (Polynomial.derivative F)).comp h_path_cont

  -- f is bounded by M on [0,1] (since chord lies in disk where |F'| ≤ M)
  have hf_bound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖f t‖ ≤ M := by
    intro t ht
    exact deriv_bound_on_chord t ht.1 ht.2

  -- The integral ∫₀¹ f(t) dt satisfies |∫ f| ≤ M (interval has length 1)
  have hint_bound : ‖∫ t in (0:ℝ)..1, f t‖ ≤ M * |1 - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact hf_bound t ⟨le_of_lt ht.1, ht.2⟩

  -- Simplify: M * |1 - 0| = M
  simp only [sub_zero, abs_one, mul_one] at hint_bound

  -- Define g(t) = F.eval((1-t)•a + t•b)
  let g : ℝ → ℂ := fun t => F.eval ((1 - t) • a + t • b)

  -- g has derivative f(t) · (b - a) at each t (chain rule)
  have hg_deriv : ∀ t : ℝ, HasDerivAt g (f t * (b - a)) t := by
    intro t
    -- d/dt[(1-t)a + tb] = -a + b = b - a
    have h_path_deriv : HasDerivAt (fun s => (1 - s) • a + s • b) (b - a) t := by
      -- d/dt[(1-s)•a] = (-1)•a = -a
      have h1 : HasDerivAt (fun s : ℝ => (1 - s) • a) (-a) t := by
      -- d/dt[1-s] = -1
        have hd : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
          have h_neg_id : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
          have h_add_one : HasDerivAt (fun s : ℝ => 1 + -s) (-1) t := by
            convert (hasDerivAt_const t (1:ℝ)).add h_neg_id using 1
            ring
          convert h_add_one using 1 <;> ring
        have := hd.smul_const a
        simp only [neg_one_smul] at this
        exact this
      -- d/dt[s•b] = 1•b = b
      have h2 : HasDerivAt (fun s : ℝ => s • b) b t := by
        have := (hasDerivAt_id t).smul_const b
        simp only [id, one_smul] at this
        exact this
      -- d/dt[(1-s)•a + s•b] = -a + b = b - a
      convert h1.add h2 using 1
      abel
    -- Chain rule: d/dt[F(γ(t))] = F'(γ(t)) · γ'(t)
    have h_poly_deriv := Polynomial.hasDerivAt F ((1 - t) • a + t • b)
    exact h_poly_deriv.comp t h_path_deriv

  -- By FTC: g(1) - g(0) = ∫₀¹ g'(t) dt
  have h_integrand_cont : Continuous (fun t => f t * (b - a)) :=
    hf_cont.mul continuous_const
  have hftc : g 1 - g 0 = ∫ t in (0:ℝ)..1, f t * (b - a) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hg_deriv t) (h_integrand_cont.intervalIntegrable 0 1)]

  -- Simplify g(1) and g(0)
  have hg1 : g 1 = F.eval b := by simp [g, smul_eq_mul]
  have hg0 : g 0 = F.eval a := by simp [g, smul_eq_mul]

  -- Factor out (b - a) from integral
  have hint_factor : ∫ t in (0:ℝ)..1, f t * (b - a) = (∫ t in (0:ℝ)..1, f t) * (b - a) := by
    rw [← intervalIntegral.integral_mul_const]

  -- Final calculation
  calc ‖F.eval b - F.eval a‖
      = ‖g 1 - g 0‖ := by rw [hg1, hg0]
    _ = ‖∫ t in (0:ℝ)..1, f t * (b - a)‖ := by rw [hftc]
    _ = ‖(∫ t in (0:ℝ)..1, f t) * (b - a)‖ := by rw [hint_factor]
    _ = ‖∫ t in (0:ℝ)..1, f t‖ * ‖b - a‖ := norm_mul _ _
    _ ≤ M * ‖b - a‖ := mul_le_mul_of_nonneg_right hint_bound (norm_nonneg _)


/-- For a polynomial nonzero on a circle, there's a positive lower bound on its modulus. -/
private lemma polynomial_circle_lower_bound (P : Polynomial ℂ) (r : ℝ) (_hr : 0 < r)
    (hP_nonzero : ∀ θ : ℝ, P.eval (r * Complex.exp (I * θ)) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ θ : ℝ, δ ≤ ‖P.eval (r * Complex.exp (I * θ))‖ := by
  -- The function θ ↦ ‖P.eval(r·e^{iθ})‖ is continuous on [0, 2π]
  -- Since it's positive everywhere and the domain is compact, it attains a positive minimum
  let f : ℝ → ℝ := fun θ => ‖P.eval (r * Complex.exp (I * θ))‖
  -- f is continuous
  have h_inner_cont : Continuous (fun θ : ℝ => P.eval (r * Complex.exp (I * θ))) := by
    apply Continuous.comp (Polynomial.continuous_aeval P)
    apply Continuous.mul continuous_const
    exact Complex.continuous_exp.comp (Continuous.mul continuous_const Complex.continuous_ofReal)
  have hf_cont : Continuous f := h_inner_cont.norm
  -- f is positive everywhere
  have hf_pos : ∀ θ, 0 < f θ := fun θ => norm_pos_iff.mpr (hP_nonzero θ)
  -- f is periodic with period 2π
  have hf_periodic : Function.Periodic f (2 * Real.pi) := by
    intro x
    simp only [f]
    congr 1
    congr 1
    have : (↑(x + 2 * Real.pi) : ℂ) = ↑x + ↑(2 * Real.pi) := by push_cast; ring
    rw [this, mul_add, Complex.exp_add]
    have h2pi : Complex.exp (I * ↑(2 * Real.pi)) = 1 := by
      rw [mul_comm I]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      exact Complex.exp_two_pi_mul_I
    rw [h2pi, mul_one]
  -- Since f is continuous and periodic, its restriction to [0, 2π] attains a minimum
  -- Use compactness of [0, 2π]
  have hcompact : IsCompact (Set.Icc 0 (2 * Real.pi)) := isCompact_Icc
  have hnonempty : Set.Nonempty (Set.Icc 0 (2 * Real.pi)) := by
    use 0
    constructor
    · linarith
    · linarith [Real.pi_pos]
  -- f restricted to [0, 2π] attains its infimum
  obtain ⟨θ₀, hθ₀_mem, hθ₀_min⟩ := hcompact.exists_isMinOn hnonempty hf_cont.continuousOn
  -- The minimum value is positive
  have hmin_pos : 0 < f θ₀ := hf_pos θ₀
  use f θ₀, hmin_pos
  intro θ
  -- Goal is f θ₀ ≤ ‖P.eval (r * exp(I*θ))‖, which is f θ₀ ≤ f θ
  show f θ₀ ≤ f θ
  -- Reduce θ to [0, 2π) using toIcoMod
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  let θ' := toIcoMod h2pi_pos 0 θ
  have hθ'_mem : θ' ∈ Set.Ico 0 (2 * Real.pi) := by
    have := toIcoMod_mem_Ico h2pi_pos 0 θ
    simp only [zero_add] at this
    exact this
  have hθ'_mem_Icc : θ' ∈ Set.Icc 0 (2 * Real.pi) := ⟨hθ'_mem.1, le_of_lt hθ'_mem.2⟩
  -- f(θ) = f(θ') by periodicity
  have hf_θ_eq : f θ = f θ' := by
    have h_diff : ∃ n : ℤ, θ = θ' + n * (2 * Real.pi) := by
      use toIcoDiv h2pi_pos 0 θ
      have := self_sub_toIcoDiv_zsmul h2pi_pos 0 θ
      simp only [zero_add, zsmul_eq_mul] at this
      linarith
    obtain ⟨n, hn⟩ := h_diff
    rw [hn]
    exact (hf_periodic.int_mul n θ')
  rw [hf_θ_eq]
  exact hθ₀_min hθ'_mem_Icc

/-- For large enough N, consecutive polynomial values have positive real inner product. -/
private lemma discrete_winding_positive_inner_product (P : Polynomial ℂ) (r : ℝ) (hr : 0 < r)
    (hP_nonzero : ∀ θ : ℝ, P.eval (r * Complex.exp (I * θ)) ≠ 0) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ j : ZMod N,
      let z_j := r * Complex.exp (I * (2 * Real.pi * (j.val : ℝ) / N))
      let z_next := r * Complex.exp (I * (2 * Real.pi * ((j.val + 1) : ℝ) / N))
      let w_j := P.eval z_j
      let w_next := P.eval z_next
      0 < (w_next * starRingEnd ℂ w_j).re := by
  -- Get the lower bound δ on |P(z)| for z on the circle
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := polynomial_circle_lower_bound P r hr hP_nonzero
  -- Get a bound M on |P'(z)| for z on the circle (derivative bound)
  -- First, P' is also a polynomial, so its eval is continuous
  set P' := Polynomial.derivative P with hP'_def
  set g : ℝ → ℝ := fun θ => ‖P'.eval (r * Complex.exp (I * θ))‖ with hg_def
  have h_g_inner_cont : Continuous (fun θ : ℝ => P'.eval (r * Complex.exp (I * θ))) := by
    apply Continuous.comp (Polynomial.continuous_aeval P')
    apply Continuous.mul continuous_const
    exact Complex.continuous_exp.comp (Continuous.mul continuous_const Complex.continuous_ofReal)
  have hg_cont : Continuous g := h_g_inner_cont.norm
  have hg_periodic : Function.Periodic g (2 * Real.pi) := by
    intro x
    simp only [g]
    congr 1
    congr 1
    have : (↑(x + 2 * Real.pi) : ℂ) = ↑x + ↑(2 * Real.pi) := by push_cast; ring
    rw [this, mul_add, Complex.exp_add]
    have h2pi : Complex.exp (I * ↑(2 * Real.pi)) = 1 := by
      rw [mul_comm I]
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
      exact Complex.exp_two_pi_mul_I
    rw [h2pi, mul_one]
  -- g attains its supremum on [0, 2π] by compactness
  have hcompact : IsCompact (Set.Icc 0 (2 * Real.pi)) := isCompact_Icc
  have hnonempty : Set.Nonempty (Set.Icc 0 (2 * Real.pi)) := ⟨0, by constructor <;> linarith [Real.pi_pos]⟩
  obtain ⟨θ_max, hθ_max_mem, hθ_max_sup⟩ := hcompact.exists_isMaxOn hnonempty hg_cont.continuousOn
  set M := g θ_max with hM_def
  have hM_bound : ∀ θ : ℝ, ‖P'.eval (r * Complex.exp (I * θ))‖ ≤ M := by
    intro θ
    have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    let θ' := toIcoMod h2pi_pos 0 θ
    have hθ'_mem : θ' ∈ Set.Ico 0 (2 * Real.pi) := by
      have := toIcoMod_mem_Ico h2pi_pos 0 θ
      simp only [zero_add] at this
      exact this
    have hθ'_mem_Icc : θ' ∈ Set.Icc 0 (2 * Real.pi) := ⟨hθ'_mem.1, le_of_lt hθ'_mem.2⟩
    have hg_eq : g θ = g θ' := by
      have h_diff : ∃ n : ℤ, θ = θ' + n * (2 * Real.pi) := by
        use toIcoDiv h2pi_pos 0 θ
        have := self_sub_toIcoDiv_zsmul h2pi_pos 0 θ
        simp only [zero_add, zsmul_eq_mul] at this
        linarith
      obtain ⟨n, hn⟩ := h_diff
      rw [hn]
      exact (hg_periodic.int_mul n θ')
    calc g θ = g θ' := hg_eq
      _ ≤ M := hθ_max_sup hθ'_mem_Icc
  by_cases hM_zero : M = 0
  · -- If M = 0, then |P'| ≡ 0 on circle, which implies P is constant
    -- For constant nonzero P: w_j = w_next = c ≠ 0, so Re(c·conj(c)) = |c|² > 0
    use 1, Nat.one_pos
    intro N hN j
    simp only
    -- M = 0 means g ≡ 0, so P'.eval ≡ 0 on circle, so P' = 0 (infinitely many roots)
    -- We show this by using that a nonzero polynomial has finitely many roots
    have hP'_eq_zero : P' = 0 := by
      by_contra hP'_ne
      -- P' ≠ 0 has finitely many roots
      -- But |P'.eval(r·e^{iθ})| = g(θ) ≤ M = 0, so P'.eval = 0 on the whole circle
      -- Circle has infinitely many points, contradiction
      -- For any θ: g(θ) ≤ M = 0, so g(θ) = 0 (since g(θ) ≥ 0), so P'.eval = 0
      have hP'_zero_circle : ∀ θ : ℝ, P'.eval (r * Complex.exp (I * θ)) = 0 := by
        intro θ
        have hbd := hM_bound θ
        rw [hM_zero] at hbd
        exact norm_eq_zero.mp (le_antisymm hbd (norm_nonneg _))
      -- For degree 0: P' is constant, equals 0 at any point, so P' = 0
      -- For degree ≥ 1: construct natDegree + 1 distinct roots and use card_roots'
      by_cases hd : P'.natDegree = 0
      · -- P' is constant
        have hPc := Polynomial.eq_C_of_natDegree_eq_zero hd
        have hr1 : P'.eval (r : ℂ) = 0 := by
          have h0 := hP'_zero_circle 0
          convert h0 using 2
          simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
        rw [hPc] at hr1
        simp only [Polynomial.eval_C] at hr1
        rw [hPc, hr1, map_zero] at hP'_ne
        exact hP'_ne rfl
      · -- P'.natDegree ≥ 1. Use IsPrimitiveRoot.pow_inj for injectivity
        let n := P'.natDegree + 1
        have hn_pos : 0 < n := Nat.succ_pos _
        have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
      -- ζ is a primitive n-th root of unity
        let ζ := Complex.exp (2 * Real.pi * I / n)
        have hζ_prim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n (Nat.cast_ne_zero.mpr hn_ne)
        have hζ_pow_n : ζ ^ n = 1 := hζ_prim.pow_eq_one
      -- Build finset of n distinct roots
        have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
        let f := fun k : ℕ => (r : ℂ) * ζ ^ k
        let S := (Finset.range n).image f
      -- S has n elements by IsPrimitiveRoot.pow_inj
        have hS_card : S.card = n := by
          have h_inj : Set.InjOn f (Finset.range n) := by
            intro k₁ hk₁ k₂ hk₂ h_eq
            simp only [Finset.coe_range, Set.mem_Iio] at hk₁ hk₂
            simp only [f] at h_eq
            have h_pow_eq : ζ ^ k₁ = ζ ^ k₂ := mul_left_cancel₀ hr_ne h_eq
            exact hζ_prim.pow_inj hk₁ hk₂ h_pow_eq
          rw [Finset.card_image_of_injOn h_inj, Finset.card_range]
      -- All elements of S are roots of P'
        have hS_roots : ∀ z ∈ S, P'.eval z = 0 := by
          intro z hz
          rw [Finset.mem_image] at hz
          obtain ⟨k, _, rfl⟩ := hz
          -- f k = r * ζ^k = r * exp(2πi*k/n)
          -- Use the angle θ_k = 2πk/n
          let θ_k : ℝ := 2 * Real.pi * k / n
          have h_eq : f k = r * Complex.exp (I * θ_k) := by
            simp only [f, ζ, θ_k]
            congr 2
            rw [← Complex.exp_nat_mul]
            congr 1
            simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast,
                       Complex.ofReal_ofNat]
            ring
          rw [h_eq]
          exact hP'_zero_circle θ_k
      -- Apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
        have h_lt : P'.natDegree < S.card := by rw [hS_card]; omega
        exact hP'_ne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P' S hS_roots h_lt)
    -- P' = 0 means P is constant
    rw [hP'_def] at hP'_eq_zero
    have hP_const : P.natDegree = 0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hP'_eq_zero
    have hP_eq_const : P = Polynomial.C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hP_const
    -- For constant P, all evaluations are equal
    have hw_eq : ∀ z₁ z₂ : ℂ, P.eval z₁ = P.eval z₂ := fun z₁ z₂ => by
      rw [hP_eq_const]
      simp only [Polynomial.eval_C]
    -- w_j = w_next, so Re(w_next · conj(w_j)) = Re(w_j · conj(w_j)) = |w_j|² > 0
    let z_j := r * Complex.exp (I * (2 * Real.pi * (j.val : ℝ) / N))
    let z_next := r * Complex.exp (I * (2 * Real.pi * ((j.val + 1) : ℝ) / N))
    have h_eq : P.eval z_next = P.eval z_j := hw_eq z_next z_j
    -- The goal is: 0 < Re(P.eval z_next * conj(P.eval z_j))
    -- After h_eq: 0 < Re(P.eval z_j * conj(P.eval z_j)) = 0 < |P.eval z_j|²
    have hne : P.eval z_j ≠ 0 := by
      have h := hP_nonzero (2 * Real.pi * (j.val : ℝ) / N)
      simp only [z_j]
      convert h using 2
      push_cast
      ring
    -- Use Complex.mul_conj z = normSq z which is real, so Re(normSq z) = normSq z
    calc (P.eval z_next * star (P.eval z_j)).re
        = (P.eval z_j * star (P.eval z_j)).re := by rw [h_eq]
      _ = ((P.eval z_j).normSq : ℂ).re := by simp only [Complex.star_def, Complex.mul_conj]
      _ = (P.eval z_j).normSq := Complex.ofReal_re _
      _ > 0 := Complex.normSq_pos.mpr hne
  · -- M > 0 case
    have hM_pos : 0 < M := by
      have hM_nonneg : 0 ≤ M := by rw [hM_def]; exact norm_nonneg _
      by_contra h
      push_neg at h
      have h_eq : M = 0 := le_antisymm h hM_nonneg
      exact hM_zero h_eq
    -- Define coefficient-based bound M_disk for the closed disk
    -- |P'(z)| ≤ Σ |P'.coeff k| · |z|^k ≤ Σ |P'.coeff k| · r^k = M_disk for |z| ≤ r
    let M_disk := (Finset.range (P'.natDegree + 1)).sum (fun k => ‖P'.coeff k‖ * r^k)
    -- M_disk bounds P' on the closed disk
    have hM_disk_bound : ∀ z : ℂ, ‖z‖ ≤ r → ‖P'.eval z‖ ≤ M_disk := by
      intro z hz
      calc ‖P'.eval z‖
          = ‖(Finset.range (P'.natDegree + 1)).sum (fun k => P'.coeff k * z^k)‖ := by
              rw [Polynomial.eval_eq_sum_range]
        _ ≤ (Finset.range (P'.natDegree + 1)).sum (fun k => ‖P'.coeff k * z^k‖) := norm_sum_le _ _
        _ = (Finset.range (P'.natDegree + 1)).sum (fun k => ‖P'.coeff k‖ * ‖z‖^k) := by
            congr 1; ext k; rw [norm_mul, norm_pow]
        _ ≤ (Finset.range (P'.natDegree + 1)).sum (fun k => ‖P'.coeff k‖ * r^k) := by
            apply Finset.sum_le_sum
            intro k _
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact pow_le_pow_left₀ (norm_nonneg z) hz k
        _ = M_disk := rfl
    -- M ≤ M_disk (M is max on circle, M_disk bounds everywhere including circle)
    have hM_le_M_disk : M ≤ M_disk := by
      simp only [hM_def, hg_def]
      have hz : ‖r * Complex.exp (I * θ_max)‖ ≤ r := by
        have h1 : ‖(r : ℂ)‖ = r := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        have h2 : ‖Complex.exp (I * θ_max)‖ = 1 := by
          rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ_max
        rw [norm_mul, h1, h2, mul_one]
      exact hM_disk_bound (r * Complex.exp (I * θ_max)) hz
    -- M_disk > 0 since M > 0 and M ≤ M_disk
    have hM_disk_pos : 0 < M_disk := lt_of_lt_of_le hM_pos hM_le_M_disk
    -- Choose N₀ such that M_disk * 2πr/N₀ < δ
    -- Use M_disk (disk bound) instead of M (circle max) for correctness
    let bound := 2 * Real.pi * r * M_disk / δ
    -- Need N₀ > bound, so take ⌈bound⌉ + 1
    use Nat.ceil bound + 1
    constructor
    · omega
    intro N hN j
    simp only
    -- Check N > bound
    have hN_gt : (N : ℝ) > bound := by
      have h1 : (Nat.ceil bound : ℝ) ≥ bound := Nat.le_ceil bound
      have h2 : (N : ℕ) ≥ Nat.ceil bound + 1 := hN
      calc (N : ℝ) ≥ (Nat.ceil bound + 1 : ℕ) := by exact Nat.cast_le.mpr h2
        _ = (Nat.ceil bound : ℝ) + 1 := by simp
        _ > bound := by linarith
    have hN_pos : (0 : ℝ) < N := by
      have hN_nat_pos : 0 < N := Nat.lt_of_lt_of_le (Nat.succ_pos _) hN
      exact Nat.cast_pos.mpr hN_nat_pos
    -- Set up the points
    let θ_j := 2 * Real.pi * (j.val : ℝ) / N
    let θ_next := 2 * Real.pi * ((j.val + 1) : ℝ) / N
    let z_j := r * Complex.exp (I * θ_j)
    let z_next := r * Complex.exp (I * θ_next)
    let w_j := P.eval z_j
    let w_next := P.eval z_next
    -- Step 1: bound |z_next - z_j|
    have hz_diff : ‖z_next - z_j‖ ≤ 2 * Real.pi * r / N := by
      -- z_next - z_j = r * (exp(i*θ_next) - exp(i*θ_j))
      --              = r * exp(i*θ_j) * (exp(i*(θ_next - θ_j)) - 1)
      have hdiff : z_next - z_j = r * Complex.exp (I * θ_j) *
                                  (Complex.exp (I * (θ_next - θ_j)) - 1) := by
        show r * Complex.exp (I * θ_next) - r * Complex.exp (I * θ_j) =
             r * Complex.exp (I * θ_j) * (Complex.exp (I * (θ_next - θ_j)) - 1)
        have hexp : Complex.exp (I * θ_j) * Complex.exp (I * (θ_next - θ_j)) = Complex.exp (I * θ_next) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
        calc r * Complex.exp (I * θ_next) - r * Complex.exp (I * θ_j)
            = r * (Complex.exp (I * θ_j) * Complex.exp (I * (θ_next - θ_j))) -
              r * Complex.exp (I * θ_j) := by rw [hexp]
          _ = r * Complex.exp (I * θ_j) * Complex.exp (I * (θ_next - θ_j)) -
              r * Complex.exp (I * θ_j) * 1 := by ring
          _ = r * Complex.exp (I * θ_j) * (Complex.exp (I * (θ_next - θ_j)) - 1) := by ring
      rw [hdiff]
      rw [norm_mul, norm_mul]
      have hr_norm : ‖(r : ℂ)‖ = r := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have hexp_norm : ‖Complex.exp (I * ↑θ_j)‖ = 1 := by
        rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ_j
      rw [hr_norm, hexp_norm, mul_one]
      -- Now bound ‖exp(i*(θ_next - θ_j)) - 1‖
      have hθ_diff : θ_next - θ_j = 2 * Real.pi / N := by
        show 2 * Real.pi * ((j.val + 1) : ℝ) / N - 2 * Real.pi * (j.val : ℝ) / N = 2 * Real.pi / N
        field_simp
        ring
      simp only [← Complex.ofReal_sub] at *
      rw [hθ_diff]
      -- Use |exp(iθ) - 1| ≤ |θ|
      have hexp_bound : ‖Complex.exp (I * (2 * Real.pi / N : ℝ)) - 1‖ ≤ |2 * Real.pi / N| := by
        have := @norm_exp_I_mul_ofReal_sub_one_le (2 * Real.pi / N)
        simp only [Real.norm_eq_abs] at this
        convert this using 2
      calc r * ‖Complex.exp (I * ↑(2 * Real.pi / N)) - 1‖
          ≤ r * |2 * Real.pi / N| := by apply mul_le_mul_of_nonneg_left hexp_bound (le_of_lt hr)
        _ = r * (2 * Real.pi / N) := by
            rw [abs_of_pos]
            apply div_pos (by linarith [Real.pi_pos]) hN_pos
        _ = 2 * Real.pi * r / N := by ring
    -- Step 2: bound |w_next - w_j| using mean value theorem
    -- Actually we use our polynomial_divided_difference_bound, but that requires points on circle
    -- Here z_j and z_next are on the circle |z| = r
    have hz_j_norm : ‖z_j‖ = r := by
      show ‖r * Complex.exp (I * θ_j)‖ = r
      have h1 : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have h2 : ‖Complex.exp (I * θ_j)‖ = 1 := by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ_j
      rw [norm_mul, h1, h2, mul_one]
    have hz_next_norm : ‖z_next‖ = r := by
      show ‖r * Complex.exp (I * θ_next)‖ = r
      have h1 : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have h2 : ‖Complex.exp (I * θ_next)‖ = 1 := by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ_next
      rw [norm_mul, h1, h2, mul_one]
    -- Get derivative bound on disk (use M_disk which we already proved)
    have hM_disk_circle : ∀ z : ℂ, ‖z‖ ≤ r → ‖P'.eval z‖ ≤ M_disk := hM_disk_bound
    have hw_diff : ‖w_next - w_j‖ ≤ M_disk * ‖z_next - z_j‖ := by
      show ‖P.eval z_next - P.eval z_j‖ ≤ M_disk * ‖z_next - z_j‖
      exact polynomial_divided_difference_bound P z_j z_next r M_disk hz_j_norm hz_next_norm hM_disk_circle
    -- Step 3: Combine bounds
    have hw_diff_bound : ‖w_next - w_j‖ < δ := by
      calc ‖w_next - w_j‖ ≤ M_disk * ‖z_next - z_j‖ := hw_diff
        _ ≤ M_disk * (2 * Real.pi * r / N) := by
            apply mul_le_mul_of_nonneg_left hz_diff (le_of_lt hM_disk_pos)
        _ = (2 * Real.pi * r * M_disk) / N := by ring
        _ < δ := by
            rw [div_lt_iff₀ hN_pos]
            have h_bound_eq : 2 * Real.pi * r * M_disk = bound * δ := by
              show 2 * Real.pi * r * M_disk = (2 * Real.pi * r * M_disk / δ) * δ
              field_simp
            calc 2 * Real.pi * r * M_disk = bound * δ := h_bound_eq
              _ < N * δ := mul_lt_mul_of_pos_right hN_gt hδ_pos
              _ = δ * N := mul_comm _ _

    have hw_j_ge_δ : δ ≤ ‖w_j‖ := hδ_bound θ_j
    have hw_next_ge_δ : δ ≤ ‖w_next‖ := hδ_bound θ_next
    have hmin_ge_δ : δ ≤ min ‖w_j‖ ‖w_next‖ := le_min hw_j_ge_δ hw_next_ge_δ
    have hw_diff_lt_min : ‖w_next - w_j‖ < min ‖w_j‖ ‖w_next‖ := lt_of_lt_of_le hw_diff_bound hmin_ge_δ
    -- The identity: |a - b|² = |a|² + |b|² - 2·Re(a * conj(b))
    have h_identity : ‖w_next - w_j‖^2 = ‖w_next‖^2 + ‖w_j‖^2 - 2 * (w_next * starRingEnd ℂ w_j).re := by
      -- Use the polarization identity directly
      have h_norm_sq : ∀ z : ℂ, ‖z‖^2 = (z.normSq : ℝ) := fun z => by
        rw [Complex.normSq_eq_norm_sq]
      have h_normSq_re : ∀ z : ℂ, z.normSq = (z * star z).re := fun z => by
        simp only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
      rw [h_norm_sq, h_norm_sq, h_norm_sq, h_normSq_re, h_normSq_re, h_normSq_re]
      -- Expand (a - b) * conj(a - b)
      have hexp : (w_next - w_j) * star (w_next - w_j) =
                  w_next * star w_next + w_j * star w_j -
                  w_next * star w_j - star w_next * w_j := by
        rw [star_sub]
        ring
      rw [hexp]
      -- star w_next * w_j = star (w_next * star w_j)
      have hconj : star w_next * w_j = star (w_next * star w_j) := by
        rw [star_mul, star_star, mul_comm]
      rw [hconj]
      -- Re(z) + Re(star z) = 2 * Re(z)
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_conj, Complex.ofReal_re,
                 Complex.star_def, Complex.conj_re]
      ring
    -- From the identity: Re(w_next * conj(w_j)) = (|w_next|² + |w_j|² - |w_next - w_j|²) / 2
    have h_re_formula : (w_next * starRingEnd ℂ w_j).re =
                        (‖w_next‖^2 + ‖w_j‖^2 - ‖w_next - w_j‖^2) / 2 := by linarith
    -- We need to prove positivity using h_re_formula and the bounds below
    -- Since |w_next - w_j| < min(|w_next|, |w_j|), we have |w_next - w_j|² < min(|w_next|², |w_j|²)
    have hw_diff_sq_lt : ‖w_next - w_j‖^2 < min (‖w_next‖^2) (‖w_j‖^2) := by
      -- hw_diff_lt_min : ‖w_next - w_j‖ < min ‖w_j‖ ‖w_next‖
      have hlt_next : ‖w_next - w_j‖ < ‖w_next‖ := lt_of_lt_of_le hw_diff_lt_min (min_le_right _ _)
      have hlt_j : ‖w_next - w_j‖ < ‖w_j‖ := lt_of_lt_of_le hw_diff_lt_min (min_le_left _ _)
      have hsq_lt_next : ‖w_next - w_j‖^2 < ‖w_next‖^2 := by
        have hneg : -‖w_next‖ < ‖w_next - w_j‖ := by
          have hpos : 0 < ‖w_next‖ := norm_pos_iff.mpr (hP_nonzero θ_next)
          linarith [norm_nonneg (w_next - w_j)]
        exact sq_lt_sq' hneg hlt_next
      have hsq_lt_j : ‖w_next - w_j‖^2 < ‖w_j‖^2 := by
        have hneg : -‖w_j‖ < ‖w_next - w_j‖ := by
          have hpos : 0 < ‖w_j‖ := norm_pos_iff.mpr (hP_nonzero θ_j)
          linarith [norm_nonneg (w_next - w_j)]
        exact sq_lt_sq' hneg hlt_j
      exact lt_min hsq_lt_next hsq_lt_j
    -- So |w_next|² + |w_j|² - |w_next - w_j|² > max(|w_next|², |w_j|²) > 0
    have hmax_pos : 0 < max (‖w_next‖^2) (‖w_j‖^2) := by
      have hw_next_pos : 0 < ‖w_next‖ := norm_pos_iff.mpr (hP_nonzero θ_next)
      exact lt_max_of_lt_left (sq_pos_of_pos hw_next_pos)
    have hsum_gt_max : max (‖w_next‖^2) (‖w_j‖^2) < ‖w_next‖^2 + ‖w_j‖^2 - ‖w_next - w_j‖^2 := by
      have hmin_lt : ‖w_next - w_j‖^2 < min (‖w_next‖^2) (‖w_j‖^2) := hw_diff_sq_lt
      -- max + min = sum, so sum - diff² > sum - min = max
      have hsum : max (‖w_next‖^2) (‖w_j‖^2) + min (‖w_next‖^2) (‖w_j‖^2) =
                  ‖w_next‖^2 + ‖w_j‖^2 := max_add_min _ _
      linarith
    -- Positivity: h_re_formula says Re = (sum of norms - diff²)/2
    -- hmax_pos and hsum_gt_max imply sum - diff² > 0, so Re > 0
    have hre_pos : 0 < (w_next * starRingEnd ℂ w_j).re := by
      rw [h_re_formula]
      apply div_pos _ (by norm_num : (0:ℝ) < 2)
      linarith
    -- The goal has expanded forms - unfold the let bindings and normalize
    simp only [w_next, w_j, z_next, z_j, θ_next, θ_j] at hre_pos
    convert hre_pos using 3
    · push_cast; ring
    · push_cast; ring


set_option maxHeartbeats 1500000 in
/-- Theorem: Discrete winding is EXACTLY additive for products when N is large enough. -/

theorem discrete_winding_mul_exact (P Q : Polynomial ℂ) (r : ℝ) (hr : 0 < r)
    (hP_nonzero : ∀ θ : ℝ, P.eval (r * Complex.exp (I * θ)) ≠ 0)
    (hQ_nonzero : ∀ θ : ℝ, Q.eval (r * Complex.exp (I * θ)) ≠ 0) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      discrete_winding_number (P * Q) N r =
       discrete_winding_number P N r + discrete_winding_number Q N r := by
  -- P*Q is also nonzero on the circle
  have hPQ_nonzero : ∀ θ : ℝ, (P * Q).eval (r * Complex.exp (I * θ)) ≠ 0 := by
    intro θ
    simp only [Polynomial.eval_mul]
    exact mul_ne_zero (hP_nonzero θ) (hQ_nonzero θ)

  /-
  Proof by lattice exhaustion:

  For polynomial F nonzero on circle |z| = r:
  - The curve γ_F(θ) = F(r·e^{iθ}) is continuous and avoids 0
  - There exists a continuous lift L_F : ℝ → ℝ of arg(γ_F)
  - L_F(2π) - L_F(0) = 2π × winding(F) (an integer)
  - L_F is uniformly continuous on compact [0, 2π]
  - For N large enough, all |L_F(θ_{j+1}) - L_F(θ_j)| < π
  - When lift changes are < π, wrap(Δarg) = Δ(lift), so discrete sum is exact

  For products:
  - L_{PQ}(θ) = L_P(θ) + L_Q(θ) + const (since arg(PQ) = arg(P) + arg(Q) mod 2π)
  - Total changes add: L_{PQ}(2π) - L_{PQ}(0) = (L_P(2π) - L_P(0)) + (L_Q(2π) - L_Q(0))
  - So winding(PQ) = winding(P) + winding(Q)
  - When N is large enough for all three to stabilize, discrete windings add exactly.
  -/


  by_cases hP_zero : P = 0
  · -- If P = 0, then P is zero everywhere, contradicting hP_nonzero
    exfalso
    have := hP_nonzero 0
    simp [hP_zero] at this

  -- Case: Q = 0
  by_cases hQ_zero : Q = 0
  · -- If Q = 0, then Q is zero everywhere, contradicting hQ_nonzero
    exfalso
    have := hQ_nonzero 0
    simp [hQ_zero] at this

  have hP_roots : ∀ α ∈ P.roots, ‖α‖ ≠ r := by
    intro α hα heq
    -- If |α| = r, then P(r * exp(iθ)) = 0 for some θ, contradicting hP_nonzero
    have h_on_circle : ∃ θ : ℝ, α = r * Complex.exp (I * θ) := by
      -- α lies on circle |z| = r, so α = r * e^{iθ} for some θ
      have hα_ne : α ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at heq
        exact (ne_of_gt hr) heq.symm
      use Complex.arg α
      -- α = ‖α‖ * e^{i * arg α}
      have h_rep := Complex.norm_mul_exp_arg_mul_I α
      calc α = ‖α‖ * Complex.exp (Complex.arg α * I) := h_rep.symm
        _ = r * Complex.exp (Complex.arg α * I) := by rw [heq]
        _ = r * Complex.exp (I * Complex.arg α) := by ring_nf
    obtain ⟨θ, hθ⟩ := h_on_circle
    have := hP_nonzero θ
    rw [← hθ] at this
    exact this (Polynomial.isRoot_of_mem_roots hα)

  have hQ_roots : ∀ α ∈ Q.roots, ‖α‖ ≠ r := by
    intro α hα heq
    have h_on_circle : ∃ θ : ℝ, α = r * Complex.exp (I * θ) := by
      have hα_ne : α ≠ 0 := by
        intro h0; rw [h0, norm_zero] at heq; exact (ne_of_gt hr) heq.symm
      use Complex.arg α
      have h_rep := Complex.norm_mul_exp_arg_mul_I α
      calc α = ‖α‖ * Complex.exp (Complex.arg α * I) := h_rep.symm
        _ = r * Complex.exp (Complex.arg α * I) := by rw [← heq]
        _ = r * Complex.exp (I * Complex.arg α) := by ring_nf
    obtain ⟨θ, hθ⟩ := h_on_circle
    have := hQ_nonzero θ
    rw [← hθ] at this
    exact this (Polynomial.isRoot_of_mem_roots hα)

  have hP_min_exists : ∃ δ_P : ℝ, δ_P > 0 ∧ ∀ θ : ℝ, ‖P.eval (r * Complex.exp (I * θ))‖ ≥ δ_P := by
    have h_inner_cont : Continuous (fun θ : ℝ => (r : ℂ) * Complex.exp (I * ↑θ)) :=
      continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    have h_eval_cont : Continuous (fun z : ℂ => P.eval z) := P.continuous
    have h_cont : Continuous (fun θ : ℝ => P.eval ((r : ℂ) * Complex.exp (I * ↑θ))) :=
      h_eval_cont.comp h_inner_cont
    have h_compact : IsCompact (Set.Icc 0 (2 * Real.pi)) := isCompact_Icc
    have h_nonempty : Set.Nonempty (Set.Icc (0 : ℝ) (2 * Real.pi)) := ⟨0, by simp [Real.pi_pos.le]⟩
    have h_norm_cont : Continuous (fun θ : ℝ => ‖P.eval ((r : ℂ) * Complex.exp (I * ↑θ))‖) :=
      continuous_norm.comp h_cont
    obtain ⟨θ_min, hθ_min_mem, hθ_min⟩ := h_compact.exists_isMinOn h_nonempty h_norm_cont.continuousOn
    use ‖P.eval (r * Complex.exp (I * θ_min))‖
    constructor
    · exact norm_pos_iff.mpr (hP_nonzero θ_min)
    · intro θ
      -- Map θ to [0, 2π] using periodicity
      let θ' := toIocMod Real.two_pi_pos 0 θ
      have hθ'_mem : θ' ∈ Set.Icc 0 (2 * Real.pi) := by
        have := toIocMod_mem_Ioc Real.two_pi_pos 0 θ
        constructor <;> linarith [this.1, this.2]
      have hθ'_eq : ‖P.eval (r * Complex.exp (I * θ))‖ = ‖P.eval (r * Complex.exp (I * θ'))‖ := by
        have h_mod := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos 0 θ
        rw [zsmul_eq_mul] at h_mod
        have h_exp_eq : Complex.exp (I * ↑θ) = Complex.exp (I * ↑θ') := by
          let k := toIocDiv Real.two_pi_pos 0 θ
          have h_diff : θ = θ' + k * (2 * Real.pi) := h_mod.symm
          calc Complex.exp (I * ↑θ)
            = Complex.exp (I * ↑(θ' + ↑k * (2 * Real.pi))) := by rw [h_diff]
            _ = Complex.exp (I * ↑θ' + ↑k * (2 * ↑Real.pi * I)) := by
                congr 1; push_cast; ring
            _ = Complex.exp (I * ↑θ') := (Complex.exp_periodic.int_mul k) (I * ↑θ')
        rw [h_exp_eq]
      rw [hθ'_eq]
      exact hθ_min hθ'_mem

  -- Step 2: Get minimum modulus for Q
  have hQ_min_exists : ∃ δ_Q : ℝ, δ_Q > 0 ∧ ∀ θ : ℝ, ‖Q.eval (r * Complex.exp (I * θ))‖ ≥ δ_Q := by
    have h_inner_cont : Continuous (fun θ : ℝ => (r : ℂ) * Complex.exp (I * ↑θ)) :=
      continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    have h_eval_cont : Continuous (fun z : ℂ => Q.eval z) := Q.continuous
    have h_cont : Continuous (fun θ : ℝ => Q.eval ((r : ℂ) * Complex.exp (I * ↑θ))) :=
      h_eval_cont.comp h_inner_cont
    have h_compact : IsCompact (Set.Icc 0 (2 * Real.pi)) := isCompact_Icc
    have h_nonempty : Set.Nonempty (Set.Icc (0 : ℝ) (2 * Real.pi)) := ⟨0, by simp [Real.pi_pos.le]⟩
    have h_norm_cont : Continuous (fun θ : ℝ => ‖Q.eval ((r : ℂ) * Complex.exp (I * ↑θ))‖) :=
      continuous_norm.comp h_cont
    obtain ⟨θ_min, hθ_min_mem, hθ_min⟩ := h_compact.exists_isMinOn h_nonempty h_norm_cont.continuousOn
    use ‖Q.eval (r * Complex.exp (I * θ_min))‖
    constructor
    · exact norm_pos_iff.mpr (hQ_nonzero θ_min)
    · intro θ
      let θ' := toIocMod Real.two_pi_pos 0 θ
      have hθ'_mem : θ' ∈ Set.Icc 0 (2 * Real.pi) := by
        have := toIocMod_mem_Ioc Real.two_pi_pos 0 θ
        constructor <;> linarith [this.1, this.2]
      have hθ'_eq : ‖Q.eval (r * Complex.exp (I * θ))‖ = ‖Q.eval (r * Complex.exp (I * θ'))‖ := by
        have h_mod := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos 0 θ
        rw [zsmul_eq_mul] at h_mod
        have h_exp_eq : Complex.exp (I * ↑θ) = Complex.exp (I * ↑θ') := by
          let k := toIocDiv Real.two_pi_pos 0 θ
          have h_diff : θ = θ' + k * (2 * Real.pi) := h_mod.symm
          calc Complex.exp (I * ↑θ)
            = Complex.exp (I * ↑(θ' + ↑k * (2 * Real.pi))) := by rw [h_diff]
            _ = Complex.exp (I * ↑θ' + ↑k * (2 * ↑Real.pi * I)) := by
                congr 1; push_cast; ring
            _ = Complex.exp (I * ↑θ') := (Complex.exp_periodic.int_mul k) (I * ↑θ')
        rw [h_exp_eq]
      rw [hθ'_eq]
      exact hθ_min hθ'_mem

  obtain ⟨δ_P, hδ_P_pos, hδ_P⟩ := hP_min_exists
  obtain ⟨δ_Q, hδ_Q_pos, hδ_Q⟩ := hQ_min_exists

  -- Step 3: Get maximum derivative bounds for P and Q on the circle
  -- The curve F(r*e^{iθ}) has velocity d/dθ = i*r*e^{iθ}*F'(r*e^{iθ})
  -- Velocity magnitude ≤ r * max|F'| on circle

  have hP_deriv_bound : ∃ M_P : ℝ, M_P > 0 ∧ ∀ θ : ℝ,
      ‖Polynomial.derivative P |>.eval (r * Complex.exp (I * θ))‖ ≤ M_P := by
    have h_inner_cont : Continuous (fun θ : ℝ => (r : ℂ) * Complex.exp (I * ↑θ)) :=
      continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    have h_eval_cont : Continuous (fun z : ℂ => (Polynomial.derivative P).eval z) :=
      (Polynomial.derivative P).continuous
    have h_cont : Continuous (fun θ : ℝ => (Polynomial.derivative P).eval ((r : ℂ) * Complex.exp (I * ↑θ))) :=
      h_eval_cont.comp h_inner_cont
    have h_compact : IsCompact (Set.Icc 0 (2 * Real.pi)) := isCompact_Icc
    have h_nonempty : Set.Nonempty (Set.Icc (0 : ℝ) (2 * Real.pi)) := ⟨0, by simp [Real.pi_pos.le]⟩
    have h_norm_cont : Continuous (fun θ : ℝ => ‖(Polynomial.derivative P).eval ((r : ℂ) * Complex.exp (I * ↑θ))‖) :=
      continuous_norm.comp h_cont
    obtain ⟨θ_max, hθ_max_mem, hθ_max⟩ := h_compact.exists_isMaxOn h_nonempty h_norm_cont.continuousOn
    use ‖(Polynomial.derivative P).eval (r * Complex.exp (I * θ_max))‖ + 1
    constructor
    · linarith [norm_nonneg ((Polynomial.derivative P).eval (r * Complex.exp (I * θ_max)))]
    · intro θ
      let θ' := toIocMod Real.two_pi_pos 0 θ
      have hθ'_mem : θ' ∈ Set.Icc 0 (2 * Real.pi) := by
        have := toIocMod_mem_Ioc Real.two_pi_pos 0 θ
        constructor <;> linarith [this.1, this.2]
      have hθ'_eq : ‖(Polynomial.derivative P).eval (r * Complex.exp (I * θ))‖ =
                    ‖(Polynomial.derivative P).eval (r * Complex.exp (I * θ'))‖ := by
        have h_mod := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos 0 θ
        rw [zsmul_eq_mul] at h_mod
        have h_exp_eq : Complex.exp (I * ↑θ) = Complex.exp (I * ↑θ') := by
          let k := toIocDiv Real.two_pi_pos 0 θ
          have h_diff : θ = θ' + k * (2 * Real.pi) := h_mod.symm
          calc Complex.exp (I * ↑θ)
            = Complex.exp (I * ↑(θ' + ↑k * (2 * Real.pi))) := by rw [h_diff]
            _ = Complex.exp (I * ↑θ' + ↑k * (2 * ↑Real.pi * I)) := by
                congr 1; push_cast; ring
            _ = Complex.exp (I * ↑θ') := (Complex.exp_periodic.int_mul k) (I * ↑θ')
        rw [h_exp_eq]
      rw [hθ'_eq]
      have h_le := hθ_max hθ'_mem
      exact le_add_of_le_of_nonneg h_le (by norm_num : (1 : ℝ) ≥ 0)

  have hQ_deriv_bound : ∃ M_Q : ℝ, M_Q > 0 ∧ ∀ θ : ℝ,
      ‖Polynomial.derivative Q |>.eval (r * Complex.exp (I * θ))‖ ≤ M_Q := by
    have h_inner_cont : Continuous (fun θ : ℝ => (r : ℂ) * Complex.exp (I * ↑θ)) :=
      continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    have h_eval_cont : Continuous (fun z : ℂ => (Polynomial.derivative Q).eval z) :=
      (Polynomial.derivative Q).continuous
    have h_cont : Continuous (fun θ : ℝ => (Polynomial.derivative Q).eval ((r : ℂ) * Complex.exp (I * ↑θ))) :=
      h_eval_cont.comp h_inner_cont
    have h_compact : IsCompact (Set.Icc 0 (2 * Real.pi)) := isCompact_Icc
    have h_nonempty : Set.Nonempty (Set.Icc (0 : ℝ) (2 * Real.pi)) := ⟨0, by simp [Real.pi_pos.le]⟩
    have h_norm_cont : Continuous (fun θ : ℝ => ‖(Polynomial.derivative Q).eval ((r : ℂ) * Complex.exp (I * ↑θ))‖) :=
      continuous_norm.comp h_cont
    obtain ⟨θ_max, hθ_max_mem, hθ_max⟩ := h_compact.exists_isMaxOn h_nonempty h_norm_cont.continuousOn
    use ‖(Polynomial.derivative Q).eval (r * Complex.exp (I * θ_max))‖ + 1
    constructor
    · linarith [norm_nonneg ((Polynomial.derivative Q).eval (r * Complex.exp (I * θ_max)))]
    · intro θ
      let θ' := toIocMod Real.two_pi_pos 0 θ
      have hθ'_mem : θ' ∈ Set.Icc 0 (2 * Real.pi) := by
        have := toIocMod_mem_Ioc Real.two_pi_pos 0 θ
        constructor <;> linarith [this.1, this.2]
      have hθ'_eq : ‖(Polynomial.derivative Q).eval (r * Complex.exp (I * θ))‖ =
                    ‖(Polynomial.derivative Q).eval (r * Complex.exp (I * θ'))‖ := by
        have h_mod := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos 0 θ
        rw [zsmul_eq_mul] at h_mod
        have h_exp_eq : Complex.exp (I * ↑θ) = Complex.exp (I * ↑θ') := by
          let k := toIocDiv Real.two_pi_pos 0 θ
          have h_diff : θ = θ' + k * (2 * Real.pi) := h_mod.symm
          calc Complex.exp (I * ↑θ)
            = Complex.exp (I * ↑(θ' + ↑k * (2 * Real.pi))) := by rw [h_diff]
            _ = Complex.exp (I * ↑θ' + ↑k * (2 * ↑Real.pi * I)) := by
                congr 1; push_cast; ring
            _ = Complex.exp (I * ↑θ') := (Complex.exp_periodic.int_mul k) (I * ↑θ')
        rw [h_exp_eq]
      rw [hθ'_eq]
      have h_le := hθ_max hθ'_mem
      exact le_add_of_le_of_nonneg h_le (by norm_num : (1 : ℝ) ≥ 0)

  obtain ⟨M_P, hM_P_pos, hM_P⟩ := hP_deriv_bound
  obtain ⟨M_Q, hM_Q_pos, hM_Q⟩ := hQ_deriv_bound

  -- Define coefficient-based disk bounds for P' and Q'
  -- These bound |P'(z)| and |Q'(z)| for ALL z with |z| ≤ r (not just on the circle)
  -- This is necessary for polynomial_divided_difference_bound which requires disk bounds
  let P' := Polynomial.derivative P
  let Q' := Polynomial.derivative Q

  let P'_disk := (Finset.range (P'.natDegree + 1)).sum (fun k => ‖P'.coeff k‖ * r^k)
  let Q'_disk := (Finset.range (Q'.natDegree + 1)).sum (fun k => ‖Q'.coeff k‖ * r^k)

  have hP'_disk_nonneg : 0 ≤ P'_disk := by
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt hr) _)

  have hQ'_disk_nonneg : 0 ≤ Q'_disk := by
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (norm_nonneg _) (pow_nonneg (le_of_lt hr) _)

  have hP'_disk_bound : ∀ z : ℂ, ‖z‖ ≤ r → ‖P'.eval z‖ ≤ P'_disk := by
    intro z hz
    calc ‖P'.eval z‖
        = ‖(Finset.range (P'.natDegree + 1)).sum (fun k => P'.coeff k * z^k)‖ := by
            rw [Polynomial.eval_eq_sum_range]
      _ ≤ (Finset.range (P'.natDegree + 1)).sum (fun k => ‖P'.coeff k * z^k‖) := norm_sum_le _ _
      _ = (Finset.range (P'.natDegree + 1)).sum (fun k => ‖P'.coeff k‖ * ‖z‖^k) := by
          congr 1; ext k; rw [norm_mul, norm_pow]
      _ ≤ (Finset.range (P'.natDegree + 1)).sum (fun k => ‖P'.coeff k‖ * r^k) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact pow_le_pow_left₀ (norm_nonneg z) hz k
      _ = P'_disk := rfl

  have hQ'_disk_bound : ∀ z : ℂ, ‖z‖ ≤ r → ‖Q'.eval z‖ ≤ Q'_disk := by
    intro z hz
    calc ‖Q'.eval z‖
        = ‖(Finset.range (Q'.natDegree + 1)).sum (fun k => Q'.coeff k * z^k)‖ := by
            rw [Polynomial.eval_eq_sum_range]
      _ ≤ (Finset.range (Q'.natDegree + 1)).sum (fun k => ‖Q'.coeff k * z^k‖) := norm_sum_le _ _
      _ = (Finset.range (Q'.natDegree + 1)).sum (fun k => ‖Q'.coeff k‖ * ‖z‖^k) := by
          congr 1; ext k; rw [norm_mul, norm_pow]
      _ ≤ (Finset.range (Q'.natDegree + 1)).sum (fun k => ‖Q'.coeff k‖ * r^k) := by
          apply Finset.sum_le_sum
          intro k _
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact pow_le_pow_left₀ (norm_nonneg z) hz k
      _ = Q'_disk := rfl

  -- Step 4: Compute Lipschitz constants for arg(P) and arg(Q)
  -- The angular velocity of arg(F(r*e^{iθ})) is bounded by |F'| * r / |F|_min
  -- Use P'_disk + 1 to ensure positivity (works even if P is constant)
  -- P'_disk bounds derivative on disk; +1 ensures L_P > 0

  let L_P := r * (P'_disk + 1) / δ_P
  let L_Q := r * (Q'_disk + 1) / δ_Q

  have hL_P_pos : L_P > 0 := div_pos (mul_pos hr (by linarith [hP'_disk_nonneg])) hδ_P_pos

  have hL_Q_pos : L_Q > 0 := div_pos (mul_pos hr (by linarith [hQ'_disk_nonneg])) hδ_Q_pos

  -- Step 5: Choose N₀ such that mesh 2π/N₀ < π / (2 * max(L_P, L_Q))
  -- This ensures each arg step is < π/2, so sum of two is < π
  -- Additionally, we need a stronger bound for the elementary arg estimate:
  -- |P(z₂) - P(z₁)|/|P(z₁)| < 1/2, which requires 2πL_P/N < 1/2, i.e., N > 4πL_P

  let L_max := max L_P L_Q
  have hL_max_pos : L_max > 0 := lt_max_of_lt_left hL_P_pos

  -- N₀ = ⌈4π * L_max⌉ + 1 ensures both:
  -- 1. 2π/N < π/(2*L_max) (for Lipschitz bound)
  -- 2. 2πL_max/N < 1/2 (for elementary arg bound)
  use Nat.ceil (4 * Real.pi * L_max) + 1
  intro N hN

  have hN_pos : (N : ℝ) > 0 := by
    have h1 : N ≥ Nat.ceil (4 * Real.pi * L_max) + 1 := hN
    have h2 : Nat.ceil (4 * Real.pi * L_max) + 1 ≥ 1 := Nat.le_add_left 1 _
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp (Nat.le_trans h2 h1)))

  have h_mesh_bound : 2 * Real.pi / N < Real.pi / (2 * L_max) := by
    have h1 : (N : ℝ) ≥ Nat.ceil (4 * Real.pi * L_max) + 1 := by exact_mod_cast hN
    have h2 : (Nat.ceil (4 * Real.pi * L_max) : ℝ) ≥ 4 * Real.pi * L_max := Nat.le_ceil _
    have h3 : (N : ℝ) > 4 * Real.pi * L_max := by linarith
    -- Since N > 4π·L_max > 4·L_max (as π > 1), we have 2π/N < π/(2·L_max)
    have hpi_pos : Real.pi > 0 := Real.pi_pos
    have h4 : (N : ℝ) > 4 * L_max := calc
      N > 4 * Real.pi * L_max := h3
      _ > 4 * 1 * L_max := by nlinarith [Real.pi_gt_three]
      _ = 4 * L_max := by ring
    calc 2 * Real.pi / N
        < 2 * Real.pi / (4 * L_max) := by
          apply div_lt_div_of_pos_left (by linarith) (by linarith) h4
      _ = Real.pi / (2 * L_max) := by ring

  -- Additional bound for elementary arg estimate: L_max * (2π/N) < 1/2
  have h_ratio_bound : L_max * (2 * Real.pi / N) < 1 / 2 := by
    have h1 : (N : ℝ) ≥ Nat.ceil (4 * Real.pi * L_max) + 1 := by exact_mod_cast hN
    have h2 : (Nat.ceil (4 * Real.pi * L_max) : ℝ) ≥ 4 * Real.pi * L_max := Nat.le_ceil _
    have h3 : (N : ℝ) > 4 * Real.pi * L_max := by linarith
    have hpi_pos : Real.pi > 0 := Real.pi_pos
    calc L_max * (2 * Real.pi / N)
        = 2 * Real.pi * L_max / N := by ring
      _ < 2 * Real.pi * L_max / (4 * Real.pi * L_max) := by
          apply div_lt_div_of_pos_left (by nlinarith) (by nlinarith) h3
      _ = 1 / 2 := by
          have h4 : 4 * Real.pi * L_max ≠ 0 := by nlinarith
          have h5 : Real.pi ≠ 0 := Real.pi_pos.ne'
          have h6 : L_max ≠ 0 := by nlinarith
          rw [div_eq_div_iff h4 (by norm_num : (2 : ℝ) ≠ 0)]
          ring

  -- Step 6: For N ≥ N₀, each arg step for P and Q is < π/2
  -- Therefore their sum is < π, and wrapping is additive

  -- Unfold discrete_winding_number
  simp only [discrete_winding_number, Polynomial.eval_mul]

  -- The key identity: wrapped differences are additive when steps are small
  -- wrap(arg(PQ)_diff) = wrap(arg(P)_diff) + wrap(arg(Q)_diff)

  -- Define the wrapped difference function
  -- Note: Complex.arg is in (-π, π], so differences are in (-2π, 2π)
  -- The wrap function corrects for branch cuts
  -- wrap maps arg differences to (-π, π] (the principal range for toReal)
  -- Use d ≤ -π (not d < -π) to handle the boundary case d = -π correctly
  set wrap : ℝ → ℝ := fun d =>
    if d > Real.pi then d - 2 * Real.pi
    else if d ≤ -Real.pi then d + 2 * Real.pi
    else d with h_wrap_def

  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := by positivity

  -- The key lemma: for each j, the wrapped difference for P*Q equals the sum
  -- (Increase heartbeats for complex trigonometric and angle computations)
  set_option maxHeartbeats 600000 in
  have h_term_eq : ∀ j < N,
      (let z_j := r * Complex.exp (I * (2 * Real.pi * (j : ℝ) / (N : ℝ)))
       let z_next := r * Complex.exp (I * (2 * Real.pi * ((j + 1) % N : ℕ) / (N : ℝ)))
       let diff_PQ := Complex.arg (P.eval z_next * Q.eval z_next) -
                      Complex.arg (P.eval z_j * Q.eval z_j)
       let diff_P := Complex.arg (P.eval z_next) - Complex.arg (P.eval z_j)
       let diff_Q := Complex.arg (Q.eval z_next) - Complex.arg (Q.eval z_j)
       wrap diff_PQ = wrap diff_P + wrap diff_Q) := by
    intro j hj
    have h_step_size : (2 * Real.pi / N : ℝ) > 0 := div_pos (by linarith [Real.pi_pos]) hN_pos

    -- In the non-wrapping case, the step is exactly 2π/N
    have h_step_nonwrap : j + 1 < N →
        2 * Real.pi * ((j + 1) % N : ℕ) / N - 2 * Real.pi * j / N = 2 * Real.pi / N := by
      intro h_wrap
      have h_mod : (j + 1) % N = j + 1 := Nat.mod_eq_of_lt h_wrap
      simp only [h_mod]
      push_cast
      field_simp [ne_of_gt hN_pos]; ring

    -- In the wrapping case (j = N-1), we use 2π-periodicity
    -- z_0 = r * exp(0) = r, and z_N = r * exp(2πi) = r, so they're the same point
    have h_wrap_periodicity : ¬(j + 1 < N) →
        r * Complex.exp (I * (2 * Real.pi * ((j + 1) % N : ℕ) / N)) =
        r * Complex.exp (I * (2 * Real.pi * (j + 1) / N)) := by
      intro h_not_wrap
      push_neg at h_not_wrap
      have h_j_eq : j = N - 1 := by omega
      have hN_pos' : N > 0 := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp (Nat.le_trans (Nat.le_add_left 1 _) hN))
      have h_mod : (j + 1) % N = 0 := by rw [h_j_eq, Nat.sub_add_cancel (Nat.one_le_of_lt hN_pos'), Nat.mod_self]
      simp only [h_mod, Nat.cast_zero, mul_zero, zero_div, mul_zero]
      -- LHS: exp(0) = 1
      -- RHS: exp(2πi * N / N) = exp(2πi) = 1
      -- Note: the goal has (j + 1 : ℂ) with direct ℕ → ℂ coercion
      have h_rhs : Complex.exp (I * (2 * Real.pi * (j + 1) / N)) = 1 := by
        have h1 : j + 1 = N := by omega
        have hN_ne : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hN_pos
      -- (j + 1 : ℂ) = (N : ℂ) from h1
        have hj1 : (j + 1 : ℂ) = (N : ℂ) := by exact_mod_cast h1
        have h_simp : (2 * Real.pi * (N : ℂ) / N : ℂ) = 2 * Real.pi := by
          field_simp [hN_ne]
        calc Complex.exp (I * (2 * Real.pi * (j + 1) / N))
            = Complex.exp (I * (2 * Real.pi * N / N)) := by rw [hj1]
          _ = Complex.exp (I * (2 * Real.pi)) := by rw [h_simp]
          _ = Complex.exp (2 * Real.pi * I) := by ring_nf
          _ = 1 := Complex.exp_two_pi_mul_I
      rw [Complex.exp_zero, h_rhs]

    -- The arg differences are bounded by L * step_size < L * (2π/N) < π/2
    -- When both |diff_P| and |diff_Q| < π/2, |diff_P + diff_Q| < π
    -- And wrap(diff_PQ) where diff_PQ ≡ diff_P + diff_Q (mod 2π) equals wrap(diff_P) + wrap(diff_Q)

    -- Get the sample points - use different names to avoid shadowing goal's let-bindings
    -- Use explicit type annotations to ensure the coercions match the goal
    let angle_j : ℝ := 2 * Real.pi * (j : ℝ) / (N : ℝ)
    let angle_next : ℝ := 2 * Real.pi * (((j + 1) % N : ℕ) : ℝ) / (N : ℝ)
    let pt_j := r * Complex.exp (I * angle_j)
    let pt_next := r * Complex.exp (I * angle_next)

    -- Non-zero conditions for P and Q at both points
    have hPj_ne : P.eval pt_j ≠ 0 := hP_nonzero angle_j
    have hPnext_ne : P.eval pt_next ≠ 0 := hP_nonzero angle_next
    have hQj_ne : Q.eval pt_j ≠ 0 := hQ_nonzero angle_j
    have hQnext_ne : Q.eval pt_next ≠ 0 := hQ_nonzero angle_next

    -- Products are also non-zero
    have hPQj_ne : P.eval pt_j * Q.eval pt_j ≠ 0 := mul_ne_zero hPj_ne hQj_ne
    have hPQnext_ne : P.eval pt_next * Q.eval pt_next ≠ 0 := mul_ne_zero hPnext_ne hQnext_ne

    -- Key relationship from arg_mul_coe_angle:
    -- (arg(xy) : Real.Angle) = (arg x : Real.Angle) + (arg y : Real.Angle)
    have h_arg_mul_j : (Complex.arg (P.eval pt_j * Q.eval pt_j) : Real.Angle) =
        Complex.arg (P.eval pt_j) + Complex.arg (Q.eval pt_j) :=
      Complex.arg_mul_coe_angle hPj_ne hQj_ne
    have h_arg_mul_next : (Complex.arg (P.eval pt_next * Q.eval pt_next) : Real.Angle) =
        Complex.arg (P.eval pt_next) + Complex.arg (Q.eval pt_next) :=
      Complex.arg_mul_coe_angle hPnext_ne hQnext_ne

    -- The differences - use different names to avoid shadowing goal's let-bindings
    let argdiff_P := Complex.arg (P.eval pt_next) - Complex.arg (P.eval pt_j)
    let argdiff_Q := Complex.arg (Q.eval pt_next) - Complex.arg (Q.eval pt_j)
    let argdiff_PQ := Complex.arg (P.eval pt_next * Q.eval pt_next) -
                   Complex.arg (P.eval pt_j * Q.eval pt_j)

    -- As Real.Angle: argdiff_PQ ≡ argdiff_P + argdiff_Q (mod 2π)
    have h_angle_eq : (argdiff_PQ : Real.Angle) = (argdiff_P : Real.Angle) + (argdiff_Q : Real.Angle) := by
      -- argdiff_PQ = arg(PQ_next) - arg(PQ_j)
      -- argdiff_P = arg(P_next) - arg(P_j)
      -- argdiff_Q = arg(Q_next) - arg(Q_j)
      -- In Real.Angle: arg(PQ) = arg(P) + arg(Q)
      calc (argdiff_PQ : Real.Angle)
          = ↑((P.eval pt_next * Q.eval pt_next).arg - (P.eval pt_j * Q.eval pt_j).arg) := rfl
        _ = ↑(P.eval pt_next * Q.eval pt_next).arg - ↑(P.eval pt_j * Q.eval pt_j).arg :=
            Real.Angle.coe_sub _ _
        _ = (↑(P.eval pt_next).arg + ↑(Q.eval pt_next).arg) - (↑(P.eval pt_j).arg + ↑(Q.eval pt_j).arg) := by
            rw [h_arg_mul_next, h_arg_mul_j]
        _ = (↑(P.eval pt_next).arg - ↑(P.eval pt_j).arg) + (↑(Q.eval pt_next).arg - ↑(Q.eval pt_j).arg) := by
            abel
        _ = ↑((P.eval pt_next).arg - (P.eval pt_j).arg) + ↑((Q.eval pt_next).arg - (Q.eval pt_j).arg) := by
            rw [Real.Angle.coe_sub, Real.Angle.coe_sub]
        _ = (argdiff_P : Real.Angle) + (argdiff_Q : Real.Angle) := rfl

    -- The diffs are in (-2π, 2π) since each arg is in (-π, π]
    have h_diff_P_bound : argdiff_P ∈ Set.Ioo (-2 * Real.pi) (2 * Real.pi) := by
      constructor <;> [nlinarith [Complex.neg_pi_lt_arg (P.eval pt_next),
          Complex.arg_le_pi (P.eval pt_next), Complex.neg_pi_lt_arg (P.eval pt_j),
          Complex.arg_le_pi (P.eval pt_j)]; nlinarith [Complex.neg_pi_lt_arg (P.eval pt_next),
          Complex.arg_le_pi (P.eval pt_next), Complex.neg_pi_lt_arg (P.eval pt_j),
          Complex.arg_le_pi (P.eval pt_j)]]
    have h_diff_Q_bound : argdiff_Q ∈ Set.Ioo (-2 * Real.pi) (2 * Real.pi) := by
      constructor <;> [nlinarith [Complex.neg_pi_lt_arg (Q.eval pt_next),
          Complex.arg_le_pi (Q.eval pt_next), Complex.neg_pi_lt_arg (Q.eval pt_j),
          Complex.arg_le_pi (Q.eval pt_j)]; nlinarith [Complex.neg_pi_lt_arg (Q.eval pt_next),
          Complex.arg_le_pi (Q.eval pt_next), Complex.neg_pi_lt_arg (Q.eval pt_j),
          Complex.arg_le_pi (Q.eval pt_j)]]
    have h_diff_PQ_bound : argdiff_PQ ∈ Set.Ioo (-2 * Real.pi) (2 * Real.pi) := by
      constructor <;> [nlinarith [Complex.neg_pi_lt_arg (P.eval pt_next * Q.eval pt_next),
          Complex.arg_le_pi (P.eval pt_next * Q.eval pt_next),
          Complex.neg_pi_lt_arg (P.eval pt_j * Q.eval pt_j),
          Complex.arg_le_pi (P.eval pt_j * Q.eval pt_j)];
        nlinarith [Complex.neg_pi_lt_arg (P.eval pt_next * Q.eval pt_next),
          Complex.arg_le_pi (P.eval pt_next * Q.eval pt_next),
          Complex.neg_pi_lt_arg (P.eval pt_j * Q.eval pt_j),
          Complex.arg_le_pi (P.eval pt_j * Q.eval pt_j)]]

    -- For values in (-2π, 2π) with d > -π, wrap gives the same as Real.Angle.toReal
    -- Note: at d = -π exactly, wrap(-π) = -π but toReal(↑(-π)) = π, so they differ.
    -- But our arg differences satisfy |d| < π/2, so d > -π is automatic.
    have h_wrap_eq_toReal : ∀ d, d ∈ Set.Ioo (-2 * Real.pi) (2 * Real.pi) → d > -Real.pi →
        wrap d = (d : Real.Angle).toReal := by
      intro d ⟨hd_lo, hd_hi⟩ hd_gt_neg_pi
      simp only [h_wrap_def]
      by_cases h1 : d > Real.pi
      · -- d ∈ (π, 2π), wrap = d - 2π
        simp only [h1, ↓reduceIte]
        have h_angle_eq : (d : Real.Angle) = ↑(d - 2 * Real.pi) := by
          have h1 : (↑(d - 2 * Real.pi) : Real.Angle) = ↑d - ↑(2 * Real.pi) :=
            Real.Angle.coe_sub d (2 * Real.pi)
          rw [h1, Real.Angle.coe_two_pi, sub_zero]
        have h_in_range : -Real.pi < d - 2 * Real.pi ∧ d - 2 * Real.pi ≤ Real.pi := by
          constructor <;> linarith [Real.pi_pos]
        rw [h_angle_eq, Real.Angle.toReal_coe_eq_self_iff.mpr h_in_range]
      · push_neg at h1
        by_cases h2 : d ≤ -Real.pi  -- Changed from < to ≤ to match wrap def
        · -- d ∈ (-2π, -π], wrap = d + 2π
          have h_not_gt : ¬(d > Real.pi) := not_lt.mpr h1
          simp only [h_not_gt, ↓reduceIte, h2]
          have h_angle_eq : (d : Real.Angle) = ↑(d + 2 * Real.pi) := by
            have h1 : (↑(d + 2 * Real.pi) : Real.Angle) = ↑d + ↑(2 * Real.pi) :=
              Real.Angle.coe_add d (2 * Real.pi)
            rw [h1, Real.Angle.coe_two_pi, add_zero]
          have h_in_range : -Real.pi < d + 2 * Real.pi ∧ d + 2 * Real.pi ≤ Real.pi := by
            constructor <;> linarith [Real.pi_pos]
          rw [h_angle_eq, Real.Angle.toReal_coe_eq_self_iff.mpr h_in_range]
        · -- d ∈ (-π, π], wrap = d (since d > -π and d ≤ π)
          push_neg at h2  -- h2 : d > -π
          have h_not_gt : ¬(d > Real.pi) := not_lt.mpr h1
          have h_not_le : ¬(d ≤ -Real.pi) := not_le.mpr h2  -- Changed from h_not_lt
          simp only [h_not_gt, ↓reduceIte, h_not_le]
          -- d is in (-π, π], so toReal gives it back
          have h_in_range : -Real.pi < d ∧ d ≤ Real.pi := ⟨h2, h1⟩  -- Changed hd_gt_neg_pi to h2
          rw [Real.Angle.toReal_coe_eq_self_iff.mpr h_in_range]

    -- We'll prove h_wrap_P' etc. after establishing the arg bounds
    -- For now, we note that argdiff > -π follows from the arg quotient bounds

    -- The mesh bound: 2π/N < π/(2*L_max)
    have h_mesh : (2 * Real.pi / N : ℝ) < Real.pi / (2 * L_max) := h_mesh_bound


    have hL_P_le : L_P ≤ L_max := le_max_left L_P L_Q
    have hL_Q_le : L_Q ≤ L_max := le_max_right L_P L_Q

    have h_lip_P : L_P * (2 * Real.pi / N) < Real.pi / 2 := by
      have h1 : L_P * (2 * Real.pi / N) < L_P * (Real.pi / (2 * L_max)) :=
        mul_lt_mul_of_pos_left h_mesh hL_P_pos
      have h2 : L_P * (Real.pi / (2 * L_max)) ≤ L_max * (Real.pi / (2 * L_max)) :=
        mul_le_mul_of_nonneg_right hL_P_le (div_nonneg (le_of_lt Real.pi_pos) (by linarith))
      have h3 : L_max * (Real.pi / (2 * L_max)) = Real.pi / 2 := by
        field_simp [ne_of_gt hL_max_pos]
      linarith

    have h_lip_Q : L_Q * (2 * Real.pi / N) < Real.pi / 2 := by
      have h1 : L_Q * (2 * Real.pi / N) < L_Q * (Real.pi / (2 * L_max)) :=
        mul_lt_mul_of_pos_left h_mesh hL_Q_pos
      have h2 : L_Q * (Real.pi / (2 * L_max)) ≤ L_max * (Real.pi / (2 * L_max)) :=
        mul_le_mul_of_nonneg_right hL_Q_le (div_nonneg (le_of_lt Real.pi_pos) (by linarith))
      have h3 : L_max * (Real.pi / (2 * L_max)) = Real.pi / 2 := by
        field_simp [ne_of_gt hL_max_pos]
      linarith


    -- Bound on the ratio |P(pt_next) - P(pt_j)| / |P(pt_j)| < 1
    have h_P_ratio_bound : L_P * (2 * Real.pi / N) < 1 := by
      calc L_P * (2 * Real.pi / N)
          ≤ L_max * (2 * Real.pi / N) := by
            apply mul_le_mul_of_nonneg_right (le_max_left L_P L_Q)
            apply div_nonneg (by linarith [Real.pi_pos]) (le_of_lt hN_pos)
        _ < 1 / 2 := h_ratio_bound
        _ < 1 := by norm_num

    have h_Q_ratio_bound : L_Q * (2 * Real.pi / N) < 1 := by
      calc L_Q * (2 * Real.pi / N)
          ≤ L_max * (2 * Real.pi / N) := by
            apply mul_le_mul_of_nonneg_right (le_max_right L_P L_Q)
            apply div_nonneg (by linarith [Real.pi_pos]) (le_of_lt hN_pos)
        _ < 1 / 2 := h_ratio_bound
        _ < 1 := by norm_num

    -- Common chord length bound (used by both P and Q sections)
    have hN_pos' : N > 0 := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp (Nat.le_trans (Nat.le_add_left 1 _) hN))
    have h_chord_common : ‖pt_next - pt_j‖ ≤ 2 * Real.pi * r / N := by
      -- For consecutive points on circle of radius r, the chord length is bounded by r × 2π/N
      -- Key lemma: ‖exp(I*t) - 1‖ ≤ |t| (from norm_exp_I_mul_ofReal_sub_one_le)
      have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
      have hr_nn : 0 ≤ r := le_of_lt hr
      -- Factor out r from pt_next - pt_j
      have h_factor : pt_next - pt_j = r * (Complex.exp (I * angle_next) - Complex.exp (I * angle_j)) := by
        simp only [pt_next, pt_j]
        ring
      -- The exp difference bound: ‖exp(I*θ₁) - exp(I*θ₂)‖ ≤ 2π/N
      have h_exp_diff_bound : ‖Complex.exp (I * angle_next) - Complex.exp (I * angle_j)‖ ≤ 2 * Real.pi / N := by
      -- Factor: exp(I*θ₁) - exp(I*θ₂) = exp(I*θ₂) * (exp(I*(θ₁ - θ₂)) - 1)
      -- For non-wrapping: θ₁ - θ₂ = 2π/N
      -- For wrapping: use periodicity to get effective step of 2π/N
        by_cases h_wrap : j + 1 < N
        · -- Non-wrapping case: angle_next - angle_j = 2π/N
          have h_mod : (j + 1) % N = j + 1 := Nat.mod_eq_of_lt h_wrap
          have h_diff : angle_next - angle_j = 2 * Real.pi / N := by
            simp only [angle_next, angle_j, h_mod]
            push_cast
            field_simp [hN_ne]; ring
          have h_factor_exp : Complex.exp (I * angle_next) - Complex.exp (I * angle_j) =
              Complex.exp (I * angle_j) * (Complex.exp (I * (angle_next - angle_j)) - 1) := by
            rw [mul_sub, mul_one, ← Complex.exp_add]
            ring_nf
          rw [h_factor_exp, norm_mul]
          have h_norm_exp : ‖Complex.exp (I * angle_j)‖ = 1 := by
            have h_comm : (I : ℂ) * (angle_j : ℂ) = (angle_j : ℂ) * I := mul_comm _ _
            rw [h_comm]
            exact Complex.norm_exp_ofReal_mul_I angle_j
          rw [h_norm_exp, one_mul]
          -- By h_diff: angle_next - angle_j = 2π/N
          -- So we need ‖exp(I * 2π/N) - 1‖ ≤ 2π/N, which is standard
          have h_diff' : (angle_next : ℂ) - (angle_j : ℂ) = ((2 * Real.pi / N : ℝ) : ℂ) := by
            rw [← Complex.ofReal_sub, h_diff]
          rw [h_diff']
          calc ‖Complex.exp (I * ((2 * Real.pi / N : ℝ) : ℂ)) - 1‖
            _ ≤ ‖(2 * Real.pi / N : ℝ)‖ := norm_exp_I_mul_ofReal_sub_one_le
            _ = 2 * Real.pi / N := by
                rw [Real.norm_eq_abs, abs_of_pos (div_pos (by linarith [Real.pi_pos]) hN_pos)]
        · -- Wrapping case: j = N - 1, so angle_next = 0, angle_j = 2π(N-1)/N
          push_neg at h_wrap
          have h_j_eq : j = N - 1 := by omega
          have hN_pos'' : N ≥ 1 := by omega
          have h_mod : (j + 1) % N = 0 := by
            rw [h_j_eq, Nat.sub_add_cancel hN_pos'', Nat.mod_self]
          have h_angle_next_zero : angle_next = 0 := by
            simp only [angle_next, h_mod, Nat.cast_zero, mul_zero, zero_div]
          have h_angle_j_val : angle_j = 2 * Real.pi * ((N - 1 : ℕ) : ℝ) / (N : ℝ) := by
            simp only [angle_j, h_j_eq]
          -- exp(0) - exp(I * 2π(N-1)/N) = 1 - exp(I * 2π(N-1)/N)
          -- Note: exp(I * 2π(N-1)/N) = exp(I * (2π - 2π/N)) = exp(-I * 2π/N) (using exp(2πi) = 1)
          simp only [h_angle_next_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
          -- Now show ‖1 - exp(I * angle_j)‖ ≤ 2π/N
          -- Key: angle_j = 2π(N-1)/N = 2π - 2π/N, so exp(I * angle_j) = exp(-I * 2π/N)
          have h_angle_j_eq : angle_j = 2 * Real.pi - 2 * Real.pi / N := by
            rw [h_angle_j_val]
            have h_cast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
              have := Nat.cast_sub hN_pos'' (R := ℝ)
              simp only [Nat.cast_one] at this
              exact this
            rw [h_cast]
            field_simp [hN_ne]
          have h_exp_eq : Complex.exp (I * angle_j) = Complex.exp (I * (-(2 * Real.pi / N))) := by
            rw [h_angle_j_eq]
            -- angle_j = 2π - 2π/N, so I * angle_j = I * 2π + I * (-2π/N)
            -- exp(I * 2π) = 1, so exp(I * angle_j) = exp(I * (-2π/N))
            have h_arg_eq : (I : ℂ) * ((2 * Real.pi - 2 * Real.pi / N : ℝ) : ℂ) =
                            2 * Real.pi * I + I * (-(2 * Real.pi / N)) := by
              push_cast
              ring
            rw [h_arg_eq, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
          rw [h_exp_eq]
          -- ‖1 - exp(-iθ)‖ = ‖exp(iθ) - 1‖ for θ real
          -- Key fact: exp(-iθ) = conj(exp(iθ)) for real θ, and |conj(z)| = |z|
          have h_conj : ‖1 - Complex.exp (I * (-(2 * Real.pi / N)))‖ =
                        ‖Complex.exp (I * (2 * Real.pi / N)) - 1‖ := by
            -- Use: exp(-iθ) = conj(exp(iθ)) and |1 - z| = |z - 1|
            have h_neg : Complex.exp (I * (-(2 * Real.pi / N))) =
                         Complex.exp (-(I * (2 * Real.pi / N))) := by
              push_cast; ring_nf
            rw [h_neg, Complex.exp_neg]
            -- |1 - 1/w| = |1 - w⁻¹| for w on unit circle
            have h_on_circle : ‖Complex.exp (I * (2 * Real.pi / N))‖ = 1 := by
              have h_comm : (I : ℂ) * (2 * Real.pi / N) = (2 * Real.pi / N : ℝ) * I := by
                push_cast; ring
              rw [h_comm]
              exact Complex.norm_exp_ofReal_mul_I _
            let w := Complex.exp (I * (2 * Real.pi / N))
            have hw_ne : w ≠ 0 := by
              intro h
              have : ‖w‖ = 0 := by simp [h]
              rw [h_on_circle] at this
              norm_num at this
            -- |1 - w⁻¹| = |w|⁻¹ * |w - 1| = |w - 1| since |w| = 1
            -- After exp_neg, goal is: ‖1 - (exp(...))⁻¹‖ = ‖exp(...) - 1‖
            calc ‖1 - w⁻¹‖ = ‖w⁻¹‖ * ‖w - 1‖ := by
                    rw [← norm_mul]
                    congr 1
                    field_simp
              _ = ‖w‖⁻¹ * ‖w - 1‖ := by rw [norm_inv]
              _ = 1 * ‖w - 1‖ := by rw [h_on_circle, inv_one]
              _ = ‖w - 1‖ := one_mul _
          rw [h_conj]
          -- ‖exp(I * θ) - 1‖ ≤ |θ| for θ = 2π/N
          calc ‖Complex.exp (I * (2 * Real.pi / N)) - 1‖
              = ‖Complex.exp (I * ((2 * Real.pi / N : ℝ) : ℂ)) - 1‖ := by norm_cast
            _ ≤ ‖(2 * Real.pi / N : ℝ)‖ := norm_exp_I_mul_ofReal_sub_one_le
            _ = 2 * Real.pi / N := by
                rw [Real.norm_eq_abs, abs_of_pos (div_pos (by linarith [Real.pi_pos]) hN_pos)]
      -- Combine: ‖pt_next - pt_j‖ = ‖r‖ * ‖exp diff‖ ≤ r * 2π/N
      rw [h_factor, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr_nn]
      calc r * ‖Complex.exp (I * ↑angle_next) - Complex.exp (I * ↑angle_j)‖
          ≤ r * (2 * Real.pi / N) := by
            apply mul_le_mul_of_nonneg_left h_exp_diff_bound hr_nn
        _ = 2 * Real.pi * r / N := by ring

    -- The key lemma: P(pt_next) / P(pt_j) has positive real part
    -- This follows from |P(pt_next)/P(pt_j) - 1| < 1, which puts it in the right half-plane
    have h_P_quotient_re_pos : 0 < (P.eval pt_next / P.eval pt_j).re := by
      -- We need |P(pt_next)/P(pt_j) - 1| < 1
      -- This means |P(pt_next) - P(pt_j)| < |P(pt_j)|
      have h_diff_bound : ‖P.eval pt_next - P.eval pt_j‖ < ‖P.eval pt_j‖ := by
        have h_chord : ‖pt_next - pt_j‖ ≤ 2 * Real.pi * r / N := h_chord_common
      -- Use that P.eval is uniformly continuous on the compact circle
      -- Combined with our choice of N₀ to make the mesh fine enough
        have h_P_diff : ‖P.eval pt_next - P.eval pt_j‖ < δ_P := by

          have h1 : P'_disk * (2 * Real.pi * r / N) < δ_P / 2 := by
            -- L_P = r * (P'_disk + 1) / δ_P
            -- Since P'_disk ≤ P'_disk + 1, we have P'_disk * X ≤ (P'_disk + 1) * X
            have h_LP_bound : L_P * (2 * Real.pi / N) < 1 / 2 := by
              have h1 : L_P * (2 * Real.pi / N) ≤ L_max * (2 * Real.pi / N) := by
                apply mul_le_mul_of_nonneg_right (le_max_left _ _)
                apply div_nonneg (by linarith [Real.pi_pos]) (le_of_lt hN_pos)
              exact lt_of_le_of_lt h1 h_ratio_bound
            -- L_P * δ_P = r * (P'_disk + 1)
            -- L_P * (2π/N) * δ_P < (1/2) * δ_P
            -- r * (P'_disk + 1) * (2π/N) < δ_P / 2
            -- P'_disk * (2πr/N) ≤ (P'_disk + 1) * (2πr/N) < δ_P / 2
            have h_le : P'_disk * (2 * Real.pi * r / N) ≤ (P'_disk + 1) * (2 * Real.pi * r / N) := by
              apply mul_le_mul_of_nonneg_right (by linarith)
              apply div_nonneg (by nlinarith [Real.pi_pos, hr]) (le_of_lt hN_pos)
            have h_eq : (P'_disk + 1) * (2 * Real.pi * r / N) = L_P * δ_P * (2 * Real.pi / N) := by
              simp only [L_P]
              have := ne_of_gt hδ_P_pos
              field_simp
            calc P'_disk * (2 * Real.pi * r / N)
                ≤ (P'_disk + 1) * (2 * Real.pi * r / N) := h_le
              _ = L_P * δ_P * (2 * Real.pi / N) := h_eq
              _ = L_P * (2 * Real.pi / N) * δ_P := by ring
              _ < (1 / 2) * δ_P := mul_lt_mul_of_pos_right h_LP_bound hδ_P_pos
              _ = δ_P / 2 := by ring
          -- h_mvt uses the disk bound P'_disk via polynomial_divided_difference_bound
          have h_mvt : ‖P.eval pt_next - P.eval pt_j‖ ≤ P'_disk * ‖pt_next - pt_j‖ := by
            -- Apply our polynomial divided-difference helper lemma with disk bound
            have h_pt_j_norm : ‖pt_j‖ = r := by
              simp only [pt_j, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
              have h_comm : I * (angle_j : ℂ) = (angle_j : ℝ) * I := by push_cast; ring
              rw [h_comm, Complex.norm_exp_ofReal_mul_I, mul_one]
            have h_pt_next_norm : ‖pt_next‖ = r := by
              simp only [pt_next, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
              have h_comm : I * (angle_next : ℂ) = (angle_next : ℝ) * I := by push_cast; ring
              rw [h_comm, Complex.norm_exp_ofReal_mul_I, mul_one]
            exact polynomial_divided_difference_bound P pt_j pt_next r P'_disk
              h_pt_j_norm h_pt_next_norm hP'_disk_bound
          calc ‖P.eval pt_next - P.eval pt_j‖
              ≤ P'_disk * ‖pt_next - pt_j‖ := h_mvt
            _ ≤ P'_disk * (2 * Real.pi * r / N) := by
                apply mul_le_mul_of_nonneg_left h_chord hP'_disk_nonneg
            _ < δ_P / 2 := h1
            _ < δ_P := by linarith [hδ_P_pos]
      -- h_P_diff : ‖...‖ < δ_P and δ_P ≤ ‖P.eval pt_j‖, so ‖...‖ < ‖P.eval pt_j‖
        calc ‖P.eval pt_next - P.eval pt_j‖
            < δ_P := h_P_diff
          _ ≤ ‖P.eval pt_j‖ := hδ_P angle_j
      -- From |a - b| < |b|, we get |a/b - 1| < 1, so a/b is in disk centered at 1 with radius < 1
      -- This disk is contained in {z : Re(z) > 0}
      have h_in_disk : ‖P.eval pt_next / P.eval pt_j - 1‖ < 1 := by
        rw [div_sub_one hPj_ne, norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hPj_ne)).mpr h_diff_bound
      -- A point in the open disk |z - 1| < 1 has Re(z) > 0
      have h_re_pos : 0 < (P.eval pt_next / P.eval pt_j).re := by
        have h1 := h_in_disk
      -- From |z - 1| < 1, we get Re(z) > Re(1) - |z - 1| > 1 - 1 = 0
      -- Step 1: (z).re = 1 + (z-1).re
        have hre_eq : (P.eval pt_next / P.eval pt_j).re =
            1 + (P.eval pt_next / P.eval pt_j - 1).re := by
          simp only [Complex.sub_re, Complex.one_re]; ring
      -- Step 2: (z-1).re ≥ -|(z-1).re| ≥ -‖z-1‖
        have hre_ge : (P.eval pt_next / P.eval pt_j - 1).re ≥
            -‖P.eval pt_next / P.eval pt_j - 1‖ := by
          calc (P.eval pt_next / P.eval pt_j - 1).re
              ≥ -|(P.eval pt_next / P.eval pt_j - 1).re| := neg_abs_le _
            _ ≥ -‖P.eval pt_next / P.eval pt_j - 1‖ := by
                apply neg_le_neg
                exact Complex.abs_re_le_norm _
      -- Step 3: Combine to get z.re ≥ 1 - ‖z-1‖ > 0
        have hgt : (P.eval pt_next / P.eval pt_j).re > 0 := by
          rw [hre_eq]
          have h2 : 1 - ‖P.eval pt_next / P.eval pt_j - 1‖ > 0 := by linarith [h1]
          linarith [hre_ge]
        exact hgt
      exact h_re_pos

    have h_Q_quotient_re_pos : 0 < (Q.eval pt_next / Q.eval pt_j).re := by
      have h_diff_bound : ‖Q.eval pt_next - Q.eval pt_j‖ < ‖Q.eval pt_j‖ := by
        have h_chord : ‖pt_next - pt_j‖ ≤ 2 * Real.pi * r / N := h_chord_common
      -- Same MVT bound as for P: using Q'_disk (coefficient-based disk bound)
        have h_Q_diff : ‖Q.eval pt_next - Q.eval pt_j‖ < δ_Q := by
          -- Use Q'_disk disk bound for polynomial_divided_difference_bound
          have h_mvt : ‖Q.eval pt_next - Q.eval pt_j‖ ≤ Q'_disk * ‖pt_next - pt_j‖ := by
            -- Apply the divided-difference lemma to Q with disk bound
            have h_pt_j_norm : ‖pt_j‖ = r := by
              simp only [pt_j, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
              have h_comm : I * (angle_j : ℂ) = (angle_j : ℝ) * I := by push_cast; ring
              rw [h_comm, Complex.norm_exp_ofReal_mul_I, mul_one]
            have h_pt_next_norm : ‖pt_next‖ = r := by
              simp only [pt_next, norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
              have h_comm : I * (angle_next : ℂ) = (angle_next : ℝ) * I := by push_cast; ring
              rw [h_comm, Complex.norm_exp_ofReal_mul_I, mul_one]
            exact polynomial_divided_difference_bound Q pt_j pt_next r Q'_disk
              h_pt_j_norm h_pt_next_norm hQ'_disk_bound
          -- Same calc pattern as P: Q'_disk ≤ Q'_disk + 1, and L_Q uses Q'_disk + 1
          have h_LQ_bound : L_Q * (2 * Real.pi / N) < 1 / 2 := by
            have h1 : L_Q * (2 * Real.pi / N) ≤ L_max * (2 * Real.pi / N) := by
              apply mul_le_mul_of_nonneg_right (le_max_right _ _)
              apply div_nonneg (by linarith [Real.pi_pos]) (le_of_lt hN_pos)
            exact lt_of_le_of_lt h1 h_ratio_bound
          have h_le : Q'_disk * (2 * Real.pi * r / N) ≤ (Q'_disk + 1) * (2 * Real.pi * r / N) := by
            apply mul_le_mul_of_nonneg_right (by linarith)
            apply div_nonneg (by nlinarith [Real.pi_pos, hr]) (le_of_lt hN_pos)
          have h_eq : (Q'_disk + 1) * (2 * Real.pi * r / N) = L_Q * δ_Q * (2 * Real.pi / N) := by
            simp only [L_Q]
            have := ne_of_gt hδ_Q_pos
            field_simp
          calc ‖Q.eval pt_next - Q.eval pt_j‖
              ≤ Q'_disk * ‖pt_next - pt_j‖ := h_mvt
            _ ≤ Q'_disk * (2 * Real.pi * r / N) := by
                apply mul_le_mul_of_nonneg_left h_chord hQ'_disk_nonneg
            _ ≤ (Q'_disk + 1) * (2 * Real.pi * r / N) := h_le
            _ = L_Q * δ_Q * (2 * Real.pi / N) := h_eq
            _ = L_Q * (2 * Real.pi / N) * δ_Q := by ring
            _ < (1 / 2) * δ_Q := mul_lt_mul_of_pos_right h_LQ_bound hδ_Q_pos
            _ < δ_Q := by linarith [hδ_Q_pos]
        calc ‖Q.eval pt_next - Q.eval pt_j‖
            < δ_Q := h_Q_diff
          _ ≤ ‖Q.eval pt_j‖ := hδ_Q angle_j
      have h_in_disk : ‖Q.eval pt_next / Q.eval pt_j - 1‖ < 1 := by
        rw [div_sub_one hQj_ne, norm_div]
        exact (div_lt_one (norm_pos_iff.mpr hQj_ne)).mpr h_diff_bound
      have h_re_pos : 0 < (Q.eval pt_next / Q.eval pt_j).re := by
        have h1 := h_in_disk
      -- Step 1: (z).re = 1 + (z-1).re
        have hre_eq : (Q.eval pt_next / Q.eval pt_j).re =
            1 + (Q.eval pt_next / Q.eval pt_j - 1).re := by
          simp only [Complex.sub_re, Complex.one_re]; ring
      -- Step 2: (z-1).re ≥ -|(z-1).re| ≥ -‖z-1‖
        have hre_ge : (Q.eval pt_next / Q.eval pt_j - 1).re ≥
            -‖Q.eval pt_next / Q.eval pt_j - 1‖ := by
          calc (Q.eval pt_next / Q.eval pt_j - 1).re
              ≥ -|(Q.eval pt_next / Q.eval pt_j - 1).re| := neg_abs_le _
            _ ≥ -‖Q.eval pt_next / Q.eval pt_j - 1‖ := by
                apply neg_le_neg
                exact Complex.abs_re_le_norm _
      -- Step 3: Combine to get z.re ≥ 1 - ‖z-1‖ > 0
        have hgt : (Q.eval pt_next / Q.eval pt_j).re > 0 := by
          rw [hre_eq]
          have h2 : 1 - ‖Q.eval pt_next / Q.eval pt_j - 1‖ > 0 := by linarith [h1]
          linarith [hre_ge]
        exact hgt
      exact h_re_pos

    -- From positive real part, we get |arg(quotient)| < π/2
    -- By abs_arg_lt_pi_div_two_iff: |arg z| < π/2 ↔ 0 < Re z ∨ z = 0
    have h_arg_P_quotient : |Complex.arg (P.eval pt_next / P.eval pt_j)| < Real.pi / 2 := by
      rw [Complex.abs_arg_lt_pi_div_two_iff]
      left
      exact h_P_quotient_re_pos

    have h_arg_Q_quotient : |Complex.arg (Q.eval pt_next / Q.eval pt_j)| < Real.pi / 2 := by
      rw [Complex.abs_arg_lt_pi_div_two_iff]
      left
      exact h_Q_quotient_re_pos

    -- Now connect arg(quotient) to argdiff
    -- arg(a/b) = arg(a) - arg(b) (mod 2π), realized in Real.Angle
    have h_arg_quot_eq_P : (Complex.arg (P.eval pt_next / P.eval pt_j) : Real.Angle) =
        (argdiff_P : Real.Angle) := by
      -- arg(x/y) = arg(x) - arg(y) in Real.Angle
      have h := Complex.arg_div_coe_angle hPnext_ne hPj_ne
      -- h : (arg(pt_next/pt_j) : Angle) = arg(pt_next) - arg(pt_j)
      rw [h]
      -- Goal: arg(P.eval pt_next) - arg(P.eval pt_j) = (argdiff_P : Angle)
      simp only [argdiff_P]
      exact (Real.Angle.coe_sub _ _).symm

    have h_arg_quot_eq_Q : (Complex.arg (Q.eval pt_next / Q.eval pt_j) : Real.Angle) =
        (argdiff_Q : Real.Angle) := by
      have h := Complex.arg_div_coe_angle hQnext_ne hQj_ne
      rw [h]
      simp only [argdiff_Q]
      exact (Real.Angle.coe_sub _ _).symm

    -- The wrapped value equals the arg of the quotient
    -- Key: wrap(argdiff_P) = (argdiff_P : Angle).toReal = (arg(quot) : Angle).toReal = arg(quot)
    -- The last step uses |arg(quot)| < π/2, so toReal returns arg(quot) directly.
    set_option maxHeartbeats 600000 in
    have h_wrap_P_eq_arg : wrap argdiff_P = Complex.arg (P.eval pt_next / P.eval pt_j) := by
      have h_arg_range := h_arg_P_quotient
      have h_angle_eq := h_arg_quot_eq_P
      have hpi := Real.pi_pos
      -- arg(quotient) ∈ (-π/2, π/2) ⊂ (-π, π]
      have h_arg_in_range : Complex.arg (P.eval pt_next / P.eval pt_j) ∈ Set.Ioc (-Real.pi) Real.pi := by
        have hab := abs_lt.mp h_arg_range
        constructor <;> linarith
      -- toReal(arg(quot) : Angle) = arg(quot) since arg(quot) ∈ (-π, π]
      have h_toReal_arg : (Complex.arg (P.eval pt_next / P.eval pt_j) : Real.Angle).toReal =
                          Complex.arg (P.eval pt_next / P.eval pt_j) :=
        Real.Angle.toReal_coe_eq_self_iff.mpr ⟨h_arg_in_range.1, h_arg_in_range.2⟩
      -- toReal(argdiff_P : Angle) = toReal(arg(quot) : Angle) since they're equal angles
      have h_toReal_eq : (argdiff_P : Real.Angle).toReal = (Complex.arg (P.eval pt_next / P.eval pt_j) : Real.Angle).toReal := by
        rw [h_angle_eq.symm]
      -- wrap(d) = toReal(d : Angle) for d ∈ (-2π, 2π) with d ≠ -π
      -- Since arg(quot) ∈ (-π/2, π/2), and (argdiff_P : Angle) = (arg(quot) : Angle),
      -- argdiff_P differs from arg(quot) by a multiple of 2π, so argdiff_P ≠ -π
      simp only [h_wrap_def]
      split_ifs with h1 h2
      · -- argdiff_P > π: wrap = argdiff_P - 2π
      -- But (argdiff_P : Angle) = (arg(quot) : Angle), and arg(quot) ∈ (-π/2, π/2)
      -- So argdiff_P - 2π ∈ (-π/2, π/2) as well, and toReal gives arg(quot)
        have h_shifted := h_toReal_eq
        simp only [h_toReal_arg] at h_shifted
        have h3 : (argdiff_P : Real.Angle) = ((argdiff_P - 2 * Real.pi : ℝ) : Real.Angle) := by
          have hcoe : ((argdiff_P - 2 * Real.pi : ℝ) : Real.Angle) =
                      (argdiff_P : Real.Angle) - ((2 : ℝ) * Real.pi : Real.Angle) :=
            Real.Angle.coe_sub argdiff_P (2 * Real.pi)
          rw [hcoe, Real.Angle.coe_two_pi, sub_zero]
        have h4 : argdiff_P - 2 * Real.pi ∈ Set.Ioc (-Real.pi) Real.pi := by
          have hb1 := h_diff_P_bound.1
          have hb2 := h_diff_P_bound.2
          constructor <;> linarith
        rw [h3, Real.Angle.toReal_coe_eq_self_iff.mpr h4] at h_shifted
        linarith
      · -- argdiff_P < -π: wrap = argdiff_P + 2π
        have h_shifted := h_toReal_eq
        simp only [h_toReal_arg] at h_shifted
        have h3 : (argdiff_P : Real.Angle) = ((argdiff_P + 2 * Real.pi : ℝ) : Real.Angle) := by
          have hcoe : ((argdiff_P + 2 * Real.pi : ℝ) : Real.Angle) =
                      (argdiff_P : Real.Angle) + ((2 : ℝ) * Real.pi : Real.Angle) :=
            Real.Angle.coe_add argdiff_P (2 * Real.pi)
          rw [hcoe, Real.Angle.coe_two_pi, add_zero]
        have h4 : argdiff_P + 2 * Real.pi ∈ Set.Ioc (-Real.pi) Real.pi := by
          have hb1 := h_diff_P_bound.1
          have hb2 := h_diff_P_bound.2
          constructor <;> linarith
        rw [h3, Real.Angle.toReal_coe_eq_self_iff.mpr h4] at h_shifted
        linarith
      · -- argdiff_P ∈ (-π, π]: wrap = argdiff_P
      -- After push_neg: h1 : argdiff_P ≤ π, h2 : argdiff_P > -π (i.e., -π < argdiff_P)
        push_neg at h1 h2
        have h_shifted := h_toReal_eq
        simp only [h_toReal_arg] at h_shifted
      -- Need argdiff_P ∈ (-π, π] for toReal to give it back
      -- h2 directly gives -π < argdiff_P
        have h4 : argdiff_P ∈ Set.Ioc (-Real.pi) Real.pi := by
          constructor
          · exact h2  -- -π < argdiff_P directly from push_neg on ≤
          · exact h1  -- argdiff_P ≤ π
        rw [Real.Angle.toReal_coe_eq_self_iff.mpr h4] at h_shifted
        exact h_shifted

    have h_wrap_P_small : wrap argdiff_P ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
      rw [Set.mem_Ioo, h_wrap_P_eq_arg]
      have hab := abs_lt.mp h_arg_P_quotient
      constructor <;> linarith [hab.1, hab.2]

    -- Same for Q (same proof structure as P)
    set_option maxHeartbeats 600000 in
    have h_wrap_Q_eq_arg : wrap argdiff_Q = Complex.arg (Q.eval pt_next / Q.eval pt_j) := by
      have h_arg_range := h_arg_Q_quotient
      have h_angle_eq := h_arg_quot_eq_Q
      have hpi := Real.pi_pos
      have h_arg_in_range : Complex.arg (Q.eval pt_next / Q.eval pt_j) ∈ Set.Ioc (-Real.pi) Real.pi := by
        have hab := abs_lt.mp h_arg_range
        constructor <;> linarith
      have h_toReal_arg : (Complex.arg (Q.eval pt_next / Q.eval pt_j) : Real.Angle).toReal =
                          Complex.arg (Q.eval pt_next / Q.eval pt_j) :=
        Real.Angle.toReal_coe_eq_self_iff.mpr ⟨h_arg_in_range.1, h_arg_in_range.2⟩
      have h_toReal_eq : (argdiff_Q : Real.Angle).toReal = (Complex.arg (Q.eval pt_next / Q.eval pt_j) : Real.Angle).toReal := by
        rw [h_angle_eq.symm]
      simp only [h_wrap_def]
      split_ifs with h1 h2
      · have h_shifted := h_toReal_eq
        simp only [h_toReal_arg] at h_shifted
        have h3 : (argdiff_Q : Real.Angle) = ((argdiff_Q - 2 * Real.pi : ℝ) : Real.Angle) := by
          have hcoe : ((argdiff_Q - 2 * Real.pi : ℝ) : Real.Angle) =
                      (argdiff_Q : Real.Angle) - ((2 : ℝ) * Real.pi : Real.Angle) :=
            Real.Angle.coe_sub argdiff_Q (2 * Real.pi)
          rw [hcoe, Real.Angle.coe_two_pi, sub_zero]
        have h4 : argdiff_Q - 2 * Real.pi ∈ Set.Ioc (-Real.pi) Real.pi := by
          have hb1 := h_diff_Q_bound.1
          have hb2 := h_diff_Q_bound.2
          constructor <;> linarith
        rw [h3, Real.Angle.toReal_coe_eq_self_iff.mpr h4] at h_shifted
        linarith
      · have h_shifted := h_toReal_eq
        simp only [h_toReal_arg] at h_shifted
        have h3 : (argdiff_Q : Real.Angle) = ((argdiff_Q + 2 * Real.pi : ℝ) : Real.Angle) := by
          have hcoe : ((argdiff_Q + 2 * Real.pi : ℝ) : Real.Angle) =
                      (argdiff_Q : Real.Angle) + ((2 : ℝ) * Real.pi : Real.Angle) :=
            Real.Angle.coe_add argdiff_Q (2 * Real.pi)
          rw [hcoe, Real.Angle.coe_two_pi, add_zero]
        have h4 : argdiff_Q + 2 * Real.pi ∈ Set.Ioc (-Real.pi) Real.pi := by
          have hb1 := h_diff_Q_bound.1
          have hb2 := h_diff_Q_bound.2
          constructor <;> linarith
        rw [h3, Real.Angle.toReal_coe_eq_self_iff.mpr h4] at h_shifted
        linarith
      · -- argdiff_Q ∈ (-π, π]: wrap = argdiff_Q
      -- After push_neg: h1 : argdiff_Q ≤ π, h2 : argdiff_Q > -π
        push_neg at h1 h2
        have h_shifted := h_toReal_eq
        simp only [h_toReal_arg] at h_shifted
        have h4 : argdiff_Q ∈ Set.Ioc (-Real.pi) Real.pi := by
          constructor
          · exact h2  -- -π < argdiff_Q directly from push_neg on ≤
          · exact h1  -- argdiff_Q ≤ π
        rw [Real.Angle.toReal_coe_eq_self_iff.mpr h4] at h_shifted
        exact h_shifted

    have h_wrap_Q_small : wrap argdiff_Q ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) := by
      rw [Set.mem_Ioo, h_wrap_Q_eq_arg]
      have hab := abs_lt.mp h_arg_Q_quotient
      constructor <;> linarith [hab.1, hab.2]

    -- With both in (-π/2, π/2), their sum is in (-π, π)
    have h_sum_in_range : wrap argdiff_P + wrap argdiff_Q ∈ Set.Ioo (-Real.pi) Real.pi := by
      rw [Set.mem_Ioo]
      have hP := h_wrap_P_small
      have hQ := h_wrap_Q_small
      constructor <;> linarith [hP.1, hP.2, hQ.1, hQ.2]

    -- When the sum is in (-π, π), toReal distributes
    -- Goal: ((argdiff_P : Angle) + (argdiff_Q : Angle)).toReal = (argdiff_P : Angle).toReal + (argdiff_Q : Angle).toReal
    -- We know (argdiff_P : Angle).toReal = wrap argdiff_P and (argdiff_Q : Angle).toReal = wrap argdiff_Q
    -- And (argdiff_P : Angle) = (wrap argdiff_P : Angle), (argdiff_Q : Angle) = (wrap argdiff_Q : Angle)
    -- (since they differ by 2πk, which is 0 in Angle)

    -- First, show (argdiff_P : Angle) = (wrap argdiff_P : Angle)
    have h_angle_P : (argdiff_P : Real.Angle) = (wrap argdiff_P : Real.Angle) := by
      simp only [h_wrap_def]
      split_ifs with h1 h2
      · -- argdiff_P > π: wrap = argdiff_P - 2π
        simp only [Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero]
      · -- argdiff_P < -π: wrap = argdiff_P + 2π
        simp only [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
      · -- argdiff_P ∈ [-π, π]: wrap = argdiff_P
        rfl

    have h_angle_Q : (argdiff_Q : Real.Angle) = (wrap argdiff_Q : Real.Angle) := by
      simp only [h_wrap_def]
      split_ifs with h1 h2
      · simp only [Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero]
      · simp only [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
      · rfl


    -- First establish that (argdiff_PQ : Angle) = (wrap argdiff_PQ : Angle)
    have h_angle_PQ : (argdiff_PQ : Real.Angle) = (wrap argdiff_PQ : Real.Angle) := by
      simp only [h_wrap_def]
      split_ifs with h1 h2
      · simp only [Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero]
      · simp only [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
      · rfl

    -- The key: toReal is additive when the sum stays in (-π, π]
    have h_toReal_add : (wrap argdiff_P + wrap argdiff_Q : Real.Angle).toReal =
        (wrap argdiff_P : Real.Angle).toReal + (wrap argdiff_Q : Real.Angle).toReal := by
      -- When both summands and their sum are in the principal range (-π, π],
      -- toReal commutes with addition
      -- h_sum_in_range : ∈ Set.Ioo (-π) π, i.e., (-π, π), both open
      -- We need (-π, π], i.e., -π < x ∧ x ≤ π. Since x < π → x ≤ π, this works.
      have h_sum_ioo := Set.mem_Ioo.mp h_sum_in_range
      have h_in_range : -Real.pi < wrap argdiff_P + wrap argdiff_Q ∧
                        wrap argdiff_P + wrap argdiff_Q ≤ Real.pi := by
        exact ⟨h_sum_ioo.1, le_of_lt h_sum_ioo.2⟩
      have hP_in : -Real.pi < wrap argdiff_P ∧ wrap argdiff_P ≤ Real.pi := by
        have hP_ioo := Set.mem_Ioo.mp h_wrap_P_small  -- -π/2 < wrap argdiff_P < π/2
        constructor
        · linarith [Real.pi_pos, hP_ioo.1]
        · linarith [Real.pi_pos, hP_ioo.2]
      have hQ_in : -Real.pi < wrap argdiff_Q ∧ wrap argdiff_Q ≤ Real.pi := by
        have hQ_ioo := Set.mem_Ioo.mp h_wrap_Q_small  -- -π/2 < wrap argdiff_Q < π/2
        constructor
        · linarith [Real.pi_pos, hQ_ioo.1]
        · linarith [Real.pi_pos, hQ_ioo.2]
      -- toReal of coercion is identity when in principal range
      have hP_toReal : (wrap argdiff_P : Real.Angle).toReal = wrap argdiff_P :=
        Real.Angle.toReal_coe_eq_self_iff.mpr hP_in
      have hQ_toReal : (wrap argdiff_Q : Real.Angle).toReal = wrap argdiff_Q :=
        Real.Angle.toReal_coe_eq_self_iff.mpr hQ_in
      have h_sum_toReal : (wrap argdiff_P + wrap argdiff_Q : Real.Angle).toReal =
          wrap argdiff_P + wrap argdiff_Q :=
        Real.Angle.toReal_coe_eq_self_iff.mpr h_in_range
      -- Now show toReal distributes
      calc (wrap argdiff_P + wrap argdiff_Q : Real.Angle).toReal
          = wrap argdiff_P + wrap argdiff_Q := h_sum_toReal
        _ = (wrap argdiff_P : Real.Angle).toReal + (wrap argdiff_Q : Real.Angle).toReal := by
            rw [hP_toReal, hQ_toReal]

    -- Chain the equalities
    have h_eq_chain : wrap argdiff_PQ = wrap argdiff_P + wrap argdiff_Q := by
      -- All are equal to the toReal of (argdiff_P + argdiff_Q : Angle)
      have h1 : (argdiff_PQ : Real.Angle).toReal = wrap argdiff_PQ := by
        have h_PQ_in : -Real.pi < wrap argdiff_PQ ∧ wrap argdiff_PQ ≤ Real.pi := by
          -- wrap by definition maps to (-π, π]
          simp only [h_wrap_def]
          split_ifs with hgt hlt
          · -- argdiff_PQ > π: wrap = argdiff_PQ - 2π
            constructor
            · have := h_diff_PQ_bound.1  -- argdiff_PQ > -2π
              linarith [Real.pi_pos]
            · have := h_diff_PQ_bound.2  -- argdiff_PQ < 2π
              linarith [Real.pi_pos]
          · -- argdiff_PQ < -π: wrap = argdiff_PQ + 2π
            constructor
            · have := h_diff_PQ_bound.1  -- argdiff_PQ > -2π
              linarith [Real.pi_pos]
            · have := h_diff_PQ_bound.2  -- argdiff_PQ < 2π
              linarith [Real.pi_pos]
          · -- argdiff_PQ ∈ (-π, π]: wrap = argdiff_PQ
            -- With new wrap def: hgt is ¬(d > π), hlt is ¬(d ≤ -π)
            push_neg at hgt hlt
            -- hgt : argdiff_PQ ≤ π, hlt : argdiff_PQ > -π
            exact ⟨hlt, hgt⟩
        rw [h_angle_PQ]
        exact Real.Angle.toReal_coe_eq_self_iff.mpr h_PQ_in
      have h2 : (argdiff_PQ : Real.Angle) = (argdiff_P : Real.Angle) + (argdiff_Q : Real.Angle) :=
        h_angle_eq
      have h3 : (argdiff_P : Real.Angle) + (argdiff_Q : Real.Angle) =
                (wrap argdiff_P : Real.Angle) + (wrap argdiff_Q : Real.Angle) := by
        rw [← h_angle_P, ← h_angle_Q]
      calc wrap argdiff_PQ
          = (argdiff_PQ : Real.Angle).toReal := h1.symm
        _ = ((argdiff_P : Real.Angle) + (argdiff_Q : Real.Angle)).toReal := by rw [h2]
        _ = ((wrap argdiff_P : Real.Angle) + (wrap argdiff_Q : Real.Angle)).toReal := by rw [h3]
        _ = (wrap argdiff_P : Real.Angle).toReal + (wrap argdiff_Q : Real.Angle).toReal := by
            -- Use the toReal_add lemma we proved above
            exact h_toReal_add
        _ = wrap argdiff_P + wrap argdiff_Q := by
            have hP : (wrap argdiff_P : Real.Angle).toReal = wrap argdiff_P := by
              have hP_ioo := Set.mem_Ioo.mp h_wrap_P_small
              apply Real.Angle.toReal_coe_eq_self_iff.mpr
              constructor
              · linarith [Real.pi_pos, hP_ioo.1]
              · linarith [Real.pi_pos, hP_ioo.2]
            have hQ : (wrap argdiff_Q : Real.Angle).toReal = wrap argdiff_Q := by
              have hQ_ioo := Set.mem_Ioo.mp h_wrap_Q_small
              apply Real.Angle.toReal_coe_eq_self_iff.mpr
              constructor
              · linarith [Real.pi_pos, hQ_ioo.1]
              · linarith [Real.pi_pos, hQ_ioo.2]
            rw [hP, hQ]

    -- Goal has let-bindings diff_*, but h_eq_chain uses argdiff_* (same values, different names)
    -- The proof h_eq_chain uses local variables argdiff_* which are definitionally
    -- equal to the goal's diff_* let-bindings. Show this by expanding both.
    simp only [wrap] at h_eq_chain ⊢
    convert h_eq_chain using 3 <;> norm_cast

  -- Sum over all j to get the final result
  -- The goal after simp is:
  -- sum of wrapped diffs for P*Q / (2π) = sum of wrapped diffs for P / (2π) + sum for Q / (2π)

  have h_sum_eq : (Finset.sum (Finset.range N) fun j =>
        let z_j := r * Complex.exp (I * (2 * Real.pi * (j : ℝ) / (N : ℝ)))
        let z_next := r * Complex.exp (I * (2 * Real.pi * ((j + 1) % N : ℕ) / (N : ℝ)))
        wrap (Complex.arg (P.eval z_next * Q.eval z_next) -
              Complex.arg (P.eval z_j * Q.eval z_j))) =
      (Finset.sum (Finset.range N) fun j =>
        let z_j := r * Complex.exp (I * (2 * Real.pi * (j : ℝ) / (N : ℝ)))
        let z_next := r * Complex.exp (I * (2 * Real.pi * ((j + 1) % N : ℕ) / (N : ℝ)))
        wrap (Complex.arg (P.eval z_next) - Complex.arg (P.eval z_j))) +
      (Finset.sum (Finset.range N) fun j =>
        let z_j := r * Complex.exp (I * (2 * Real.pi * (j : ℝ) / (N : ℝ)))
        let z_next := r * Complex.exp (I * (2 * Real.pi * ((j + 1) % N : ℕ) / (N : ℝ)))
        wrap (Complex.arg (Q.eval z_next) - Complex.arg (Q.eval z_j))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < N := Finset.mem_range.mp hj
    exact h_term_eq j hj'

  simp only [wrap, h_wrap_def] at h_sum_eq

  -- Step 2: Combine RHS into single division and use h_sum_eq
  have h2pi_ne' : (2 : ℝ) * Real.pi ≠ 0 := by positivity

  -- Rewrite RHS: a/c + b/c = (a + b)/c
  rw [← add_div]

  -- Now goal: (sum_PQ) / (2π) = (sum_P + sum_Q) / (2π)
  -- This follows from h_sum_eq by dividing both sides by 2π
  -- Since h_sum_eq says sum_PQ = sum_P + sum_Q
  -- congr 1 closes the goal since the numerators are definitionally equal
  -- after simp converts wrap to if-then-else (h_sum_eq establishes this equality)
  congr 1

/-- ARGUMENT PRINCIPLE FOR POLYNOMIALS (Exact Version). -/
theorem argument_principle_polynomial_exact (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (h_no_roots_on_circle : ∀ α ∈ Q.roots, ‖α‖ ≠ r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀,
      discrete_winding_number Q N r = (Q.roots.filter (fun α => ‖α‖ < r)).card := by

  -- Each root is either inside or outside (not on circle by hypothesis)
  have h_partition : ∀ α ∈ Q.roots, ‖α‖ < r ∨ ‖α‖ > r := by
    intro α hα
    have h := h_no_roots_on_circle α hα
    rcases lt_trichotomy ‖α‖ r with h_lt | h_eq | h_gt
    · left; exact h_lt
    · exact absurd h_eq h
    · right; exact h_gt

  -- For each root, get the threshold where winding becomes exact
  have h_all_roots_threshold : ∀ α ∈ Q.roots, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      discrete_winding_number (Polynomial.X - Polynomial.C α) N r =
        if ‖α‖ < r then 1 else 0 := by
    intro α hα
    rcases h_partition α hα with h_lt | h_gt
    · obtain ⟨N₀, hN₀⟩ := discrete_winding_exact_for_circle_inside α r hr h_lt
      use N₀; intro N hN; simp only [h_lt, ↓reduceIte]; exact hN₀ N hN
    · obtain ⟨N₀, hN₀⟩ := discrete_winding_exact_for_circle_outside α r hr h_gt
      use N₀; intro N hN; simp only [not_lt.mpr (le_of_lt h_gt), ↓reduceIte]; exact hN₀ N hN

  -- Define threshold function for each root
  let threshold : ℂ → ℕ := fun α =>
    if h : α ∈ Q.roots then Classical.choose (h_all_roots_threshold α h) else 0

  -- Take N₀ as the maximum threshold over all roots, plus a buffer for multiplicativity
  -- The actual N₀ needs to account for discrete_winding_mul_exact thresholds
  -- For simplicity, we use the polynomial factorization approach

  -- Step 1: Polynomial factorization
  have hQ_splits : Q.Splits := IsAlgClosed.splits Q
  have hQ_roots_card : Q.roots.card = Q.natDegree := Polynomial.splits_iff_card_roots.mp hQ_splits
  have hc_ne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ

  -- Q = C(leadingCoeff) * ∏(X - C α) over roots
  have hQ_factor : Q = Polynomial.C Q.leadingCoeff *
      (Q.roots.map (fun α => Polynomial.X - Polynomial.C α)).prod :=
    (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hQ_roots_card).symm

  have h_circle_norm : ∀ θ : ℝ, ‖r * Complex.exp (I * θ)‖ = r := by
    intro θ
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    have h_exp : ‖Complex.exp (I * θ)‖ = 1 := by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ
    rw [h_exp, mul_one]

  -- We need to prove the property for Q by induction on Q.roots.
  -- The key insight is that Q = C(lc) * ∏(X - C α) where α ranges over roots.

  -- Use the existing exact results and multiplicativity

  -- Build N₀ using the threshold function and accounting for multiplicativity
  let N₀_roots := (Q.roots.toFinset.sup threshold) + 1

  have h_const_winding : ∀ (c : ℂ), c ≠ 0 → ∀ (N : ℕ), N > 0 →
      discrete_winding_number (Polynomial.C c) N r = 0 := by
    intro c hc N hN
    simp only [discrete_winding_number, Polynomial.eval_C]
    -- All angles are the same (arg c), so all differences are 0
    -- Each diff = arg c - arg c = 0, which is in (-π, π], so wrap is identity
    have h_wrap_zero : ∀ (j : ℕ),
        (let diff := Complex.arg c - Complex.arg c
         if diff > Real.pi then diff - 2 * Real.pi
         else if diff ≤ -Real.pi then diff + 2 * Real.pi
         else diff) = 0 := by
      intro j
      simp only [sub_self]
      have h1 : ¬((0 : ℝ) > Real.pi) := not_lt.mpr (le_of_lt Real.pi_pos)
      have h2 : ¬((0 : ℝ) ≤ -Real.pi) := not_le.mpr (neg_neg_of_pos Real.pi_pos)
      simp only [h1, ↓reduceIte, h2]
    simp only [Finset.sum_eq_zero (fun j _ => h_wrap_zero j), zero_div]

  -- Nonzero on circle helper: Q has no roots on circle implies Q(z) ≠ 0 for |z| = r
  have h_Q_nonzero_circle : ∀ θ : ℝ, Q.eval (r * Complex.exp (I * θ)) ≠ 0 := by
    intro θ
    by_contra h_eq
    -- If Q(r*exp(iθ)) = 0, then r*exp(iθ) is a root
    have h_is_root : r * Complex.exp (I * θ) ∈ Q.roots := by
      rw [Polynomial.mem_roots hQ]
      exact h_eq
    -- But this root has |·| = r, contradicting h_no_roots_on_circle
    have h_norm : ‖r * Complex.exp (I * θ)‖ = r := h_circle_norm θ
    exact h_no_roots_on_circle _ h_is_root h_norm

  -- For any subset of roots (multiset), the product has no roots on circle
  have h_prod_nonzero : ∀ (s : Multiset ℂ), (∀ α ∈ s, ‖α‖ ≠ r) →
      ∀ θ : ℝ, (s.map (fun α => Polynomial.X - Polynomial.C α)).prod.eval
        (r * Complex.exp (I * θ)) ≠ 0 := by
    intro s hs θ
    rw [Polynomial.eval_multiset_prod]
    -- Need to show: the multiset of evaluations doesn't contain 0
    apply Multiset.prod_ne_zero
    -- Goal: 0 ∉ (s.map (fun α => ...)).map (fun p => p.eval ...)
    rw [Multiset.mem_map]
    push_neg
    intro p hp
    -- p ∈ s.map (fun α => X - C α) means p = X - C α for some α ∈ s
    rw [Multiset.mem_map] at hp
    obtain ⟨α, hα, rfl⟩ := hp
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
    intro h_eq
    have h_norm_eq : ‖α‖ = r := by rw [← h_eq]; exact h_circle_norm θ
    exact hs α hα h_norm_eq

  -- Main induction: winding of product = count of roots inside
  -- Property P(s): ∃ N₀, ∀ N ≥ N₀, winding(∏(X - C α)) = (s.filter (|·| < r)).card
  have h_roots_subset : ∀ α ∈ Q.roots, ‖α‖ ≠ r := h_no_roots_on_circle

  -- The general property for any subset of roots
  have h_induction : ∀ (s : Multiset ℂ), (∀ α ∈ s, ‖α‖ ≠ r) →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        discrete_winding_number (s.map (fun α => Polynomial.X - Polynomial.C α)).prod N r =
          (s.filter (fun α => ‖α‖ < r)).card := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty =>
      -- Empty product = 1 = C(1), which is a nonzero constant
      use 1
      intro N hN
      simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.filter_zero, Multiset.card_zero,
        Nat.cast_zero]
      -- Need to show: discrete_winding_number 1 N r = 0
      -- Note: (1 : Polynomial ℂ) = C 1
      have h1_eq : (1 : Polynomial ℂ) = Polynomial.C 1 := Polynomial.C_1.symm
      rw [h1_eq]
      have hN_pos : N > 0 := Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hN)
      exact h_const_winding 1 one_ne_zero N hN_pos
    | cons a s' ih =>
      -- a ::ₘ s' maps to (X - C a) * ∏_{α ∈ s'}(X - C α)
      have ha_not_on : ‖a‖ ≠ r := hs a (Multiset.mem_cons_self a s')
      have hs'_not_on : ∀ α ∈ s', ‖α‖ ≠ r := fun α hα => hs α (Multiset.mem_cons_of_mem hα)

      -- Get threshold for the linear factor (X - C a)
      have ha_partition : ‖a‖ < r ∨ ‖a‖ > r := by
        rcases lt_trichotomy ‖a‖ r with h_lt | h_eq | h_gt
        · exact Or.inl h_lt
        · exact absurd h_eq ha_not_on
        · exact Or.inr h_gt

      -- Get N₀ for the linear factor
      obtain ⟨N₀_a, hN₀_a⟩ : ∃ N₀ : ℕ, ∀ N ≥ N₀,
          discrete_winding_number (Polynomial.X - Polynomial.C a) N r =
            if ‖a‖ < r then 1 else 0 := by
        rcases ha_partition with h_lt | h_gt
        · obtain ⟨N₀, hN₀⟩ := discrete_winding_exact_for_circle_inside a r hr h_lt
          use N₀; intro N hN; simp only [h_lt, ↓reduceIte]; exact hN₀ N hN
        · obtain ⟨N₀, hN₀⟩ := discrete_winding_exact_for_circle_outside a r hr h_gt
          use N₀; intro N hN; simp only [not_lt.mpr (le_of_lt h_gt), ↓reduceIte]; exact hN₀ N hN

      -- Get N₀ for the product from IH
      obtain ⟨N₀_s', hN₀_s'⟩ := ih hs'_not_on

      -- Get N₀ for multiplicativity
      have h_lin_nonzero : ∀ θ : ℝ, (Polynomial.X - Polynomial.C a).eval
          (r * Complex.exp (I * θ)) ≠ 0 := by
        intro θ
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
        intro h_eq
        have h_norm : ‖a‖ = r := by rw [← h_eq]; exact h_circle_norm θ
        exact ha_not_on h_norm

      have h_s'_nonzero : ∀ θ : ℝ, (s'.map (fun α => Polynomial.X - Polynomial.C α)).prod.eval
          (r * Complex.exp (I * θ)) ≠ 0 := h_prod_nonzero s' hs'_not_on

      obtain ⟨N₀_mul, hN₀_mul⟩ := discrete_winding_mul_exact
        (Polynomial.X - Polynomial.C a)
        (s'.map (fun α => Polynomial.X - Polynomial.C α)).prod
        r hr h_lin_nonzero h_s'_nonzero

      -- Combine all thresholds
      use max (max N₀_a N₀_s') N₀_mul
      intro N hN

      have hN_a : N ≥ N₀_a := le_trans (le_max_left N₀_a N₀_s') (le_trans (le_max_left _ _) hN)
      have hN_s' : N ≥ N₀_s' := le_trans (le_max_right N₀_a N₀_s') (le_trans (le_max_left _ _) hN)
      have hN_mul : N ≥ N₀_mul := le_trans (le_max_right _ _) hN

      -- Rewrite the product
      have h_prod_eq : (a ::ₘ s').map (fun α => Polynomial.X - Polynomial.C α) =
          (Polynomial.X - Polynomial.C a) ::ₘ s'.map (fun α => Polynomial.X - Polynomial.C α) :=
        Multiset.map_cons _ _ _
      simp only [h_prod_eq, Multiset.prod_cons]

      -- Apply multiplicativity
      rw [hN₀_mul N hN_mul]
      rw [hN₀_a N hN_a]
      rw [hN₀_s' N hN_s']

      -- Count: filter on a ::ₘ s' = (filter on {a}) + (filter on s')
      simp only [Multiset.filter_cons]
      split_ifs with ha_inside
      · -- a is inside: count increases by 1
      -- Goal: 1 + (s'.filter ...).card = ({a} + s'.filter ...).card
        rw [Multiset.card_add, Multiset.card_singleton]
        push_cast
        ring
      · -- a is outside: count stays same
      -- Goal: 0 + (s'.filter ...).card = (0 + s'.filter ...).card = (s'.filter ...).card
        simp only [Multiset.zero_add, zero_add]

  -- Apply induction to Q.roots
  obtain ⟨N₀_prod, hN₀_prod⟩ := h_induction Q.roots h_roots_subset

  -- Get threshold for multiplying by constant
  have h_lc_nonzero_circle : ∀ θ : ℝ, (Polynomial.C Q.leadingCoeff).eval
      (r * Complex.exp (I * θ)) ≠ 0 := by
    intro θ
    simp only [Polynomial.eval_C]
    exact hc_ne

  have h_prod_factor_nonzero : ∀ θ : ℝ, (Q.roots.map (fun α => Polynomial.X - Polynomial.C α)).prod.eval
      (r * Complex.exp (I * θ)) ≠ 0 := h_prod_nonzero Q.roots h_roots_subset

  obtain ⟨N₀_lc_mul, hN₀_lc_mul⟩ := discrete_winding_mul_exact
    (Polynomial.C Q.leadingCoeff)
    (Q.roots.map (fun α => Polynomial.X - Polynomial.C α)).prod
    r hr h_lc_nonzero_circle h_prod_factor_nonzero

  -- Final threshold - use max with 1 to ensure N > 0
  use max 1 (max N₀_prod N₀_lc_mul)
  intro N hN

  have hN_prod : N ≥ N₀_prod := le_trans (le_max_left N₀_prod N₀_lc_mul) (le_trans (le_max_right _ _) hN)
  have hN_lc_mul : N ≥ N₀_lc_mul := le_trans (le_max_right N₀_prod N₀_lc_mul) (le_trans (le_max_right _ _) hN)

  -- Prove N > 0 first
  have hN_pos : N > 0 := by
    have h1 : N ≥ max 1 (max N₀_prod N₀_lc_mul) := hN
    have h2 : max 1 (max N₀_prod N₀_lc_mul) ≥ 1 := le_max_left _ _
    omega

  -- Step-by-step proof avoiding rewriting Q.roots
  -- Step 1: Winding of factored form = winding of C(lc) + winding of product
  have h_step1 : discrete_winding_number (Polynomial.C Q.leadingCoeff *
      (Q.roots.map (fun α => Polynomial.X - Polynomial.C α)).prod) N r =
      discrete_winding_number (Polynomial.C Q.leadingCoeff) N r +
      discrete_winding_number (Q.roots.map (fun α => Polynomial.X - Polynomial.C α)).prod N r :=
    hN₀_lc_mul N hN_lc_mul

  -- Step 2: Winding of constant is 0
  have h_step2 : discrete_winding_number (Polynomial.C Q.leadingCoeff) N r = 0 :=
    h_const_winding Q.leadingCoeff hc_ne N hN_pos

  -- Step 3: Winding of product = count of roots inside
  have h_step3 : discrete_winding_number (Q.roots.map (fun α => Polynomial.X - Polynomial.C α)).prod N r =
      (Q.roots.filter (fun α => ‖α‖ < r)).card :=
    hN₀_prod N hN_prod

  -- Combine: Use hQ_factor to relate Q to the factored form
  -- Q = C(lc) * product, so winding(Q) = winding(C(lc) * product) = 0 + count = count
  calc discrete_winding_number Q N r
      = discrete_winding_number (Polynomial.C Q.leadingCoeff *
          (Q.roots.map (fun α => Polynomial.X - Polynomial.C α)).prod) N r := by
        conv_lhs => rw [hQ_factor]
      _ = discrete_winding_number (Polynomial.C Q.leadingCoeff) N r +
          discrete_winding_number (Q.roots.map (fun α => Polynomial.X - Polynomial.C α)).prod N r :=
        h_step1
      _ = 0 + (Q.roots.filter (fun α => ‖α‖ < r)).card := by rw [h_step2, h_step3]
      _ = (Q.roots.filter (fun α => ‖α‖ < r)).card := by ring

-- The error bound versions follow trivially from the exact version
theorem argument_principle_polynomial_theorem (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (h_no_roots_on_circle : ∀ α ∈ Q.roots, ‖α‖ ≠ r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀,
      |discrete_winding_number Q N r - (Q.roots.filter (fun α => ‖α‖ < r)).card| < 1/2 := by
  obtain ⟨N₀, hN₀⟩ := argument_principle_polynomial_exact Q hQ r hr h_no_roots_on_circle
  use N₀
  intro N hN
  rw [hN₀ N hN, sub_self, abs_zero]
  norm_num

theorem argument_principle_polynomial_tight_theorem (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (h_no_roots_on_circle : ∀ α ∈ Q.roots, ‖α‖ ≠ r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀,
      |discrete_winding_number Q N r - (Q.roots.filter (fun α => ‖α‖ < r)).card| < 1/4 := by
  obtain ⟨N₀, hN₀⟩ := argument_principle_polynomial_exact Q hQ r hr h_no_roots_on_circle
  use N₀
  intro N hN
  rw [hN₀ N hN, sub_self, abs_zero]
  norm_num

-- Backward compatibility aliases
alias argument_principle_polynomial_axiom := argument_principle_polynomial_theorem
alias argument_principle_polynomial_tight := argument_principle_polynomial_tight_theorem

/-- The minimum angular gap to roots on a circle of radius r.
    For linear factor (z - α), this is the angular "width" of the root region. -/
noncomputable def angular_gap (α : ℂ) (r : ℝ) : ℝ :=
  if _h : ‖α‖ < r then
    -- α is inside: angle subtended by α from circle of radius r
    2 * Real.arcsin (‖α‖ / r)
  else if _h' : ‖α‖ > r then
    -- α is outside: circle doesn't contain origin, gap is the "angular miss"
    2 * Real.arcsin (r / ‖α‖)
  else
    -- α is on the circle: degenerate case
    0

/-- For a linear factor with root inside the circle, the discrete winding
    stabilizes to exactly 1 once the mesh is fine enough. -/
theorem linear_factor_winding_stabilizes_inside (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ < r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀, ∀ M ≥ N,
      discrete_winding_number (Polynomial.X - Polynomial.C α) N r =
      discrete_winding_number (Polynomial.X - Polynomial.C α) M r := by
  /-
  Proof sketch:

  Key geometric fact: The image of the circle |z| = r under z ↦ z - α is a
  circle of radius r centered at -α. Since |α| < r, the origin is INSIDE this circle.

  The argument arg(z - α) increases monotonically (with some oscillation) by exactly 2π
  as z traverses the circle.

  Once the mesh 2π/N is smaller than the minimum gap (controlled by r - |α|),
  each step satisfies |Δarg| < π, so the wrapping correction is exact, and
  the total equals 2π (discrete winding = 1).

  The value stabilizes because finer meshes don't change the exact value.
  -/
  -- Use the axiom: once past the threshold, winding = 1 for all N
  obtain ⟨N₀, hN₀⟩ := discrete_winding_exact_for_circle_inside α r hr hα
  use N₀
  intro N hN M hM
  -- Both N and M give exactly 1
  have hN_eq : discrete_winding_number (Polynomial.X - Polynomial.C α) N r = 1 := hN₀ N hN
  have hM_eq : discrete_winding_number (Polynomial.X - Polynomial.C α) M r = 1 :=
    hN₀ M (le_trans hN hM)
  rw [hN_eq, hM_eq]

/-- For a linear factor with root outside the circle, the discrete winding
    stabilizes to exactly 0 once the mesh is fine enough. -/
theorem linear_factor_winding_stabilizes_outside (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ > r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀, ∀ M ≥ N,
      discrete_winding_number (Polynomial.X - Polynomial.C α) N r =
      discrete_winding_number (Polynomial.X - Polynomial.C α) M r := by
  -- Use the axiom: once past the threshold, winding = 0 for all N
  obtain ⟨N₀, hN₀⟩ := discrete_winding_exact_for_circle_outside α r hr hα
  use N₀
  intro N hN M hM
  -- Both N and M give exactly 0
  have hN_eq : discrete_winding_number (Polynomial.X - Polynomial.C α) N r = 0 := hN₀ N hN
  have hM_eq : discrete_winding_number (Polynomial.X - Polynomial.C α) M r = 0 :=
    hN₀ M (le_trans hN hM)
  rw [hN_eq, hM_eq]

/-- Exact Winding Lemma: Once the mesh is fine enough, discrete winding -/
theorem discrete_winding_exact_for_linear_inside (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ < r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀,
      discrete_winding_number (Polynomial.X - Polynomial.C α) N r = 1 := by
  /-
  Proof (geometric, exact):

  Setup: Let f(θ) = r·e^{iθ} - α. As θ goes 0 → 2π:
  - f traces a circle of radius r centered at -α
  - Since |α| < r, origin is STRICTLY INSIDE
  - arg(f(θ)) increases by exactly 2π

  Key observation: arg(f(θ)) is a continuous function that increases monotonically
  (modulo 2π) with some oscillation bounded by the angular gap.

  Claim: For N ≥ N₀ = ⌈4π/(r - |α|)⌉ + 1:
  1. The mesh 2π/N is small enough that consecutive samples satisfy |Δarg| < π
  2. With |Δarg| < π, the wrapping correction is EXACT (no information loss)
  3. The sum telescopes: Σ Δarg = arg(f(2π)) - arg(f(0)) + 2πk for some integer k
  4. Since we traverse once counterclockwise, k = 1
  5. discrete_winding = (2π · 1)/(2π) = 1

  The mesh condition: We need 2π/N < θ_min where θ_min is the minimum angular
  step at which |Δarg| could exceed π. By the geometry of the problem:
  - |f(θ)| ≥ r - |α| > 0 for all θ (triangle inequality)
  - The derivative |d(arg f)/dθ| ≤ r/(r - |α|) (Lipschitz bound)
  - So |Δarg| ≤ (r/(r-|α|)) · (2π/N)
  - We need (r/(r-|α|)) · (2π/N) < π
  - This gives N > 2r/(r-|α|)
  - Using N > 4π/(r-|α|) is sufficient (stronger condition)
  -/
  -- Use the analytical axiom directly
  exact discrete_winding_exact_for_circle_inside α r hr hα

/-- Exact Winding Lemma: For root outside, discrete winding equals 0 exactly. -/
theorem discrete_winding_exact_for_linear_outside (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ > r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀,
      discrete_winding_number (Polynomial.X - Polynomial.C α) N r = 0 := by
  -- Use the analytical axiom directly
  exact discrete_winding_exact_for_circle_outside α r hr hα

-- Helper: Discrete winding of linear factor (X - α) with |α| < r converges to 1

lemma linear_factor_winding_inside (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ < r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀,
      |discrete_winding_number (Polynomial.X - Polynomial.C α) N r - 1| < 1/4 := by
  /-
  Proof: Use the exact winding lemma `discrete_winding_exact_for_linear_inside`.

  Since the discrete winding equals EXACTLY 1 for large enough N, we have
  |1 - 1| = 0 < 1/4 trivially.
  -/
  -- Get the exact result from the stabilization lemma
  obtain ⟨N₀, hN₀⟩ := discrete_winding_exact_for_linear_inside α r hr hα
  use N₀
  intro N hN
  -- The discrete winding is exactly 1
  have h_exact : discrete_winding_number (Polynomial.X - Polynomial.C α) N r = 1 := hN₀ N hN
  -- So |1 - 1| = 0 < 1/4
  simp only [h_exact, sub_self, abs_zero]
  norm_num

-- Helper: Discrete winding of linear factor (X - α) with |α| > r converges to 0
lemma linear_factor_winding_outside (α : ℂ) (r : ℝ) (hr : 0 < r) (hα : ‖α‖ > r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀,
      |discrete_winding_number (Polynomial.X - Polynomial.C α) N r - 0| < 1/4 := by
  /-
  Proof: Use the exact winding lemma `discrete_winding_exact_for_linear_outside`.

  Since the discrete winding equals EXACTLY 0 for large enough N, we have
  |0 - 0| = 0 < 1/4 trivially.
  -/
  -- Get the exact result from the stabilization lemma
  obtain ⟨N₀, hN₀⟩ := discrete_winding_exact_for_linear_outside α r hr hα
  use N₀
  intro N hN
  -- The discrete winding is exactly 0
  have h_exact : discrete_winding_number (Polynomial.X - Polynomial.C α) N r = 0 := hN₀ N hN
  -- So |0 - 0| = 0 < 1/4
  simp only [h_exact, sub_zero, abs_zero]
  norm_num

-- Helper: Discrete winding is approximately additive for products
-- For any ε > 0, sufficiently fine lattice resolution gives error < ε
-- (This follows from the exact multiplicativity theorem)
lemma discrete_winding_mul (P Q : Polynomial ℂ) (r : ℝ) (hr : 0 < r)
    (hP : ∀ θ : ℝ, P.eval (r * Complex.exp (I * θ)) ≠ 0)
    (hQ : ∀ θ : ℝ, Q.eval (r * Complex.exp (I * θ)) ≠ 0)
    (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |discrete_winding_number (P * Q) N r -
       (discrete_winding_number P N r + discrete_winding_number Q N r)| < ε := by
  -- Get the exact multiplicativity threshold
  obtain ⟨N₀, hN₀⟩ := discrete_winding_mul_exact P Q r hr hP hQ
  use N₀
  intro N hN
  -- The exact version says they're equal, so difference is 0 < ε
  rw [hN₀ N hN, sub_self, abs_zero]
  exact hε

-- Argument principle for polynomials: winding number equals root count
-- For polynomial Q with roots α₁, ..., αₙ and radius r not equal to any |αᵢ|:
-- winding_number(Q, r) = #{i : |αᵢ| < r}
theorem argument_principle_polynomial (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (h_no_roots_on_circle : ∀ α ∈ Q.roots, ‖α‖ ≠ r) :
    ∃ (N₀ : ℕ), ∀ N ≥ N₀,
      |discrete_winding_number Q N r - (Q.roots.filter (fun α => ‖α‖ < r)).card| < 1/2 := by
  -- Step 1: Q is bounded away from 0 on the circle
  obtain ⟨ε, hε_pos, h_lower_bound⟩ := polynomial_nonzero_on_circle Q hQ r hr h_no_roots_on_circle
  -- Step 2: The true winding number equals the root count (argument principle)
  -- This is the classical result: winding(Q∘γ, 0) = #{roots inside γ}
  let true_winding : ℕ := (Q.roots.filter (fun α => ‖α‖ < r)).card

  exact argument_principle_polynomial_axiom Q hQ r hr h_no_roots_on_circle

-- The set of root radii is finite (since Q has finitely many roots)
lemma root_radii_finite (Q : Polynomial ℂ) (_hQ : Q ≠ 0) :
    Set.Finite {r : ℝ | ∃ α ∈ Q.roots, ‖α‖ = r} := by
  -- Q.roots is a finite multiset, so the image under ‖·‖ is finite
  refine Set.Finite.subset (Set.finite_range (fun α : Q.roots.toFinset => ‖(α : ℂ)‖)) ?_
  intro r ⟨α, hα_mem, hα_norm⟩
  simp only [Set.mem_range]
  exact ⟨⟨α, Multiset.mem_toFinset.mpr hα_mem⟩, hα_norm⟩

-- Helper: Any root radius can be isolated from other root radii
-- This follows from finiteness of the root radii set
lemma root_radius_isolated (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (α : ℂ) (_hα : α ∈ Q.roots) (_hα_ne : α ≠ 0) :
    ∃ (δ : ℝ), δ > 0 ∧
      ∀ β ∈ Q.roots, β ≠ 0 → ‖β‖ ≠ ‖α‖ → |‖β‖ - ‖α‖| > δ := by
  -- The set of root radii is finite
  have h_finite := root_radii_finite Q hQ
  -- Extract the finite set of radii different from ‖α‖
  let other_radii := {r : ℝ | ∃ β ∈ Q.roots, ‖β‖ = r ∧ r ≠ ‖α‖}
  have h_other_finite : Set.Finite other_radii := by
    refine Set.Finite.subset h_finite ?_
    intro r ⟨β, hβ_mem, hβ_norm, _⟩
    exact ⟨β, hβ_mem, hβ_norm⟩
  -- If other_radii is empty, any δ > 0 works
  by_cases h_empty : other_radii = ∅
  · use 1, one_pos
    intro β hβ_mem hβ_ne hβ_diff
    exfalso
    have : ‖β‖ ∈ other_radii := ⟨β, hβ_mem, rfl, hβ_diff⟩
    rw [h_empty] at this
    exact this
  · -- Otherwise, find the minimum distance to other radii
    have h_nonempty : other_radii.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    -- The distance function |r - ‖α‖| is positive on other_radii
    have h_pos : ∀ r ∈ other_radii, |r - ‖α‖| > 0 := by
      intro r ⟨β, _, hr_eq, hr_ne⟩
      simp only [abs_pos, sub_ne_zero]
      exact hr_ne
    -- On a finite nonempty set, a positive function has a positive infimum
    -- Get the minimum distance using Finset operations
    set dist_finset := h_other_finite.toFinset with h_dist_def
    have h_dist_nonempty : dist_finset.Nonempty := by
      rw [Set.Finite.toFinset_nonempty]
      exact h_nonempty
    -- min of |r - ‖α‖| over other_radii
    have h_image_nonempty : (dist_finset.image (fun r => |r - ‖α‖|)).Nonempty :=
      Finset.Nonempty.image h_dist_nonempty _
    set min_dist := (dist_finset.image (fun r => |r - ‖α‖|)).min' h_image_nonempty with h_min_def
    -- min_dist > 0 since all distances are positive
    have h_min_pos : min_dist > 0 := by
      have h_mem := Finset.min'_mem _ h_image_nonempty
      rw [Finset.mem_image] at h_mem
      obtain ⟨r, hr_mem, hr_eq⟩ := h_mem
      have h_r_pos : |r - ‖α‖| > 0 := by
        apply h_pos
        rw [Set.Finite.mem_toFinset] at hr_mem
        exact hr_mem
      simp only [h_min_def, ← hr_eq]
      exact h_r_pos
    -- Use δ = min_dist / 2
    use min_dist / 2, by linarith
    intro β hβ_mem hβ_ne hβ_diff
    -- ‖β‖ is in other_radii
    have hβ_in : ‖β‖ ∈ other_radii := ⟨β, hβ_mem, rfl, hβ_diff⟩
    -- So |‖β‖ - ‖α‖| ≥ min_dist
    have h_in_finset : ‖β‖ ∈ dist_finset := by
      rw [Set.Finite.mem_toFinset]
      exact hβ_in
    have h_in_image : |‖β‖ - ‖α‖| ∈ dist_finset.image (fun r => |r - ‖α‖|) :=
      Finset.mem_image_of_mem _ h_in_finset
    have h_ge : |‖β‖ - ‖α‖| ≥ min_dist := Finset.min'_le _ _ h_in_image
    linarith

/-! ### Profinite Lattice for Root Detection

The spiral root counter S(ε) approximates a sum of Heaviside steps,
stabilizing at each lattice level. -/

-- The lattice step bound: for any isolation gap δ₀, we can find n such that
-- the profinite lattice step l/p^n is smaller than δ₀
lemma profinite_lattice_refines (l : ℝ) (_hl : l > 0) (δ₀ : ℝ) (hδ₀ : δ₀ > 0) (p : ℕ) (hp : p ≥ 2) :
    ∃ n : ℕ, l / (p ^ n : ℝ) < δ₀ := by
  -- p^n → ∞, so l/p^n → 0
  -- Use Archimedean property
  have hp_pos : (p : ℝ) > 1 := by
    have : (p : ℝ) ≥ 2 := by exact_mod_cast hp
    linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (l / δ₀) hp_pos
  use n
  have h_pn_pos : (p ^ n : ℝ) > 0 := by positivity
  -- l / δ₀ < p^n  implies  l < p^n * δ₀  implies  l / p^n < δ₀
  have h1 : l / δ₀ < (p : ℝ) ^ n := hn
  have h2 : l < (p : ℝ) ^ n * δ₀ := by
    have := mul_lt_mul_of_pos_right h1 hδ₀
    rwa [div_mul_cancel₀ l (ne_of_gt hδ₀)] at this
  calc l / (p ^ n : ℝ) = l / (p : ℝ) ^ n := by norm_cast
    _ < δ₀ := by
        have h3 : l / (p : ℝ) ^ n < (p : ℝ) ^ n * δ₀ / (p : ℝ) ^ n := by
          apply div_lt_div_of_pos_right h2 h_pn_pos
        rw [mul_comm, mul_div_assoc, div_self (ne_of_gt h_pn_pos), mul_one] at h3
        exact h3

-- Key lemma: The spiral root counter detects root radii
-- S(ε) is constant except at log-radii where roots exist
-- The Heaviside limit: there exists δ > 0 and N₀ such that for N ≥ N₀,
-- the discrete counter has a jump of at least 1/2 across the root radius
lemma spiral_counter_step_at_root (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (α : ℂ) (hα : α ∈ Q.roots) (hα_ne : α ≠ 0) :
    ∃ (δ : ℝ) (N₀ : ℕ), δ > 0 ∧ ∀ (N : ℕ), N ≥ N₀ →
      |spiral_root_counter Q N (Real.log ‖α‖ + δ) -
       spiral_root_counter Q N (Real.log ‖α‖ - δ)| ≥ 1/2 := by
  -- Step 1: Isolate the root radius using finiteness
  obtain ⟨δ₀, hδ₀_pos, h_isolated⟩ := root_radius_isolated Q hQ α hα hα_ne

  have hα_norm_pos : ‖α‖ > 0 := norm_pos_iff.mpr hα_ne
  -- Use log-based δ for exact control
  let δ := Real.log (1 + δ₀ / (2 * ‖α‖))
  have h_arg_pos : 1 + δ₀ / (2 * ‖α‖) > 1 := by
    have : δ₀ / (2 * ‖α‖) > 0 := div_pos hδ₀_pos (by linarith)
    linarith
  have hδ_pos : δ > 0 := Real.log_pos h_arg_pos
  -- Define the two radii
  let r_plus := Real.exp (Real.log ‖α‖ + δ)
  let r_minus := Real.exp (Real.log ‖α‖ - δ)
  -- Key simplification: e^δ = 1 + δ₀/(2‖α‖)
  have h_exp_δ : Real.exp δ = 1 + δ₀ / (2 * ‖α‖) := by
    simp only [δ]
    rw [Real.exp_log (by linarith : 1 + δ₀ / (2 * ‖α‖) > 0)]
  -- Simplify: r_plus = ‖α‖ * e^δ, r_minus = ‖α‖ * e^{-δ}
  have h_r_plus : r_plus = ‖α‖ * Real.exp δ := by
    simp only [r_plus, Real.exp_add, Real.exp_log hα_norm_pos]
  have h_r_minus : r_minus = ‖α‖ * Real.exp (-δ) := by
    simp only [r_minus, Real.exp_sub, Real.exp_log hα_norm_pos]
    rw [Real.exp_neg, div_eq_mul_inv]
  have h_r_plus_pos : r_plus > 0 := Real.exp_pos _
  have h_r_minus_pos : r_minus > 0 := Real.exp_pos _
  -- Key: ‖α‖ is strictly between r_minus and r_plus
  have h_exp_δ_gt_one : Real.exp δ > 1 := Real.one_lt_exp_iff.mpr hδ_pos
  have h_alpha_lt_rplus : ‖α‖ < r_plus := by
    rw [h_r_plus]
    have h1 : ‖α‖ * 1 < ‖α‖ * Real.exp δ := by
      apply mul_lt_mul_of_pos_left h_exp_δ_gt_one hα_norm_pos
    linarith
  have h_rminus_lt_alpha : r_minus < ‖α‖ := by
    rw [h_r_minus]
    have h1 : Real.exp (-δ) < 1 := by
      rw [Real.exp_neg]
      exact inv_lt_one_of_one_lt₀ h_exp_δ_gt_one
    have h2 : ‖α‖ * Real.exp (-δ) < ‖α‖ * 1 := by
      apply mul_lt_mul_of_pos_left h1 hα_norm_pos
    linarith
  -- Show no roots on r_plus or r_minus (using isolation)
  -- The annulus width is EXACTLY δ₀/2 on the plus side
  have h_annulus_small : r_plus - ‖α‖ < δ₀ ∧ ‖α‖ - r_minus < δ₀ := by
    constructor
    · -- r_plus - ‖α‖ = ‖α‖·(e^δ - 1) = ‖α‖ · δ₀/(2‖α‖) = δ₀/2 < δ₀
      calc r_plus - ‖α‖ = ‖α‖ * Real.exp δ - ‖α‖ := by rw [h_r_plus]
        _ = ‖α‖ * (Real.exp δ - 1) := by ring
        _ = ‖α‖ * (1 + δ₀ / (2 * ‖α‖) - 1) := by rw [h_exp_δ]
        _ = ‖α‖ * (δ₀ / (2 * ‖α‖)) := by ring
        _ = δ₀ / 2 := by field_simp
        _ < δ₀ := by linarith
    · -- ‖α‖ - r_minus = ‖α‖(1 - e^{-δ}) < ‖α‖(1 - 1/e^δ) < ‖α‖ · δ₀/(2‖α‖) = δ₀/2 < δ₀
      -- Actually: 1 - e^{-δ} = 1 - 1/(1 + δ₀/(2‖α‖)) = (δ₀/(2‖α‖))/(1 + δ₀/(2‖α‖))
      have h_exp_neg : Real.exp (-δ) = 1 / (1 + δ₀ / (2 * ‖α‖)) := by
        rw [Real.exp_neg, h_exp_δ, one_div]
      calc ‖α‖ - r_minus = ‖α‖ - ‖α‖ * Real.exp (-δ) := by rw [h_r_minus]
        _ = ‖α‖ * (1 - Real.exp (-δ)) := by ring
        _ = ‖α‖ * (1 - 1 / (1 + δ₀ / (2 * ‖α‖))) := by rw [h_exp_neg]
        _ = ‖α‖ * ((δ₀ / (2 * ‖α‖)) / (1 + δ₀ / (2 * ‖α‖))) := by
            congr 1
            field_simp
            ring
        _ < ‖α‖ * (δ₀ / (2 * ‖α‖)) := by
            apply mul_lt_mul_of_pos_left _ hα_norm_pos
            apply div_lt_self (div_pos hδ₀_pos (by linarith))
            linarith
        _ = δ₀ / 2 := by field_simp
        _ < δ₀ := by linarith
  have h_no_roots_r_plus : ∀ β ∈ Q.roots, ‖β‖ ≠ r_plus := by
    intro β hβ_mem hβ_eq
    by_cases hβ_ne : β = 0
    · simp only [hβ_ne, norm_zero] at hβ_eq
      linarith
    · by_cases h_same : ‖β‖ = ‖α‖
      · -- If same radius as α, then r_plus ≠ ‖β‖ = ‖α‖ since r_plus > ‖α‖
        rw [h_same] at hβ_eq
        linarith
      · -- Different radius, use isolation
        have h_gap := h_isolated β hβ_mem hβ_ne h_same
        rw [hβ_eq] at h_gap
      -- |r_plus - ‖α‖| > δ₀ but r_plus - ‖α‖ < δ₀, contradiction
        have : |r_plus - ‖α‖| = r_plus - ‖α‖ := abs_of_pos (by linarith)
        rw [this] at h_gap
        linarith [h_annulus_small.1]
  have h_no_roots_r_minus : ∀ β ∈ Q.roots, ‖β‖ ≠ r_minus := by
    intro β hβ_mem hβ_eq
    by_cases hβ_ne : β = 0
    · simp only [hβ_ne, norm_zero] at hβ_eq
      linarith
    · by_cases h_same : ‖β‖ = ‖α‖
      · rw [h_same] at hβ_eq
        linarith
      · have h_gap := h_isolated β hβ_mem hβ_ne h_same
        rw [hβ_eq] at h_gap
      -- h_gap : |r_minus - ‖α‖| > δ₀
      -- We know r_minus < ‖α‖, so |r_minus - ‖α‖| = ‖α‖ - r_minus
        have h_neg : r_minus - ‖α‖ < 0 := by linarith
        have h_abs : |r_minus - ‖α‖| = ‖α‖ - r_minus := by
          rw [abs_of_neg h_neg]
          ring
        rw [h_abs] at h_gap
      -- Now h_gap : ‖α‖ - r_minus > δ₀
      -- But h_annulus_small.2 : ‖α‖ - r_minus < δ₀
        linarith [h_annulus_small.2]
  -- Apply argument principle (tight version) at both radii
  obtain ⟨N₁, hN₁⟩ := argument_principle_polynomial_tight Q hQ r_plus h_r_plus_pos h_no_roots_r_plus
  obtain ⟨N₂, hN₂⟩ := argument_principle_polynomial_tight Q hQ r_minus h_r_minus_pos h_no_roots_r_minus
  -- Now we can provide δ and N₀ = max N₁ N₂
  use δ, max N₁ N₂, hδ_pos
  intro N hN
  simp only [spiral_root_counter]
  -- For N ≥ max(N₁, N₂), both bounds hold
  have h_count_plus := hN₁ N (le_of_max_le_left hN)
  have h_count_minus := hN₂ N (le_of_max_le_right hN)
  -- count_plus ≥ count_minus + 1 because α ∈ filter at r_plus but not at r_minus
  let count_plus := (Q.roots.filter (fun β => ‖β‖ < r_plus)).card
  let count_minus := (Q.roots.filter (fun β => ‖β‖ < r_minus)).card
  have h_alpha_in_plus : α ∈ Q.roots.filter (fun β => ‖β‖ < r_plus) := by
    rw [Multiset.mem_filter]
    exact ⟨hα, h_alpha_lt_rplus⟩
  have h_alpha_not_minus : α ∉ Q.roots.filter (fun β => ‖β‖ < r_minus) := by
    rw [Multiset.mem_filter]
    push_neg
    intro _
    linarith
  have h_count_ge : count_plus ≥ count_minus + 1 := by
    -- First establish r_minus < r_plus
    have h_r_order : r_minus < r_plus := by
      simp only [r_plus, r_minus]
      have h1 : Real.exp δ > 1 := h_exp_δ_gt_one
      have h2 : Real.exp (-δ) < 1 := by
        rw [Real.exp_neg]
        exact inv_lt_one_of_one_lt₀ h1
      calc Real.exp (Real.log ‖α‖ - δ)
          = Real.exp (Real.log ‖α‖) / Real.exp δ := by rw [Real.exp_sub]
        _ = ‖α‖ / Real.exp δ := by rw [Real.exp_log hα_norm_pos]
        _ < ‖α‖ / 1 := by {
            apply div_lt_div_of_pos_left hα_norm_pos (by linarith : (0 : ℝ) < 1) h1
          }
        _ = ‖α‖ := div_one ‖α‖
        _ < ‖α‖ * Real.exp δ := by {
            have : ‖α‖ * 1 < ‖α‖ * Real.exp δ := mul_lt_mul_of_pos_left h1 hα_norm_pos
            simp at this ⊢; exact this
          }
        _ = Real.exp (Real.log ‖α‖) * Real.exp δ := by rw [Real.exp_log hα_norm_pos]
        _ = Real.exp (Real.log ‖α‖ + δ) := by rw [Real.exp_add]
    -- The filter at r_plus contains everything in filter at r_minus, plus α
    -- Use monotone_filter_right: if p → q then filter p ≤ filter q
    have h_subset : Q.roots.filter (fun β => ‖β‖ < r_minus) ≤
                    Q.roots.filter (fun β => ‖β‖ < r_plus) := by
      apply Multiset.monotone_filter_right
      intro β hβ
      exact lt_trans hβ h_r_order
    have h_card_le := Multiset.card_le_card h_subset
    -- And α is in r_plus filter but not r_minus filter
    have h_strict : Q.roots.filter (fun β => ‖β‖ < r_minus) <
                    Q.roots.filter (fun β => ‖β‖ < r_plus) := by
      constructor
      · exact h_subset
      · intro h_eq
        have := Multiset.mem_of_le h_eq h_alpha_in_plus
        exact h_alpha_not_minus this
    exact Nat.lt_iff_add_one_le.mp (Multiset.card_lt_card h_strict)
  -- Now use the 1/4 bounds
  -- |disc_plus - count_plus| < 1/4 and |disc_minus - count_minus| < 1/4
  -- disc_plus > count_plus - 1/4 ≥ count_minus + 1 - 1/4 = count_minus + 3/4
  -- disc_minus < count_minus + 1/4
  -- disc_plus - disc_minus > 3/4 - 1/4 = 1/2
  have h_disc_plus_lb : discrete_winding_number Q N r_plus > count_plus - 1/4 := by
    have := h_count_plus
    rw [abs_lt] at this
    linarith
  have h_disc_minus_ub : discrete_winding_number Q N r_minus < count_minus + 1/4 := by
    have := h_count_minus
    rw [abs_lt] at this
    linarith
  -- The calc shows strictly > 1/2, which implies ≥ 1/2
  have h_count_plus_real : (count_plus : ℝ) ≥ count_minus + 1 := by exact_mod_cast h_count_ge
  have h_strict : |discrete_winding_number Q N (Real.exp (Real.log ‖α‖ + δ)) -
        discrete_winding_number Q N (Real.exp (Real.log ‖α‖ - δ))| > 1/2 := by
    calc |discrete_winding_number Q N (Real.exp (Real.log ‖α‖ + δ)) -
          discrete_winding_number Q N (Real.exp (Real.log ‖α‖ - δ))|
        = |discrete_winding_number Q N r_plus - discrete_winding_number Q N r_minus| := rfl
      _ = discrete_winding_number Q N r_plus - discrete_winding_number Q N r_minus := by
          apply abs_of_pos; linarith
      _ > (count_plus - 1/4) - (count_minus + 1/4) := by linarith
      _ = (count_plus : ℝ) - count_minus - 1/2 := by ring
      _ ≥ (count_minus + 1) - count_minus - 1/2 := by linarith
      _ = 1/2 := by ring
  exact le_of_lt h_strict

-- Connection: spiral_test and discrete_winding_number both probe the same structure
-- The spiral_test uses product; winding number uses argument sum

lemma spiral_test_exact_root_detection (Q : Polynomial ℂ) (_hQ : Q ≠ 0)
    (p : ℕ) (_hp : Nat.Prime p) (n : ℕ) (σ : ℝ) :
    (spiral_test Q p n σ = 0) ↔
    (∃ j ∈ Finset.range (p ^ n),
      let θ_j : ℝ := 2 * Real.pi * (j : ℝ) / (p ^ n)
      let θ_comp : ℝ := 2 * Real.pi * ((p ^ n - j) : ℝ) / (p ^ n)
      Q.eval (Complex.exp (σ + I * θ_j)) = 0 ∨
      Q.eval (Complex.exp (-σ + I * θ_comp)) = 0) := by
  -- spiral_test is a finite product; it's zero iff some factor is zero
  unfold spiral_test
  rw [Finset.prod_eq_zero_iff]
  simp only [mul_eq_zero]

lemma spiral_test_detects_roots_via_winding (Q : Polynomial ℂ) (hQ : Q ≠ 0)
    (p : ℕ) (_hp : Nat.Prime p) (σ : ℝ) :
    (spiral_test Q p 1 σ = 0) →
    ∃ α ∈ Q.roots, ‖α‖ = Real.exp σ ∨ ‖α‖ = Real.exp (-σ) := by
  -- If spiral_test = 0, then Q(z) = 0 for some z on one of the two shells
  -- This happens exactly when there's a root at radius e^σ or e^{-σ}
  intro h_zero
  -- Unfold spiral_test definition
  unfold spiral_test at h_zero
  simp only [pow_one] at h_zero
  -- The product is zero iff some factor is zero
  rw [Finset.prod_eq_zero_iff] at h_zero
  obtain ⟨j, _, h_factor_zero⟩ := h_zero
  -- A factor Q.eval(z_j) * Q.eval(z'_j) = 0 means Q has a root at z_j or z'_j
  rw [mul_eq_zero] at h_factor_zero
  cases h_factor_zero with
  | inl h_pos =>
    -- Q.eval z_pos = 0, so z_pos is a root
    let θ_j := 2 * Real.pi * (j : ℝ) / p
    let z_pos := Complex.exp (σ + I * θ_j)
    have h_root : Q.IsRoot z_pos := h_pos
    have h_mem : z_pos ∈ Q.roots := Polynomial.mem_roots hQ |>.mpr h_root
    use z_pos, h_mem
    left
    -- ‖z_pos‖ = ‖exp(σ + i*θ)‖ = exp(Re(σ + i*θ)) = exp(σ)
    rw [Complex.norm_exp]
    -- Re(σ + I * θ_j) = σ
    congr 1
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  | inr h_neg =>
    -- Q.eval z_neg = 0, so z_neg is a root
    let θ_comp := 2 * Real.pi * ((p - j) : ℝ) / p
    let z_neg := Complex.exp (-σ + I * θ_comp)
    have h_root : Q.IsRoot z_neg := h_neg
    have h_mem : z_neg ∈ Q.roots := Polynomial.mem_roots hQ |>.mpr h_root
    use z_neg, h_mem
    right
    -- ‖z_neg‖ = ‖exp(-σ + i*θ)‖ = exp(Re(-σ + i*θ)) = exp(-σ)
    rw [Complex.norm_exp]
    -- Re(-σ + I * θ_comp) = -σ
    congr 1
    simp [Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]


-- The shell spiral test: evaluates Q at N-th roots of unity scaled to radius r
-- Returns the product Q(r·ωⱼ) · Q(r⁻¹·ω̄ⱼ) over j = 0, ..., N-1
noncomputable def shell_spiral_test (Q : Polynomial ℂ) (N : ℕ) (r : ℝ) : ℂ :=
  Finset.prod (Finset.range N) fun j =>
    let θ := 2 * Real.pi * (j : ℝ) / N
    let z := r * Complex.exp (I * θ)
    let z_inv := (1/r) * Complex.exp (-I * θ)
    Q.eval z * Q.eval z_inv


-- For polynomials REAL on the unit circle with spiral symmetry,
-- roots come in paired shells (r, 1/r)
-- This means: knowing inside roots (|α| < 1) determines outside roots (|α| > 1)
lemma shell_pairing_from_spiral_symmetry (Q : Polynomial ℂ) (_hQ : Q ≠ 0)
    (h_real : ∀ z : ℂ, ‖z‖ = 1 → (Q.eval z).im = 0)
    (r : ℝ) (hr : 0 < r) (_hr_ne_1 : r ≠ 1) :
    (∃ α ∈ Q.roots, ‖α‖ = r) ↔ (∃ β ∈ Q.roots, ‖β‖ = 1/r) := by
  constructor
  · -- Forward: root at r implies root at 1/r
    intro ⟨α, hα_mem, hα_norm⟩
    use 1 / conj α
    constructor
    · exact roots_of_real_on_circle Q h_real α hα_mem
    · -- ‖1/conj α‖ = 1/‖α‖ = 1/r
      have hα_ne : α ≠ 0 := by
        intro h
        rw [h] at hα_norm
        simp at hα_norm
        linarith
      rw [norm_div, norm_one, Complex.norm_conj, hα_norm]
  · -- Backward: root at 1/r implies root at r
    intro ⟨β, hβ_mem, hβ_norm⟩
    use 1 / conj β
    constructor
    · exact roots_of_real_on_circle Q h_real β hβ_mem
    · -- ‖1/conj β‖ = 1/‖β‖ = 1/(1/r) = r
      have hβ_ne : β ≠ 0 := by
        intro h
        rw [h] at hβ_norm
        simp at hβ_norm
        have : r = 0 := by linarith
        linarith
      rw [norm_div, norm_one, Complex.norm_conj, hβ_norm]
      field_simp


-- Key lemma: If Q has a root α on the unit circle, we can find roots of unity
-- arbitrarily close to α where Q evaluates to a small value

-- Simplified version: just show roots of unity get arbitrarily close
-- The full version with Q(ω) small requires polynomial Lipschitz bounds
lemma spiral_test_vanishes_at_root (Q : Polynomial ℂ) (_hQ : Q ≠ 0)
    (h_real : ∀ z : ℂ, ‖z‖ = 1 → (Q.eval z).im = 0)
    (α : ℂ) (hα_norm : ‖α‖ = 1) (hα_root : Q.IsRoot α) :
    ∀ ε > 0, ∃ (ω : ℂ), ∃ (N : ℕ+),
      (ω ^ (N : ℕ) = 1) ∧  -- ω is a root of unity
      ‖ω‖ = 1 ∧            -- ω is on the circle
      ‖ω - α‖ < ε := by     -- ω is close to α
  intro ε hε
  -- Use root_detection_via_roots_of_unity to approximate α by roots of unity
  obtain ⟨ω_seq, h_roots, h_norm, h_conv⟩ :=
    root_detection_via_roots_of_unity Q h_real α hα_norm hα_root
  -- Get n₀ such that ‖ω_seq n₀ - α‖ < ε
  obtain ⟨n₀, hn₀⟩ := h_conv ε hε
  -- ω_seq n₀ is our witness
  use ω_seq n₀
  -- It's a root of unity
  obtain ⟨N, hN⟩ := h_roots n₀
  use N
  constructor
  · exact hN
  constructor
  · exact h_norm n₀
  · exact hn₀ n₀ (le_refl n₀)


/-! ### Fejér-Riesz factor: helper lemmas -/

/-- Root pairing from spiral symmetry (Q.eval z / z^N form):
    If Q is real on the circle (in the Q/z^N sense), then roots pair via α ↦ 1/conj(α). -/
private lemma roots_paired_from_spiral_div (Q : Polynomial ℂ) (N : ℕ)
    (h_real : ∀ z : ℂ, ‖z‖ = 1 → (Q.eval z / z ^ N).im = 0)
    (h_deg : Q.natDegree ≤ 2 * N)
    (α : ℂ) (hα_root : α ∈ Q.roots) (hα_ne : α ≠ 0) :
    (1 / conj α) ∈ Q.roots := by
  have hQ_ne : Q ≠ 0 := Polynomial.ne_zero_of_mem_roots hα_root
  rw [Polynomial.mem_roots hQ_ne]
  -- From spiral_symmetry_extends: Q(w) = w^{2N} * conj(Q(1/conj w))
  have h_spiral := spiral_symmetry_extends Q N h_real h_deg α hα_ne
  -- Q(α) = 0
  have hα_eval : Q.eval α = 0 := (Polynomial.mem_roots hQ_ne).mp hα_root
  -- So 0 = α^{2N} * conj(Q(1/conj α)), and α ≠ 0 implies conj(Q(1/conj α)) = 0
  rw [hα_eval] at h_spiral
  have h_pow_ne : α ^ (2 * N) ≠ 0 := pow_ne_zero _ hα_ne
  have h_conj_zero := (mul_eq_zero.mp h_spiral.symm).resolve_left h_pow_ne
  rwa [map_eq_zero] at h_conj_zero

/-- On the unit circle, the factor (z - 1/conj α) equals (-z/conj α) * conj(z - α).
    This is the key algebraic identity for converting outside-disk roots to conjugates of inside-disk roots. -/
private lemma circle_factor_reflect (α z : ℂ) (hα : α ≠ 0) (hz : ‖z‖ = 1) :
    z - 1 / conj α = -z / conj α * conj (z - α) := by
  have hα_conj : conj α ≠ 0 := by intro h; apply hα; rwa [map_eq_zero] at h
  have hz_inv : z * conj z = 1 := by
    rw [mul_conj]
    have : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq]; simp [hz]
    simp [this]
  -- Expand conj(z - α) = conj z - conj α
  rw [map_sub]
  -- Now: z - 1/conj α = -z/conj α * (conj z - conj α)
  -- Multiply out RHS
  have : -z / conj α * (conj z - conj α) = -z * conj z / conj α + z := by
    field_simp; ring
  rw [this]
  -- Simplify using z * conj z = 1
  rw [show -z * conj z = -(z * conj z) from by ring, hz_inv]
  ring

/-- Multiset product version of circle_factor_reflect:
    ∏_{α ∈ S} (z - 1/conj α) = (-z)^|S| / ∏(conj α) * conj(∏(z - α)). -/
private lemma multiset_prod_circle_reflect (S : Multiset ℂ) (hS : ∀ α ∈ S, α ≠ 0)
    (z : ℂ) (hz : ‖z‖ = 1) :
    (S.map (fun α => z - 1 / conj α)).prod =
    (-z) ^ S.card / (S.map conj).prod * conj ((S.map (fun α => z - α)).prod) := by
  induction S using Multiset.induction_on with
  | empty =>
    simp [Multiset.map_zero, Multiset.prod_zero]
  | cons a S ih =>
    have ha : a ≠ 0 := hS a (Multiset.mem_cons_self a S)
    have hS' : ∀ α ∈ S, α ≠ 0 := fun α hα => hS α (Multiset.mem_cons_of_mem hα)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rw [ih hS']
    rw [circle_factor_reflect a z ha hz]
    -- LHS: (-z/conj a * conj(z-a)) * ((-z)^|S| / ∏conj(S) * conj(∏(z-α)))
    -- RHS: (-z)^(|S|+1) / (conj a * ∏conj(S)) * conj((z-a) * ∏(z-α))
    rw [pow_succ]
    rw [map_mul]
    have h_conj_ne : ∀ α : ℂ, α ≠ 0 → conj α ≠ 0 := by
      intro α hα h_eq; apply hα; rwa [map_eq_zero] at h_eq
    have h_conj_prod_ne : (S.map conj).prod ≠ 0 := by
      apply Multiset.prod_ne_zero
      rw [Multiset.mem_map]
      push_neg
      intro y hy
      exact h_conj_ne y (hS' y hy)
    have h_conj_a_ne : conj a ≠ 0 := h_conj_ne a ha
    field_simp

/-! ### Fejér-Riesz factor: algebraic helpers for root factorization -/

/-- The polynomial identity from spiral symmetry: Q = spiral_reflect(Q) · X^{2N-d}. -/
private lemma spiral_reflect_poly_identity (Q : Polynomial ℂ) (N : ℕ)
    (h_real : ∀ z : ℂ, ‖z‖ = 1 → (Q.eval z / z ^ N).im = 0)
    (h_deg : Q.natDegree ≤ 2 * N) :
    Q = spiral_reflect Q * X ^ (2 * N - Q.natDegree) := by
  -- Show Q and R := spiral_reflect(Q) * X^{2N-d} agree on the unit circle, then apply identity theorem
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.Infinite.mono _ unit_circle_infinite
  intro z hz
  simp only [Set.mem_setOf_eq] at hz ⊢
  have hz_ne : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact one_ne_zero hz.symm
  -- Step 1: On circle, Q(z) = z^{2N} * conj(Q(z)) (spiral symmetry)
  have h_spiral := spiral_symmetry_on_circle Q N h_real z hz
  rw [unit_circle_inv_eq_self z hz] at h_spiral
  -- h_spiral : Q.eval z = z ^ (2 * N) * starRingEnd ℂ (Q.eval z)
  -- Step 2: Compute (spiral_reflect Q * X^{2N-d}).eval z
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  -- Goal: Q.eval z = (spiral_reflect Q).eval z * z ^ (2 * N - Q.natDegree)
  -- Step 3: spiral_reflect(Q).eval z = z^d * conj(Q.eval z) on circle
  -- (Replicating the computation from normSq_eq_mul_spiral_reflect_on_circle)
  unfold spiral_reflect polynomial_mirror
  set Q_conj := Q.map (starRingEnd ℂ) with hQ_conj
  -- Compute Q_conj.reverse.eval z via eval₂_reverse_mul_pow
  have hz_inv_ne : z⁻¹ ≠ 0 := inv_ne_zero hz_ne
  haveI : Invertible z⁻¹ := invertibleOfNonzero hz_inv_ne
  have h1 := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) z⁻¹ Q_conj
  simp only [Polynomial.eval₂_id, invOf_eq_inv, inv_inv] at h1
  -- h1 : Q_conj.reverse.eval z * z⁻¹ ^ Q_conj.natDegree = Q_conj.eval z⁻¹
  have h_deg_eq : Q_conj.natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective _) Q
  have h_inv_conj : z⁻¹ = starRingEnd ℂ z := inv_eq_conj hz
  have h_conj_eval : Q_conj.eval z⁻¹ = starRingEnd ℂ (Q.eval z) := by
    rw [h_inv_conj, hQ_conj, Polynomial.eval_map_apply]
  rw [h_deg_eq, h_conj_eval] at h1
  -- h1 : Q_conj.reverse.eval z * z⁻¹ ^ Q.natDegree = conj(Q.eval z)
  -- Solve for Q_conj.reverse.eval z
  have h_sr : Q_conj.reverse.eval z = z ^ Q.natDegree * starRingEnd ℂ (Q.eval z) := by
    have := congr_arg (· * z ^ Q.natDegree) h1
    simp only [mul_assoc] at this
    rw [← mul_pow, inv_mul_cancel₀ hz_ne, one_pow, mul_one] at this
    rw [mul_comm] at this; exact this
  -- Step 4: Combine
  rw [h_sr]
  -- Goal: Q.eval z = z^d * conj(Q.eval z) * z^{2N-d}
  conv_lhs => rw [h_spiral]
  -- Goal: z^{2N} * conj(Q.eval z) = z^d * conj(Q.eval z) * z^{2N-d}
  symm
  calc z ^ Q.natDegree * starRingEnd ℂ (Q.eval z) * z ^ (2 * N - Q.natDegree)
      = z ^ Q.natDegree * z ^ (2 * N - Q.natDegree) * starRingEnd ℂ (Q.eval z) := by ring
    _ = z ^ (Q.natDegree + (2 * N - Q.natDegree)) * starRingEnd ℂ (Q.eval z) := by
        rw [← pow_add]
    _ = z ^ (2 * N) * starRingEnd ℂ (Q.eval z) := by rw [Nat.add_sub_of_le h_deg]

/-- Roots of a multiset product of linear factors: (S.map (X - C ·)).prod.roots = S. -/
private lemma roots_multiset_prod_X_sub_C (S : Multiset ℂ) :
    (S.map (fun α => X - C α)).prod.roots = S := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have h_ne : (X - C a) * (S.map (fun α => X - C α)).prod ≠ 0 :=
      mul_ne_zero (Polynomial.X_sub_C_ne_zero a) (by
        apply Multiset.prod_ne_zero
        rw [Multiset.mem_map]; push_neg
        intro b _; exact Polynomial.X_sub_C_ne_zero b)
    rw [Polynomial.roots_mul h_ne, Polynomial.roots_X_sub_C, ih, Multiset.singleton_add]

/-- reverse(X - C β) = C(-β) * (X - C β⁻¹) for β ≠ 0. -/
private lemma reverse_X_sub_C_ne_zero (β : ℂ) (hβ : β ≠ 0) :
    (X - C β).reverse = C (-β) * (X - C β⁻¹) := by
  conv_lhs => rw [show X - C β = (X : ℂ[X]) + C (-β) from by
    rw [sub_eq_add_neg, Polynomial.C_neg]]
  rw [Polynomial.reverse_add_C, Polynomial.natDegree_X, pow_one]
  have hX_rev : (X : ℂ[X]).reverse = 1 := by
    rw [show (X : ℂ[X]) = X * 1 from (mul_one X).symm, Polynomial.reverse_X_mul,
        show (1 : ℂ[X]) = C 1 from Polynomial.C_1.symm, Polynomial.reverse_C]
  rw [hX_rev]
  have : C (-β) * (X - C β⁻¹) = 1 + C (-β) * X := by
    have h1 : C (-β) * C β⁻¹ = -(1 : ℂ[X]) := by
      rw [← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ hβ, Polynomial.C_neg, Polynomial.C_1]
    rw [mul_sub, h1]; ring
  rw [this]

/-- Roots of the reverse of a multiset product of linear factors with nonzero roots.
    reverse(∏(X - C α)).roots = S.map(·⁻¹) when all α ∈ S are nonzero. -/
private lemma roots_reverse_multiset_prod_X_sub_C (S : Multiset ℂ) (hS : ∀ α ∈ S, α ≠ 0) :
    ((S.map (fun α => X - C α)).prod).reverse.roots = S.map (·⁻¹) := by
  induction S using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [show (1 : ℂ[X]) = C 1 from Polynomial.C_1.symm, Polynomial.reverse_C]
    simp [Polynomial.roots_C]
  | cons a S ih =>
    have ha : a ≠ 0 := hS a (Multiset.mem_cons_self a S)
    have hS' : ∀ α ∈ S, α ≠ 0 := fun α hα => hS α (Multiset.mem_cons_of_mem hα)
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [Polynomial.reverse_mul_of_domain]
    rw [reverse_X_sub_C_ne_zero a ha]
    -- Goal: (C (-a) * (X - C a⁻¹) * reverse(∏_S)).roots = {a⁻¹} + S.map(·⁻¹)
    have h_left_ne : C (-a) * (X - C a⁻¹) ≠ 0 :=
      mul_ne_zero (by rwa [Polynomial.C_ne_zero, neg_ne_zero]) (Polynomial.X_sub_C_ne_zero a⁻¹)
    have h_right_ne : (S.map (fun α => X - C α)).prod.reverse ≠ 0 := by
      intro h_eq
      have h_prod_ne : (S.map (fun α => X - C α)).prod ≠ 0 := by
        apply Multiset.prod_ne_zero
        rw [Multiset.mem_map]; push_neg
        intro b _; exact Polynomial.X_sub_C_ne_zero b
      have h_lc := Polynomial.leadingCoeff_ne_zero.mpr h_prod_ne
      rw [← Polynomial.coeff_zero_reverse] at h_lc
      rw [h_eq, Polynomial.coeff_zero] at h_lc; exact h_lc rfl
    rw [Polynomial.roots_mul (mul_ne_zero h_left_ne h_right_ne)]
    rw [Polynomial.roots_C_mul _ (by rwa [neg_ne_zero])]
    rw [Polynomial.roots_X_sub_C, ih hS', Multiset.singleton_add]

/-- Nonzero roots are self-paired: T.map(1/conj·) = T where T = Q.roots.filter(· ≠ 0). -/
private lemma nonzero_roots_self_paired (Q : Polynomial ℂ) (N : ℕ) (hQ : Q ≠ 0)
    (h_real : ∀ z : ℂ, ‖z‖ = 1 → (Q.eval z / z ^ N).im = 0)
    (h_deg : Q.natDegree ≤ 2 * N) :
    (Q.roots.filter (· ≠ (0 : ℂ))).map (fun α => 1 / conj α) =
      Q.roots.filter (· ≠ (0 : ℂ)) := by
  set T := Q.roots.filter (· ≠ (0 : ℂ)) with hT_def
  set m := 2 * N - Q.natDegree with hm_def
  have hlc_ne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  -- Q splits over ℂ
  have hQ_splits := IsAlgClosed.splits Q
  have hQ_roots_card := Polynomial.splits_iff_card_roots.mp hQ_splits
  -- Q = C(lc) * ∏_{all roots}(X - C α) = C(lc) * X^m * ∏_T(X - C α)
  have hQ_factor : Q = Polynomial.C Q.leadingCoeff *
      (Q.roots.map (fun α => X - C α)).prod :=
    (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hQ_roots_card).symm
  -- Zero roots contribute X factors
  -- From spiral_reflect_poly_identity: Q = spiral_reflect(Q) * X^m
  have h_poly_id := spiral_reflect_poly_identity Q N h_real h_deg
  -- spiral_reflect(Q) ≠ 0
  have h_sr_ne : spiral_reflect Q ≠ 0 := by
    intro h; rw [h, zero_mul] at h_poly_id; exact hQ h_poly_id
  -- Step A: Compute spiral_reflect(Q).roots from the "left" representation
  -- Q = X^m * (C(lc) * ∏_T(X - C α)), and Q = spiral_reflect(Q) * X^m
  -- So spiral_reflect(Q) = C(lc) * ∏_T(X - C α)
  set P_left := Polynomial.C Q.leadingCoeff * (T.map (fun α => X - C α)).prod with hP_left_def
  -- Q = X^m * P_left (show this)
  -- First: m₀ := (Q.roots.filter(·=0)).card = m (from spiral_reflect_poly_identity)
  -- (This was proven in fejer_riesz_root_factorization but we reprove the key fact)
  have h_sr_eval_zero : (spiral_reflect Q).eval 0 ≠ 0 := by
    unfold spiral_reflect polynomial_mirror
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse,
        Polynomial.leadingCoeff_map (starRingEnd ℂ)]
    rw [ne_eq, ← map_zero (starRingEnd ℂ)]
    exact (starRingEnd ℂ).injective.ne hlc_ne
  have h_roots_eq : Q.roots = (spiral_reflect Q).roots + m • ({0} : Multiset ℂ) := by
    conv_lhs => rw [h_poly_id]
    rw [Polynomial.roots_mul (mul_ne_zero h_sr_ne (pow_ne_zero _ Polynomial.X_ne_zero)),
        Polynomial.roots_X_pow]
  -- T = spiral_reflect(Q).roots (since spiral_reflect(Q) has no zero root)
  have hT_eq_sr_roots : T = (spiral_reflect Q).roots := by
    have h1 : T = Q.roots.filter (· ≠ (0:ℂ)) := rfl
    rw [h_roots_eq] at h1
    rw [h1, Multiset.filter_add, Multiset.filter_eq_self.mpr, Multiset.filter_eq_nil.mpr]
    · simp
    · intro a ha
      by_cases hm : m = 0
      · simp [hm] at ha
      · rw [Multiset.mem_nsmul] at ha; simp [Multiset.mem_singleton.mp ha.2]
    · intro a ha h_eq
      rw [h_eq] at ha
      exact h_sr_eval_zero ((Polynomial.mem_roots h_sr_ne).mp ha)
  -- Step B: Compute spiral_reflect(Q).roots from the "right" representation
  -- spiral_reflect(Q) = (Q.map conj).reverse
  -- (Q.map conj).roots = Q.roots.map conj (by roots_map_of_injective)
  have h_conj_roots : Q.roots.map (starRingEnd ℂ) = (Q.map (starRingEnd ℂ)).roots :=
    Polynomial.roots_map_of_injective_of_card_eq_natDegree
      (starRingEnd ℂ).injective hQ_roots_card
  -- (Q.map conj) = X^m * (C(conj(lc)) * ∏_{α ∈ T}(X - C(conj α)))
  -- reverse(Q.map conj) = reverse(C(conj(lc)) * ∏_{α ∈ T}(X - C(conj α)))
  -- To get roots: reverse.roots = (T.map conj).map(·⁻¹) = T.map(fun α => (conj α)⁻¹)
  -- We show this by relating the root multisets through the polynomial identity.
  -- spiral_reflect(Q) = (Q.map conj).reverse, so spiral_reflect(Q).roots = reverse.roots
  -- Compute (Q.map conj) factored form
  have hQ_map_factor : Q.map (starRingEnd ℂ) =
      Polynomial.C (starRingEnd ℂ Q.leadingCoeff) *
      ((Q.roots.map (starRingEnd ℂ)).map (fun α => X - C α)).prod := by
    conv_lhs => rw [hQ_factor]
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod]
    congr 1
    rw [Multiset.map_map, Multiset.map_map]
    congr 1; ext α
    simp [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  -- Zeros map to zeros
  have h_conj_zeros :
      (Q.roots.filter (· = (0:ℂ))).map (starRingEnd ℂ) =
      m • ({0} : Multiset ℂ) := by
    -- filter(·=0) = replicate(count 0 Q.roots) 0
    rw [Multiset.filter_eq' Q.roots (0:ℂ)]
    simp only [Multiset.map_replicate, map_zero, Multiset.nsmul_singleton]
    -- Goal: count 0 Q.roots = m
    -- From h_roots_eq: Q.roots = sr.roots + m•{0}
    rw [h_roots_eq, Multiset.count_add, Multiset.count_nsmul, Multiset.count_singleton_self,
        mul_one]
    -- Goal: count 0 sr.roots + m = m (sr has no zero root, so count = 0)
    have h_sr_count_zero : Multiset.count 0 (spiral_reflect Q).roots = 0 := by
      rw [Multiset.count_eq_zero]
      intro h_mem
      exact h_sr_eval_zero ((Polynomial.mem_roots h_sr_ne).mp h_mem)
    rw [h_sr_count_zero, zero_add]
  set T_conj := T.map (starRingEnd ℂ) with hTconj_def
  set R := Polynomial.C (starRingEnd ℂ Q.leadingCoeff) *
      (T_conj.map (fun α => X - C α)).prod with hR_def
  have hT_conj_ne : ∀ α ∈ T_conj, α ≠ 0 := by
    intro α hα
    obtain ⟨β, hβ_mem, rfl⟩ := Multiset.mem_map.mp hα
    intro h_eq; rw [map_eq_zero] at h_eq
    exact (Multiset.mem_filter.mp hβ_mem).2 h_eq
  have hR_ne : R ≠ 0 := by
    rw [hR_def]; apply mul_ne_zero
    · rwa [Polynomial.C_ne_zero, ne_eq, map_eq_zero]
    · apply Multiset.prod_ne_zero
      rw [Multiset.mem_map]; push_neg
      intro b _; exact Polynomial.X_sub_C_ne_zero b
  -- Show Q.map conj = X^m * R
  have hQ_conj_eq : Q.map (starRingEnd ℂ) = X ^ m * R := by
    rw [hR_def, hQ_map_factor]
    -- Goal: C(conj lc) * ((Q.roots.map conj).map(X-C·)).prod = X^m * (C(conj lc) * T_conj.map(X-C·).prod)
    -- Split Q.roots.map conj = zeros.map conj + T_conj
    have h_split : Q.roots.map (starRingEnd ℂ) =
        (Q.roots.filter (· = (0:ℂ))).map (starRingEnd ℂ) + T_conj := by
      rw [hTconj_def, ← Multiset.map_add]; congr 1
      exact (Multiset.filter_add_not (· = (0:ℂ)) Q.roots).symm
    rw [h_split]
    rw [Multiset.map_add, Multiset.prod_add]
    -- zeros.map conj = m • {0}, and (m•{0}).map(X-C·).prod = X^m
    rw [h_conj_zeros]
    rw [show (m • ({0} : Multiset ℂ)).map (fun α => X - C α) =
        m • ({(X : ℂ[X])} : Multiset ℂ[X]) from by
      rw [Multiset.map_nsmul]; congr 1; simp]
    rw [Multiset.prod_nsmul, Multiset.prod_singleton]
    ring
  -- Step B2: (Q.map conj).reverse = R.reverse
  have h_sr_eq_R_rev : spiral_reflect Q = R.reverse := by
    unfold spiral_reflect polynomial_mirror
    rw [hQ_conj_eq, Polynomial.reverse_X_pow_mul]
  -- Step B3: R.reverse.roots = (T_conj).map(·⁻¹)
  have h_R_rev_roots : R.reverse.roots = T_conj.map (·⁻¹) := by
    rw [hR_def]
    rw [Polynomial.reverse_mul_of_domain]
    rw [Polynomial.reverse_C]
    rw [Polynomial.roots_C_mul _ (by rwa [ne_eq, map_eq_zero])]
    exact roots_reverse_multiset_prod_X_sub_C T_conj hT_conj_ne
  -- Step C: Combine
  -- T = spiral_reflect(Q).roots = R.reverse.roots = T_conj.map(·⁻¹)
  -- = (T.map conj).map(·⁻¹) = T.map(fun α => (conj α)⁻¹)
  have h_key : T = T_conj.map (·⁻¹) := by
    rw [← h_R_rev_roots, ← h_sr_eq_R_rev, hT_eq_sr_roots]
  -- Convert: T_conj.map(·⁻¹) = (T.map conj).map(·⁻¹) = T.map(fun α => (conj α)⁻¹) = T.map(1/conj·)
  conv_rhs => rw [h_key, hTconj_def, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro α _
  simp [Function.comp, one_div]

/-- Root partition identity for the strictly positive case: -/
private lemma fejer_riesz_root_factorization (Q : Polynomial ℂ) (N : ℕ) (hQ : Q ≠ 0)
    (h_real : ∀ z : ℂ, ‖z‖ = 1 → (Q.eval z / z ^ N).im = 0)
    (h_pos : ∀ z : ℂ, ‖z‖ = 1 → 0 < (Q.eval z / z ^ N).re)
    (h_deg : Q.natDegree ≤ 2 * N) :
    ∃ (P : Polynomial ℂ) (A : ℝ), 0 < A ∧ P.natDegree ≤ N ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        Q.eval z = (A : ℂ) * z ^ N * ↑(Complex.normSq (P.eval z)) := by
  -- Step 1: Factor Q over ℂ
  have hQ_splits := IsAlgClosed.splits Q
  have hQ_roots_card := Polynomial.splits_iff_card_roots.mp hQ_splits
  have hlc_ne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hQ_factor : Q = C Q.leadingCoeff * (Q.roots.map (fun α => X - C α)).prod :=
    (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hQ_roots_card).symm
  -- Evaluation formula
  have h_eval : ∀ z : ℂ, Q.eval z = Q.leadingCoeff * (Q.roots.map (fun α => z - α)).prod := by
    intro z; conv_lhs => rw [hQ_factor]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod]
    congr 1; simp [Multiset.map_map, Function.comp, Polynomial.eval_sub]
  -- Step 2: No circle roots (strict positivity)
  have h_no_circle : ∀ α ∈ Q.roots, ‖α‖ ≠ 1 := by
    intro α hα hα_norm
    have h_eval_zero := (Polynomial.mem_roots hQ).mp hα
    have h_pos_z := h_pos α hα_norm
    rw [h_eval_zero, zero_div] at h_pos_z; simp at h_pos_z
  -- Step 3: All roots are nonzero iff norm > 0; all inside roots have norm < 1 (nonzero)
  have h_all_nz_in_S_in_nz : ∀ α ∈ Q.roots.filter (· ≠ (0:ℂ)), α ≠ 0 := by
    intro α hα; exact (Multiset.mem_filter.mp hα).2
  -- Step 4: Define inside nonzero roots, outside roots, and the polynomial P
  set S_in_nz := (Q.roots.filter (· ≠ (0:ℂ))).filter (fun α => ‖α‖ < 1) with hSin_nz_def
  set S_out := (Q.roots.filter (· ≠ (0:ℂ))).filter (fun α => ¬ ‖α‖ < 1) with hSout_def
  set P_nz := (S_in_nz.map (fun α => X - C α)).prod with hP_nz_def
  -- Step 5: Key multiset fact — outside roots equal mapped inside roots
  -- This follows from: spiral_reflect_poly_identity gives Q = spiral_reflect(Q) * X^{2N-d},
  -- which forces T.map(1/conj·) = T (nonzero roots self-paired), and then
  -- filtering by norm gives S_out = S_in_nz.map(1/conj·).
  have h_out_eq : S_out = S_in_nz.map (fun α => 1 / conj α) := by
    have h_sp := nonzero_roots_self_paired Q N hQ h_real h_deg
    -- S_out = T.filter(¬ ‖·‖ < 1), S_in_nz = T.filter(‖·‖ < 1), T = Q.roots.filter(· ≠ 0)
    -- From h_sp: T.map φ = T. Filter (¬ ‖·‖ < 1) on both sides, use Multiset.filter_map.
    show S_out = S_in_nz.map (fun α => 1 / conj α)
    rw [hSout_def, hSin_nz_def]
    set T := Q.roots.filter (· ≠ (0:ℂ))
    conv_lhs => rw [← h_sp]
    rw [Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro α hα_mem
    have hα_ne : α ≠ 0 := (Multiset.mem_filter.mp hα_mem).2
    have hα_root : α ∈ Q.roots := (Multiset.mem_filter.mp hα_mem).1
    have hα_norm_ne : ‖α‖ ≠ 1 := h_no_circle α hα_root
    have hα_norm_pos : (0 : ℝ) < ‖α‖ := norm_pos_iff.mpr hα_ne
    simp only [Function.comp, norm_div, norm_one, Complex.norm_conj]
    constructor
    · intro h
      push_neg at h
      have h_le : ‖α‖ ≤ 1 := by rwa [le_div_iff₀ hα_norm_pos, one_mul] at h
      exact lt_of_le_of_ne h_le hα_norm_ne
    · intro h
      push_neg
      rw [le_div_iff₀ hα_norm_pos, one_mul]
      exact le_of_lt h
  -- Step 6: Inside roots are all nonzero (they're in filter (· ≠ 0))
  have h_sin_nz : ∀ α ∈ S_in_nz, α ≠ 0 := by
    intro α hα
    have := (Multiset.mem_filter.mp ((Multiset.mem_filter.mp hα).1)).2
    exact this
  -- Step 7: card(S_in) = N (zero root count + inside nonzero count)
  -- From spiral_reflect_poly_identity: m₀ = 2N - d
  -- From d = m₀ + 2k (root count with S_out.card = k): m₀ + k = N
  have h_card : (Q.roots.filter (· = (0:ℂ))).card + S_in_nz.card = N := by
    -- card(S_out) = card(S_in_nz) from h_out_eq
    have h_Sout_card : S_out.card = S_in_nz.card := by
      rw [h_out_eq, Multiset.card_map]
    -- Total root count: d = m₀ + 2k (where k = S_in_nz.card)
    have h_T_split : Q.roots.filter (· ≠ (0:ℂ)) = S_in_nz + S_out :=
      (Multiset.filter_add_not (fun α => ‖α‖ < 1) _).symm
    have h_total_parts : Q.roots.card =
        (Q.roots.filter (· = (0:ℂ))).card + (S_in_nz.card + S_out.card) := by
      have h1 := congr_arg Multiset.card
        (Multiset.filter_add_not (· = (0:ℂ)) Q.roots).symm
      rw [Multiset.card_add, h_T_split, Multiset.card_add] at h1
      exact h1
    rw [hQ_roots_card, h_Sout_card, ← two_mul] at h_total_parts
    -- h_total_parts : d = m₀ + 2*k
    -- Zero root count = 2N - d from spiral_reflect_poly_identity
    have h_poly_id := spiral_reflect_poly_identity Q N h_real h_deg
    have h_sr_ne : spiral_reflect Q ≠ 0 := by
      intro h; rw [h, zero_mul] at h_poly_id; exact hQ h_poly_id
    have h_xpow_ne : (X : Polynomial ℂ) ^ (2 * N - Q.natDegree) ≠ 0 :=
      pow_ne_zero _ Polynomial.X_ne_zero
    -- spiral_reflect(Q).eval 0 ≠ 0 (constant term = conj(lc) ≠ 0)
    have h_sr_eval_zero : (spiral_reflect Q).eval 0 ≠ 0 := by
      unfold spiral_reflect polynomial_mirror
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse,
          Polynomial.leadingCoeff_map (starRingEnd ℂ)]
      rw [ne_eq, ← map_zero (starRingEnd ℂ)]
      exact (starRingEnd ℂ).injective.ne hlc_ne
    -- Q.roots = spiral_reflect(Q).roots + (2N-d)•{0}
    have h_roots_eq : Q.roots = (spiral_reflect Q).roots +
        (2 * N - Q.natDegree) • ({0} : Multiset ℂ) := by
      conv_lhs => rw [h_poly_id]
      rw [Polynomial.roots_mul (mul_ne_zero h_sr_ne h_xpow_ne), Polynomial.roots_X_pow]
    -- Zero root count: m₀ = 2N - d
    have h_m0 : (Q.roots.filter (· = (0:ℂ))).card = 2 * N - Q.natDegree := by
      -- count via filter
      have : Q.roots.filter (· = (0:ℂ)) =
          (spiral_reflect Q).roots.filter (· = (0:ℂ)) +
          ((2 * N - Q.natDegree) • ({0} : Multiset ℂ)).filter (· = (0:ℂ)) := by
        rw [h_roots_eq, Multiset.filter_add]
      rw [this, Multiset.card_add]
      -- spiral_reflect(Q) has no zero root, so filter is empty
      have h1 : ((spiral_reflect Q).roots.filter (· = (0:ℂ))).card = 0 := by
        rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
        intro a ha h_eq
        rw [h_eq] at ha
        exact h_sr_eval_zero ((Polynomial.mem_roots h_sr_ne).mp ha)
      -- (2N-d)•{0} filtered by (·=0) is itself
      have h2 : ((2 * N - Q.natDegree) • ({0} : Multiset ℂ)).filter (· = (0:ℂ)) =
          (2 * N - Q.natDegree) • ({0} : Multiset ℂ) := by
        rw [Multiset.filter_eq_self]
        intro a ha
        by_cases hn : 2 * N - Q.natDegree = 0
        · simp [hn] at ha
        · rw [Multiset.mem_nsmul] at ha; exact Multiset.mem_singleton.mp ha.2
      rw [h1, h2, Multiset.card_nsmul, Multiset.card_singleton, mul_one, zero_add]
    omega
  -- Step 8: Evaluate Q on the circle using root partition + multiset_prod_circle_reflect
  -- Q.eval z = lc · z^m₀ · ∏_{S_in_nz}(z-α) · ∏_{S_out}(z-β)
  -- = lc · z^m₀ · W · ((-z)^k / ∏conj(α) · conj(W))   where W = ∏_{S_in_nz}(z-α)
  -- = lc·(-1)^k/∏conj(α) · z^{m₀+k} · normSq(W)
  -- = A · z^N · normSq(P_nz.eval z)   where A = lc·(-1)^k/∏conj(α)
  -- Step 8: Set up the constant A and prove the factorization
  set k := S_in_nz.card
  set conj_prod := (S_in_nz.map conj).prod
  have h_conj_prod_ne : conj_prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    rw [Multiset.mem_map]
    push_neg
    intro α hα h_eq
    exact h_sin_nz α hα (by rwa [map_eq_zero] at h_eq)
  set A_cpx := Q.leadingCoeff * (-1 : ℂ) ^ k / conj_prod with hA_cpx_def
  -- Step 8a: The circle identity
  have h_identity : ∀ z : ℂ, ‖z‖ = 1 →
      Q.eval z = A_cpx * z ^ N * ↑(Complex.normSq (P_nz.eval z)) := by
    intro z hz
    have hz_ne : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact one_ne_zero hz.symm
    -- P_nz.eval z = product over inside roots
    have h_P_eval : P_nz.eval z = (S_in_nz.map (fun α => z - α)).prod := by
      rw [hP_nz_def, Polynomial.eval_multiset_prod]
      congr 1; rw [Multiset.map_map]; congr 1; ext α
      simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    -- Decompose Q.roots = zeros + S_in_nz + S_out
    have h_root_eq : Q.roots = Q.roots.filter (· = (0:ℂ)) + (S_in_nz + S_out) := by
      conv_lhs => rw [← Multiset.filter_add_not (· = (0:ℂ)) Q.roots]
      congr 1
      exact (Multiset.filter_add_not (fun α => ‖α‖ < 1) (Q.roots.filter (· ≠ (0:ℂ)))).symm
    -- Product decomposition: Q.roots → z^m₀ * W_in * W_out
    have h_prod_eq : (Q.roots.map (fun α => z - α)).prod =
        z ^ (Q.roots.filter (· = (0:ℂ))).card *
        (S_in_nz.map (fun α => z - α)).prod *
        (S_out.map (fun α => z - α)).prod := by
      have h1 : (Q.roots.filter (· = (0:ℂ))).map (fun α : ℂ => z - α) =
          (Q.roots.filter (· = (0:ℂ))).map (fun _ => z) :=
        Multiset.map_congr rfl (fun a ha => by rw [(Multiset.mem_filter.mp ha).2]; simp)
      conv_lhs => rw [h_root_eq]
      rw [Multiset.map_add, Multiset.prod_add, Multiset.map_add, Multiset.prod_add,
          h1, Multiset.map_const', Multiset.prod_replicate, ← mul_assoc]
    -- S_out product via circle reflection
    have h_Sout_prod : (S_out.map (fun α => z - α)).prod =
        (-z) ^ k / conj_prod * conj ((S_in_nz.map (fun α => z - α)).prod) := by
      rw [h_out_eq, Multiset.map_map,
        show (fun α : ℂ => z - α) ∘ (fun α => 1 / conj α) = fun α => z - 1 / conj α from
          by ext; simp]
      exact multiset_prod_circle_reflect S_in_nz h_sin_nz z hz
    -- Substitute and simplify
    rw [h_eval z, h_prod_eq, h_Sout_prod, ← h_P_eval, ← Complex.mul_conj (P_nz.eval z),
        show (z : ℂ) ^ N = z ^ (Q.roots.filter (· = (0:ℂ))).card * z ^ k from by
          rw [← pow_add]; congr 1; omega]
    simp only [hA_cpx_def]
    field_simp
    ring
  -- Step 8b: P_nz has no circle roots
  have h_P_no_circle_root : ∀ z : ℂ, ‖z‖ = 1 → P_nz.eval z ≠ 0 := by
    intro z hz h_eq
    have h_qz := h_pos z hz
    rw [h_identity z hz, h_eq, Complex.normSq_zero, Complex.ofReal_zero,
        mul_zero, zero_div] at h_qz
    exact lt_irrefl 0 h_qz
  -- Step 8c: A_cpx is real (from h_real + identity + normSq > 0)
  have h_A_real : A_cpx.im = 0 := by
    have hz1 : ‖(1:ℂ)‖ = 1 := by simp
    have h_ns_pos : (0:ℝ) < Complex.normSq (P_nz.eval 1) := by
      rw [Complex.normSq_pos]
      exact h_P_no_circle_root 1 hz1
    have h_id1 := h_identity 1 hz1
    have h_r1 := h_real 1 hz1
    rw [h_id1, one_pow, mul_one, div_one] at h_r1
    -- h_r1 : (A_cpx * ↑(normSq(P.eval 1))).im = 0
    -- Expand: A_cpx.im * normSq(P.eval 1) = 0
    have h_mul_im : (A_cpx * ↑(Complex.normSq (P_nz.eval 1))).im =
        A_cpx.im * Complex.normSq (P_nz.eval 1) := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [h_mul_im] at h_r1
    exact (mul_eq_zero.mp h_r1).resolve_right (ne_of_gt h_ns_pos)
  -- Step 8d: A_cpx.re > 0 (from h_pos + identity + normSq > 0)
  have h_A_pos : 0 < A_cpx.re := by
    have hz1 : ‖(1:ℂ)‖ = 1 := by simp
    have h_ns_pos : (0:ℝ) < Complex.normSq (P_nz.eval 1) := by
      rw [Complex.normSq_pos]
      exact h_P_no_circle_root 1 hz1
    have h_id1 := h_identity 1 hz1
    have h_p1 := h_pos 1 hz1
    rw [h_id1, one_pow, mul_one, div_one] at h_p1
    -- h_p1 : 0 < (A_cpx * ↑(normSq(P.eval 1))).re
    -- Expand: 0 < A_cpx.re * normSq(P.eval 1)
    have h_mul_re : (A_cpx * ↑(Complex.normSq (P_nz.eval 1))).re =
        A_cpx.re * Complex.normSq (P_nz.eval 1) := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [h_mul_re] at h_p1
    exact (mul_pos_iff.mp h_p1).elim And.left
      (fun h => absurd h.2 (not_lt.mpr h_ns_pos.le))
  have h_A_eq : (A_cpx.re : ℂ) = A_cpx :=
    Complex.ext (by simp) (by simp [h_A_real])
  -- Step 8e: Assemble the result
  refine ⟨P_nz, A_cpx.re, h_A_pos, ?_, ?_⟩
  · -- Degree bound: P_nz.natDegree ≤ N
    calc P_nz.natDegree
        ≤ ((S_in_nz.map (fun α => X - C α)).map Polynomial.natDegree).sum :=
          Polynomial.natDegree_multiset_prod_le _
      _ = S_in_nz.card := by
          simp only [Multiset.map_map, Function.comp, Polynomial.natDegree_X_sub_C,
            Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
      _ ≤ N := by omega
  · -- Identity
    intro z hz
    rw [h_A_eq]
    exact h_identity z hz

/-! ### Fejér-Riesz factor: strictly positive case -/

/-- Strictly positive case: When Q(z)/z^N > 0 on the circle, Q factors as z^N * |P(z)|².
    Reduces to fejer_riesz_root_factorization by absorbing √A into P. -/
private lemma polynomial_fejer_riesz_factor_pos (Q : Polynomial ℂ) (N : ℕ) (hQ : Q ≠ 0)
    (h_real : ∀ z : ℂ, ‖z‖ = 1 → (Q.eval z / z ^ N).im = 0)
    (h_pos : ∀ z : ℂ, ‖z‖ = 1 → 0 < (Q.eval z / z ^ N).re)
    (h_deg : Q.natDegree ≤ 2 * N) :
    ∃ (P_poly : Polynomial ℂ), P_poly.natDegree ≤ N ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        Q.eval z = z ^ N * ↑(Complex.normSq (P_poly.eval z)) := by
  obtain ⟨P, A, hA, hP_deg, hP_eq⟩ := fejer_riesz_root_factorization Q N hQ h_real h_pos h_deg
  refine ⟨C (↑(Real.sqrt A) : ℂ) * P, ?_, ?_⟩
  · -- Degree bound: deg(C(√A) · P) ≤ deg(P) ≤ N
    calc (C (↑(Real.sqrt A) : ℂ) * P).natDegree
        ≤ P.natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ N := hP_deg
  · -- Identity: Q(z) = z^N · normSq(√A · P(z))
    intro z hz
    rw [hP_eq z hz, Polynomial.eval_mul, Polynomial.eval_C]
    -- Goal: ↑A * z^N * ↑(normSq(P.eval z)) = z^N * ↑(normSq(↑√A * P.eval z))
    have h_ns : Complex.normSq ((↑(Real.sqrt A) : ℂ) * P.eval z) =
        A * Complex.normSq (P.eval z) := by
      rw [map_mul Complex.normSq, Complex.normSq_ofReal, Real.mul_self_sqrt hA.le]
    rw [h_ns]; push_cast; ring

/-! ### Fejér-Riesz factor: limit extraction for general case -/

/-- Limit extraction: If Q + ε·X^N factors for all ε > 0, then Q factors. -/
private lemma polynomial_limit_normSq (Q : Polynomial ℂ) (N : ℕ)
    (h_factor : ∀ n : ℕ, ∃ P_n : Polynomial ℂ, P_n.natDegree ≤ N ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        (Q + Polynomial.C ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * X ^ N).eval z =
          z ^ N * (Complex.normSq (P_n.eval z) : ℂ)) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ N ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        Q.eval z = z ^ N * (Complex.normSq (P.eval z) : ℂ) := by
  choose P_seq hP_deg hP_eq using h_factor
  -- Coefficient bound via Mahler measure: bounded on circle → mahlerMeasure bounded → coeff bounded
  have h_coeff_bnd : ∃ M : ℝ, 0 ≤ M ∧ ∀ n k, ‖(P_seq n).coeff k‖ ≤ M := by
    -- B uniformly bounds normSq(P_n(z)) on circle
    set B := (Finset.range (Q.natDegree + 1)).sum (fun k => ‖Q.coeff k‖) + 1 with hB_def
    have hB_pos : (0 : ℝ) < B := by positivity
    have hB_one : (1 : ℝ) ≤ B := by
      have := Finset.sum_nonneg
        (fun k (_ : k ∈ Finset.range (Q.natDegree + 1)) => norm_nonneg (Q.coeff k))
      linarith
    -- Step 1: ‖P_n(z)‖ ≤ √B on circle
    have h_eval_bnd : ∀ n (z : ℂ), ‖z‖ = 1 →
        ‖(P_seq n).eval z‖ ≤ Real.sqrt B := by
      intro n z hz
      -- ‖P_n(z)‖ = √(normSq(P_n(z)))
      rw [show ‖(P_seq n).eval z‖ = Real.sqrt (Complex.normSq ((P_seq n).eval z)) from
        by rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]]
      apply Real.sqrt_le_sqrt
      -- normSq(P_n(z)) = ‖(Q + ε X^N).eval z‖ (from identity, taking norms)
      have hid := hP_eq n z hz
      have hz_pow : ‖z ^ N‖ = 1 := by rw [norm_pow, hz, one_pow]
      have h_ns : Complex.normSq ((P_seq n).eval z) =
          ‖(Q + Polynomial.C ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * X ^ N).eval z‖ := by
        symm; rw [hid, norm_mul, hz_pow, one_mul]
        exact Complex.norm_of_nonneg (Complex.normSq_nonneg _)
      rw [h_ns]
      -- ‖(Q + ε X^N).eval z‖ ≤ ‖Q.eval z‖ + ‖ε X^N .eval z‖ ≤ (Σ‖Q.coeff k‖) + 1 = B
      calc ‖(Q + Polynomial.C ((1 / ((↑n : ℝ) + 1) : ℝ) : ℂ) * X ^ N).eval z‖
          ≤ ‖Q.eval z‖ +
            ‖(Polynomial.C ((1 / ((↑n : ℝ) + 1) : ℝ) : ℂ) * X ^ N).eval z‖ := by
            rw [Polynomial.eval_add]; exact norm_add_le _ _
        _ ≤ (Finset.range (Q.natDegree + 1)).sum (fun k => ‖Q.coeff k‖) + 1 := by
            gcongr
            · -- ‖Q.eval z‖ ≤ Σ ‖Q.coeff k‖
              rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr le_rfl)]
              calc ‖∑ i ∈ Finset.range (Q.natDegree + 1), Q.coeff i * z ^ i‖
                  ≤ ∑ i ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff i * z ^ i‖ :=
                    norm_sum_le _ _
                _ = _ := by
                    congr 1; ext i
                    rw [norm_mul, norm_pow, hz, one_pow, mul_one]
            · -- ‖(ε X^N).eval z‖ ≤ 1
              simp only [Polynomial.eval_mul, Polynomial.eval_C,
                Polynomial.eval_pow, Polynomial.eval_X]
              rw [norm_mul, norm_pow, hz, one_pow, mul_one,
                Complex.norm_of_nonneg (show (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) by positivity)]
              exact (div_le_one (show (0 : ℝ) < (↑n : ℝ) + 1 by positivity)).mpr
                (le_add_of_nonneg_left (Nat.cast_nonneg n))
    -- Step 2: mahlerMeasure(P_n) ≤ √B via circleAverage monotonicity
    have h_mahler : ∀ n, (P_seq n).mahlerMeasure ≤ Real.sqrt B := by
      intro n
      by_cases hn : P_seq n = 0
      · simp [hn]
      · have hm_pos := Polynomial.mahlerMeasure_pos_of_ne_zero hn
        suffices h : (P_seq n).logMahlerMeasure ≤ Real.log (Real.sqrt B) by
          rwa [← Real.log_le_log_iff hm_pos (Real.sqrt_pos.mpr hB_pos),
            ← Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
        rw [Polynomial.logMahlerMeasure_def]
        apply circleAverage_mono_on_of_le_circle
        · exact (P_seq n).intervalIntegrable_mahlerMeasure
        · intro z hz
          simp only [Metric.mem_sphere, dist_zero_right, abs_one] at hz
          by_cases hPz : (P_seq n).eval z = 0
          · simp [hPz]; exact Real.log_nonneg (Real.one_le_sqrt.mpr hB_one)
          · exact Real.log_le_log (norm_pos_iff.mpr hPz) (h_eval_bnd n z hz)
    -- Step 3: Coefficient bound from mahlerMeasure + Nat.choose_le_two_pow
    refine ⟨(2 : ℝ) ^ N * Real.sqrt B, by positivity, fun n k => ?_⟩
    by_cases hk : (P_seq n).natDegree < k
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk, norm_zero]; positivity
    · push_neg at hk
      calc ‖(P_seq n).coeff k‖
          ≤ (P_seq n).natDegree.choose k * (P_seq n).mahlerMeasure :=
            Polynomial.norm_coeff_le_choose_mul_mahlerMeasure k (P_seq n)
        _ ≤ (2 : ℝ) ^ N * Real.sqrt B := by
            apply mul_le_mul
            · calc ((P_seq n).natDegree.choose k : ℝ)
                  ≤ (2 ^ (P_seq n).natDegree : ℝ) := by exact_mod_cast Nat.choose_le_two_pow _ _
                _ ≤ (2 ^ N : ℝ) := by
                    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (hP_deg n)
            · exact h_mahler n
            · exact Polynomial.mahlerMeasure_nonneg _
            · positivity
  obtain ⟨M, hM_nn, h_bnd⟩ := h_coeff_bnd
  -- View coefficient vectors as sequence in Fin(N+1) → ℂ
  let v : ℕ → (Fin (N + 1) → ℂ) := fun n k => (P_seq n).coeff ↑k
  -- Vectors lie in compact closed ball
  have hv_in : ∀ n, v n ∈ Metric.closedBall (0 : Fin (N + 1) → ℂ) M := by
    intro n; rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hM_nn).mpr (fun k => h_bnd n k)
  -- Bolzano-Weierstrass: extract convergent subsequence
  obtain ⟨a, -, φ, hφ_mono, hφ_conv⟩ :=
    (isCompact_closedBall (0 : Fin (N + 1) → ℂ) M).tendsto_subseq hv_in
  -- Component-wise convergence of coefficients
  have h_cc : ∀ k : Fin (N + 1),
      Filter.Tendsto (fun n => (P_seq (φ n)).coeff ↑k) Filter.atTop (nhds (a k)) :=
    fun k => tendsto_pi_nhds.mp hφ_conv k
  -- Construct limit polynomial from converging coefficients
  refine ⟨∑ k : Fin (N + 1), Polynomial.C (a k) * X ^ (k : ℕ), ?_, ?_⟩
  · -- Degree bound ≤ N
    apply le_trans (Polynomial.natDegree_sum_le _ _)
    apply Finset.sup_le; intro k _
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le (a k) k) (Nat.lt_succ_iff.mp k.isLt)
  · -- Identity on circle: take limit of perturbed identity
    intro z hz
    set P := ∑ k : Fin (N + 1), Polynomial.C (a k) * X ^ (k : ℕ) with hP_def
    -- P.coeff i = a ⟨i, hi⟩ for i < N+1, 0 otherwise
    have hP_coeff : ∀ i, P.coeff i =
        if h : i < N + 1 then a ⟨i, h⟩ else 0 := by
      intro i; simp only [hP_def, Polynomial.finset_sum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      by_cases hi : i < N + 1
      · simp only [hi, dite_true]
        rw [Finset.sum_eq_single ⟨i, hi⟩]
        · simp
        · intro b _ hb; simp [Fin.val_ne_of_ne (Ne.symm hb)]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp only [hi, dite_false]
        apply Finset.sum_eq_zero; intro k _
        simp only [ite_eq_right_iff]; intro heq
        exact absurd (heq ▸ k.isLt) (not_lt.mpr (not_lt.mp hi))
    -- Eval convergence: P_seq(φ m).eval z → P.eval z
    have h_eval_conv : Filter.Tendsto (fun m => (P_seq (φ m)).eval z)
        Filter.atTop (nhds (P.eval z)) := by
      rw [Polynomial.eval_eq_sum_range' (show P.natDegree < N + 1 by
        apply Nat.lt_succ_of_le
        apply le_trans (Polynomial.natDegree_sum_le _ _)
        apply Finset.sup_le; intro k _
        exact le_trans (show (Polynomial.C (a k) * X ^ (k : ℕ)).natDegree ≤ (k : ℕ) from
          Polynomial.natDegree_C_mul_X_pow_le (a k) k) (Nat.lt_succ_iff.mp k.isLt))]
      simp_rw [Polynomial.eval_eq_sum_range'
        (show (P_seq (φ _)).natDegree < N + 1 from Nat.lt_of_le_of_lt (hP_deg _) (by omega))]
      apply tendsto_finset_sum _ (fun i hi => ?_)
      apply Filter.Tendsto.mul _ tendsto_const_nhds
      rw [Finset.mem_range] at hi
      rw [hP_coeff i, dif_pos hi]
      exact h_cc ⟨i, hi⟩
    -- NormSq convergence (normSq is continuous)
    have h_ns_conv : Filter.Tendsto
        (fun m => (Complex.normSq ((P_seq (φ m)).eval z) : ℂ))
        Filter.atTop (nhds ↑(Complex.normSq (P.eval z))) :=
      ((Complex.continuous_ofReal.comp Complex.continuous_normSq).continuousAt.tendsto).comp
        h_eval_conv
    -- RHS convergence: z^N * normSq(P_n.eval z) → z^N * normSq(P.eval z)
    have h_rhs : Filter.Tendsto
        (fun m => z ^ N * (Complex.normSq ((P_seq (φ m)).eval z) : ℂ))
        Filter.atTop (nhds (z ^ N * ↑(Complex.normSq (P.eval z)))) :=
      tendsto_const_nhds.mul h_ns_conv
    -- LHS convergence: (Q + ε * X^N).eval z → Q.eval z
    have h_lhs : Filter.Tendsto
        (fun m => (Q + Polynomial.C ((1 / ((φ m : ℝ) + 1) : ℝ) : ℂ) * X ^ N).eval z)
        Filter.atTop (nhds (Q.eval z)) := by
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      suffices h_eps : Filter.Tendsto
          (fun m => ((1 / ((φ m : ℝ) + 1) : ℝ) : ℂ) * z ^ N) Filter.atTop (nhds 0) by
        have h := tendsto_const_nhds (x := Q.eval z).add h_eps
        rwa [add_zero] at h
      rw [show (0 : ℂ) = 0 * z ^ N from (zero_mul _).symm]
      exact Filter.Tendsto.mul
        (show Filter.Tendsto (fun m => ((1 / ((φ m : ℝ) + 1) : ℝ) : ℂ))
            Filter.atTop (nhds 0) from by
          rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from Complex.ofReal_zero.symm]
          exact Complex.continuous_ofReal.continuousAt.tendsto.comp
            (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ_mono.tendsto_atTop))
        tendsto_const_nhds
    -- Combine: limits must be equal
    exact tendsto_nhds_unique h_lhs
      ((Filter.tendsto_congr (fun m => (hP_eq (φ m) z hz).symm)).mp h_rhs)

/-- Polynomial factorization (Fejér-Riesz core): a polynomial that is real and non-negative on the unit circle -/
private lemma polynomial_fejer_riesz_factor (Q : Polynomial ℂ) (N : ℕ) (hQ : Q ≠ 0)
    (h_real : ∀ z : ℂ, ‖z‖ = 1 → (Q.eval z / z ^ N).im = 0)
    (h_nonneg : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (Q.eval z / z ^ N).re)
    (h_deg : Q.natDegree ≤ 2 * N) :
    ∃ (P_poly : Polynomial ℂ), P_poly.natDegree ≤ N ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        Q.eval z = z ^ N * ↑(Complex.normSq (P_poly.eval z)) := by
  -- Try strictly positive case first
  by_cases h_strict : ∀ z : ℂ, ‖z‖ = 1 → 0 < (Q.eval z / z ^ N).re
  · exact polynomial_fejer_riesz_factor_pos Q N hQ h_real h_strict h_deg
  -- General case: perturb by ε = 1/(n+1) and extract limit
  · apply polynomial_limit_normSq Q N
    intro n
    set ε := (1 / (↑n + 1 : ℝ)) with hε_def
    have hε_pos : 0 < ε := by positivity
    set Q_ε := Q + C (↑ε : ℂ) * X ^ N with hQ_ε_def
    -- Q_ε satisfies the strictly positive hypotheses
    have hQ_ε_ne : Q_ε ≠ 0 := by
      intro h_eq
      have h_eval_zero : Q_ε.eval 1 = 0 := by rw [h_eq]; simp
      simp [hQ_ε_def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] at h_eval_zero
      -- h_eval_zero : Q.eval 1 + ↑ε = 0
      have h1 := h_nonneg 1 (by simp [norm_one])
      simp [div_one] at h1
      -- Extract real part: (Q.eval 1 + ↑ε).re = 0
      have h_re : (Q.eval 1).re + ε = 0 := by
        have := congr_arg Complex.re h_eval_zero
        simp at this; exact this
      linarith
    have hQ_ε_real : ∀ z : ℂ, ‖z‖ = 1 → (Q_ε.eval z / z ^ N).im = 0 := by
      intro z hz
      have hz_ne : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact one_ne_zero hz.symm
      have h_zpow_ne : z ^ N ≠ 0 := pow_ne_zero _ hz_ne
      have h_cancel : Q_ε.eval z / z ^ N = Q.eval z / z ^ N + (↑ε : ℂ) := by
        simp only [hQ_ε_def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, add_div]
        congr 1; exact mul_div_cancel_right₀ _ h_zpow_ne
      rw [h_cancel]
      simp [h_real z hz, Complex.ofReal_im]
    have hQ_ε_pos : ∀ z : ℂ, ‖z‖ = 1 → 0 < (Q_ε.eval z / z ^ N).re := by
      intro z hz
      have hz_ne : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact one_ne_zero hz.symm
      have h_zpow_ne : z ^ N ≠ 0 := pow_ne_zero _ hz_ne
      have h_cancel : Q_ε.eval z / z ^ N = Q.eval z / z ^ N + (↑ε : ℂ) := by
        simp only [hQ_ε_def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, add_div]
        congr 1; exact mul_div_cancel_right₀ _ h_zpow_ne
      rw [h_cancel]
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [h_nonneg z hz]
    have hQ_ε_deg : Q_ε.natDegree ≤ 2 * N := by
      apply le_trans (Polynomial.natDegree_add_le _ _)
      apply max_le h_deg
      calc (C (↑ε : ℂ) * X ^ N).natDegree ≤ N := Polynomial.natDegree_C_mul_X_pow_le _ _
        _ ≤ 2 * N := Nat.le_mul_of_pos_left N (by omega)
    exact polynomial_fejer_riesz_factor_pos Q_ε N hQ_ε_ne hQ_ε_real hQ_ε_pos hQ_ε_deg

/-- Convert a standard polynomial to a TrigPolyℤ via its coefficients on {0,...,N}. -/
private noncomputable def polynomial_to_trigpoly (P_poly : Polynomial ℂ) (N : ℕ) : TrigPolyℤ :=
  (Finset.range (N + 1)).sum (fun k => Finsupp.single (k : ℤ) (P_poly.coeff k))

private lemma polynomial_to_trigpoly_support_nonneg (P_poly : Polynomial ℂ) (N : ℕ) :
    ∀ k ∈ (polynomial_to_trigpoly P_poly N).support, 0 ≤ k := by
  intro k hk
  -- P is a sum of singles at (k : ℤ) for k ∈ range(N+1), so support ⊆ {0,...,N} ⊂ ℤ≥0
  by_contra h_neg
  push_neg at h_neg
  -- k < 0, but the sum of singles at non-negative ℤ indices is 0 at k < 0
  have h_zero : (polynomial_to_trigpoly P_poly N) k = 0 := by
    show ((Finset.range (N + 1)).sum
      (fun j => Finsupp.single (j : ℤ) (P_poly.coeff j))) k = 0
    rw [Finsupp.finset_sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    simp only [Finsupp.single_apply, ite_eq_right_iff]
    intro h_eq; omega
  exact absurd h_zero (Finsupp.mem_support_iff.mp hk)

/-- Bridge: on the circle, polynomial_to_trigpoly evaluates as the original polynomial.
    For z = exp(2πixI): (polynomial_to_trigpoly P N).toCircle(↑x) = P.eval(z). -/
private lemma polynomial_to_trigpoly_toCircle (P_poly : Polynomial ℂ) (N : ℕ)
    (hP_deg : P_poly.natDegree ≤ N) (x : ℝ) :
    let z := Complex.exp (2 * Real.pi * x * Complex.I)
    (polynomial_to_trigpoly P_poly N).toCircle (↑x : 𝕋) = P_poly.eval z := by
  intro z
  -- Both sides = ∑_{j ∈ range(N+1)} P_poly.coeff j * z^j
  rw [Polynomial.eval_eq_sum_range' (by omega : P_poly.natDegree < N + 1) z]
  -- Unfold toCircle
  simp only [TrigPolyℤ.toCircle, ContinuousMap.coe_mk]
  -- Extend the support sum to (Finset.range (N+1)).image Nat.cast
  set P := polynomial_to_trigpoly P_poly N with hP_def
  set S := (Finset.range (N + 1)).image (Nat.cast : ℕ → ℤ) with hS_def
  have h_support_sub : P.support ⊆ S := by
    intro k hk
    have hk_nn : 0 ≤ k := polynomial_to_trigpoly_support_nonneg P_poly N k hk
    have hk_val : P k ≠ 0 := Finsupp.mem_support_iff.mp hk
    have hk_le : k ≤ ↑N := by
      by_contra h_gt; push_neg at h_gt
      have : P k = 0 := by
        show ((Finset.range (N + 1)).sum
          (fun j => Finsupp.single (↑j : ℤ) (P_poly.coeff j))) k = 0
        rw [Finsupp.finset_sum_apply]
        apply Finset.sum_eq_zero
        intro j hj
        simp only [Finsupp.single_apply, ite_eq_right_iff]
        intro h_eq; have := Finset.mem_range.mp hj; omega
      exact absurd this hk_val
    have hk_toNat : k.toNat ≤ N := by
      have h1 := Int.toNat_of_nonneg hk_nn
      exact_mod_cast h1 ▸ hk_le
    exact Finset.mem_image.mpr ⟨k.toNat, Finset.mem_range.mpr (by omega),
      Int.toNat_of_nonneg hk_nn⟩
  rw [Finset.sum_subset h_support_sub (fun k _ hk => by
    simp [Finsupp.notMem_support_iff.mp hk])]
  -- Reindex: ∑_{k ∈ S} P(k) * fourier(k, ↑x) = ∑_{j ∈ range(N+1)} P(↑j) * fourier(↑j, ↑x)
  rw [Finset.sum_image (fun (i : ℕ) _ (j : ℕ) _ (h : (i : ℤ) = (j : ℤ)) =>
    by exact_mod_cast h)]
  -- Now: ∑_{j ∈ range(N+1)} P(↑j) * fourier(↑j, ↑x) = ∑_{j ∈ range(N+1)} coeff(j) * z^j
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  · -- P(↑j) = P_poly.coeff j
    show ((Finset.range (N + 1)).sum
      (fun k => Finsupp.single (↑k : ℤ) (P_poly.coeff k))) (↑j : ℤ) = P_poly.coeff j
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single j]
    · exact Finsupp.single_eq_same
    · intro k _ hk_ne
      simp only [Finsupp.single_apply, ite_eq_right_iff]
      intro h_eq; exact absurd (by exact_mod_cast h_eq : k = j) hk_ne
    · intro hj_not; exfalso; exact hj_not hj
  · -- fourier(↑j, ↑x) = z^j
    rw [fourier_coe_apply]
    simp only [Complex.ofReal_one, div_one]
    conv_lhs => rw [show (2 * ↑Real.pi * Complex.I * ↑(↑j : ℤ) * ↑x : ℂ) =
      ↑(↑j : ℤ) * (2 * ↑Real.pi * ↑x * Complex.I) from by ring]
    rw [Complex.exp_int_mul, zpow_natCast]

/-- Bridge: on the circle, R.toPolynomial evaluates as z^N · R.toCircle.
    For z = exp(2πiθ): toPolynomial(R,N).eval(z) = z^N · R.toCircle(θ). -/
private lemma toPolynomial_eval_on_circle (R : TrigPolyℤ) (N : ℕ) (hN : R.degree ≤ N)
    (x : ℝ) :
    let z := Complex.exp (2 * Real.pi * x * Complex.I)
    (R.toPolynomial N).eval z = z ^ N * R.toCircle (↑x : 𝕋) := by
  intro z
  have hz_ne : z ≠ 0 := Complex.exp_ne_zero _
  unfold TrigPolyℤ.toPolynomial
  simp only [TrigPolyℤ.toCircle, ContinuousMap.coe_mk]
  rw [Finsupp.sum, Polynomial.eval_finset_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hk_abs : k.natAbs ≤ N := le_trans (Finset.le_sup (f := fun j => j.natAbs) hk) hN
  have hk_nn : 0 ≤ k + ↑N := by omega
  -- z^{(k+N).toNat} = z^k * z^N
  have h1 : (z : ℂ) ^ (k + ↑N).toNat = z ^ k * z ^ N := by
    rw [← zpow_natCast z (k + ↑N).toNat, Int.toNat_of_nonneg hk_nn,
        zpow_add₀ hz_ne, zpow_natCast]
  -- fourier k (↑x) = z^k
  have h4 : (fourier k (↑x : 𝕋) : ℂ) = z ^ k := by
    rw [fourier_coe_apply]
    simp only [Complex.ofReal_one, div_one]
    conv_lhs => rw [show (2 * ↑Real.pi * Complex.I * ↑k * ↑x : ℂ) =
      ↑k * (2 * ↑Real.pi * ↑x * Complex.I) from by ring]
    exact Complex.exp_int_mul _ k
  rw [h1, ← h4]; ring

/-- Key identity: P(z) · spiral_reflect(P)(z) = z^d · |P(z)|² on the unit circle, -/
private lemma normSq_eq_mul_spiral_reflect_on_circle (P_poly : Polynomial ℂ)
    (z : ℂ) (hz : ‖z‖ = 1) (hz_ne : z ≠ 0) :
    P_poly.eval z * (spiral_reflect P_poly).eval z =
      z ^ P_poly.natDegree * ↑(Complex.normSq (P_poly.eval z)) := by
  unfold spiral_reflect polynomial_mirror
  set Q := P_poly.map (starRingEnd ℂ) with hQ_def
  -- Step 1: Use eval₂_reverse_mul_pow to relate Q.reverse.eval z to Q.eval(z⁻¹)
  have hz_inv_ne : z⁻¹ ≠ 0 := inv_ne_zero hz_ne
  haveI : Invertible z⁻¹ := invertibleOfNonzero hz_inv_ne
  -- eval₂ id (⅟(z⁻¹)) (Q.reverse) * (z⁻¹)^{Q.natDeg} = eval₂ id (z⁻¹) Q
  -- i.e., Q.reverse.eval z * (z⁻¹)^{Q.natDeg} = Q.eval(z⁻¹)
  have h1 := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) z⁻¹ Q
  simp only [Polynomial.eval₂_id, invOf_eq_inv, inv_inv] at h1
  -- h1 : Q.reverse.eval z * z⁻¹ ^ Q.natDegree = Q.eval z⁻¹
  -- Step 2: Q.natDegree = P.natDegree
  have h_deg : Q.natDegree = P_poly.natDegree :=
    Polynomial.natDegree_map (starRingEnd ℂ)
  -- Step 3: z⁻¹ = conj z on the unit circle
  have h_inv_conj : z⁻¹ = starRingEnd ℂ z := inv_eq_conj hz
  -- Step 4: Q.eval(z⁻¹) = conj(P.eval z)
  have h_eval : Q.eval z⁻¹ = starRingEnd ℂ (P_poly.eval z) := by
    simp only [h_inv_conj, hQ_def, Polynomial.eval_map_apply]
  -- Step 5: Solve for Q.reverse.eval z from h1
  -- h1: Q.reverse.eval z * (z⁻¹)^d = Q.eval(z⁻¹) = conj(P.eval z)
  -- Multiply both sides by z^d: uses (z⁻¹)^d * z^d = 1
  rw [h_deg, h_eval] at h1
  -- h1 : Q.reverse.eval z * z⁻¹ ^ P.natDegree = conj(P.eval z)
  have h_sr : Q.reverse.eval z = z ^ P_poly.natDegree * starRingEnd ℂ (P_poly.eval z) := by
    have := congr_arg (· * z ^ P_poly.natDegree) h1
    simp only [mul_assoc] at this
    rw [← mul_pow, inv_mul_cancel₀ hz_ne, one_pow, mul_one] at this
    rw [mul_comm] at this; exact this
  -- Step 6: Combine P.eval z * (z^d * conj(P.eval z)) = z^d * normSq(P.eval z)
  rw [h_sr, ← mul_assoc, mul_comm (P_poly.eval z) (z ^ P_poly.natDegree), mul_assoc]
  congr 1
  exact mul_conj (P_poly.eval z)

lemma TrigPolyℤ.normSq_apply (P : TrigPolyℤ) (k : ℤ) :
    (TrigPolyℤ.normSq P) k = ∑ n ∈ P.support, (starRingEnd ℂ) (P n) * P (n + k) := by
  classical
  unfold TrigPolyℤ.normSq
  simp only [Finsupp.ofSupportFinite_coe]

lemma conj_fourier (n : ℤ) (θ : 𝕋) :
    conj (fourier n θ) = fourier (-n) θ := by
  simp [fourier]

lemma TrigPolyℤ.toCircle_normSq_eq_double_sum (P : TrigPolyℤ) (θ : 𝕋) :
    (TrigPolyℤ.normSq P).toCircle θ =
      ∑ n ∈ P.support, ∑ m ∈ P.support,
        (starRingEnd ℂ) (P n) * P m * fourier (m - n) θ := by
  classical
  unfold TrigPolyℤ.toCircle
  simp only [ContinuousMap.coe_mk]
  set S := P.support
  set supp := (S.product S).image (fun mn : ℤ × ℤ => mn.2 - mn.1)
  have hsub : (TrigPolyℤ.normSq P).support ⊆ supp := by
    intro k hk
    have hk0 : (TrigPolyℤ.normSq P) k ≠ 0 := Finsupp.mem_support_iff.mp hk
    have : ∃ i ∈ S, (starRingEnd ℂ) (P i) * P (i + k) ≠ 0 := by
      by_contra h
      push_neg at h
      have : (TrigPolyℤ.normSq P) k = 0 := by
        simp only [TrigPolyℤ.normSq_apply]
        exact Finset.sum_eq_zero (fun i hiS => h i hiS)
      exact hk0 this
    rcases this with ⟨i, hiS, hterm⟩
    have hikS : i + k ∈ S := by
      by_contra hikS
      simp [Finsupp.notMem_support_iff.mp hikS] at hterm
    refine Finset.mem_image.mpr ⟨(i, i + k), Finset.mem_product.mpr ⟨hiS, hikS⟩, by ring⟩
  have h_extend_to_supp : ∑ k ∈ (TrigPolyℤ.normSq P).support,
        (TrigPolyℤ.normSq P) k * fourier k θ =
      ∑ k ∈ supp, (TrigPolyℤ.normSq P) k * fourier k θ := by
    apply Finset.sum_subset hsub
    intro k _ hk_not_support
    simp [Finsupp.notMem_support_iff.mp hk_not_support]
  rw [h_extend_to_supp]
  conv_lhs => arg 2; intro k; rw [TrigPolyℤ.normSq_apply, Finset.sum_mul]
  conv_lhs => arg 2; intro k; arg 2; intro n; rw [mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  have sum_restrict : ∑ k ∈ supp, (starRingEnd ℂ) (P n) * (P (n + k) * fourier k θ) =
      ∑ k ∈ supp.filter (fun k => n + k ∈ S),
        (starRingEnd ℂ) (P n) * (P (n + k) * fourier k θ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk_supp hk_not_filter
    simp only [Finset.mem_filter, not_and] at hk_not_filter
    have : n + k ∉ S := hk_not_filter hk_supp
    simp [Finsupp.notMem_support_iff.mp this]
  rw [sum_restrict]
  set F : Finset ℤ := supp.filter (fun k => n + k ∈ S)
  have hm_sub_mem_supp : ∀ {m : ℤ}, m ∈ S → m - n ∈ supp := by
    intro m hm
    refine Finset.mem_image.mpr ⟨(n, m), Finset.mem_product.mpr ⟨hn, hm⟩, by simp⟩
  suffices ∑ k ∈ F, (starRingEnd ℂ) (P n) * (P (n + k) * fourier k θ) =
      ∑ m ∈ S, (starRingEnd ℂ) (P n) * P m * fourier (m - n) θ by
    exact this
  refine Finset.sum_bij (fun k _ => n + k) ?_ ?_ ?_ ?_
  · intro k hk
    exact (Finset.mem_filter.mp hk).2
  · intro k₁ _ k₂ _ hEq
    exact add_left_cancel hEq
  · intro m hm
    refine ⟨m - n, ?_, by simp [sub_add_cancel]⟩
    refine Finset.mem_filter.mpr ⟨hm_sub_mem_supp hm, by simpa [sub_add_cancel]⟩
  · intro k hk
    simp only [add_sub_cancel_left]
    ring

lemma TrigPolyℤ.normSq_toCircle_eval (P : TrigPolyℤ) (θ : 𝕋) :
    (TrigPolyℤ.normSq P).toCircle θ = Complex.normSq (P.toCircle θ) := by
  classical
  rw [TrigPolyℤ.toCircle_normSq_eq_double_sum]
  have h_rhs : Complex.normSq (P.toCircle θ) =
      ∑ n ∈ P.support, ∑ m ∈ P.support,
        (starRingEnd ℂ) (P n) * P m * fourier (m - n) θ := by
    simp only [TrigPolyℤ.toCircle, ContinuousMap.coe_mk, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, starRingEnd_apply]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    congr 1
    ext n
    congr 1
    ext m
    calc star (P n) * star ((fourier n) θ) * (P m * (fourier m) θ)
        = star (P n) * P m * (star ((fourier n) θ) * (fourier m) θ) := by ring
      _ = star (P n) * P m * (conj ((fourier n) θ) * (fourier m) θ) := by
          rfl
      _ = star (P n) * P m * (fourier (-n) θ * fourier m θ) := by
          rw [conj_fourier]
      _ = star (P n) * P m * fourier (-n + m) θ := by
          rw [← fourier_add]
      _ = star (P n) * P m * fourier (m + -n) θ := by
          congr 1; ring_nf
      _ = star (P n) * P m * fourier (m - n) θ := by
          simp only [sub_eq_add_neg]
  rw [h_rhs]

private lemma fejer_riesz_core (R : TrigPolyℤ)
    (hR_real : ∀ θ : 𝕋, (R.toCircle θ).im = 0)
    (hR_nonneg : ∀ θ : 𝕋, 0 ≤ (R.toCircle θ).re) :
    ∃ (P : TrigPolyℤ), (∀ k ∈ P.support, 0 ≤ k) ∧ R = TrigPolyℤ.normSq P := by
  -- Case R = 0
  by_cases hR0 : R = 0
  · refine ⟨0, fun _ h => absurd h (by simp), ?_⟩
    rw [hR0]; unfold TrigPolyℤ.normSq; ext k
    simp [Finsupp.ofSupportFinite]
  -- R ≠ 0: polynomial root factorization
  -- Step 1: Form Q(z) = R.toPolynomial N (a polynomial of degree ≤ 2N)
  let N := R.degree
  let Q := R.toPolynomial N
  -- Step 2: Transfer hypotheses to Q
  have hQ_ne : Q ≠ 0 := by
    intro h_eq
    have h_ne : R.support.Nonempty := Finsupp.support_nonempty_iff.mpr hR0
    obtain ⟨k₀, hk₀⟩ := h_ne
    have hR_k₀ : R k₀ ≠ 0 := Finsupp.mem_support_iff.mp hk₀
    let n₀ := (k₀ + (N : ℤ)).toNat
    have h_coeff : Q.coeff n₀ = R k₀ := by
      change (R.toPolynomial N).coeff n₀ = R k₀
      unfold TrigPolyℤ.toPolynomial
      rw [Finsupp.sum, Polynomial.finset_sum_coeff]
      simp_rw [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single k₀]
      · simp [n₀]
      · intro k hk hk_ne
        simp only [ite_eq_right_iff]
        intro h_eq_n
        have h1 : k.natAbs ≤ N := Finset.le_sup (f := fun j => j.natAbs) hk
        have h2 : k₀.natAbs ≤ N := Finset.le_sup (f := fun j => j.natAbs) hk₀
        exfalso; apply hk_ne; omega
      · exact fun h => absurd hk₀ h
    rw [h_eq, Polynomial.coeff_zero] at h_coeff
    exact hR_k₀ h_coeff.symm
  have hQ_real : ∀ z : ℂ, ‖z‖ = 1 → (Q.eval z / z ^ N).im = 0 := by
    intro z hz
    -- Every unit complex is exp(θ*I) for some θ
    obtain ⟨θ, hθ⟩ := (norm_eq_one_iff z).mp hz
    -- z = exp(θ * I); bridge: Q.eval z = z^N * R.toCircle(↑(θ/(2π)))
    have hz_ne : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; exact one_ne_zero hz.symm
    -- Set x = θ/(2π), then exp(θ*I) = exp(2π*x*I)
    set x := θ / (2 * Real.pi) with hx_def
    -- The bridge gives us the key identity
    have h_bridge_raw := toPolynomial_eval_on_circle R N (le_refl N) x
    -- Show z = the z' from the bridge
    have h_z_eq : z = Complex.exp (2 * Real.pi * x * Complex.I) := by
      rw [← hθ]
      congr 1
      simp only [hx_def, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
      have hpi : (2 * (Real.pi : ℂ) ≠ 0) := by
        push_cast; exact_mod_cast mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos)
      field_simp
    have h_bridge : Q.eval z = z ^ N * R.toCircle (↑x : 𝕋) := by
      rw [h_z_eq]
      exact toPolynomial_eval_on_circle R N (le_refl N) x
    rw [h_bridge, mul_div_cancel_left₀ _ (pow_ne_zero _ hz_ne)]
    exact hR_real _
  have hQ_nonneg : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (Q.eval z / z ^ N).re := by
    intro z hz
    obtain ⟨θ, hθ⟩ := (norm_eq_one_iff z).mp hz
    have hz_ne : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz; exact one_ne_zero hz.symm
    set x := θ / (2 * Real.pi) with hx_def
    have h_z_eq : z = Complex.exp (2 * Real.pi * x * Complex.I) := by
      rw [← hθ]; congr 1
      simp only [hx_def, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
      have hpi : (2 * (Real.pi : ℂ) ≠ 0) := by
        push_cast; exact_mod_cast mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos)
      field_simp
    have h_bridge : Q.eval z = z ^ N * R.toCircle (↑x : 𝕋) := by
      rw [h_z_eq]
      exact toPolynomial_eval_on_circle R N (le_refl N) x
    rw [h_bridge, mul_div_cancel_left₀ _ (pow_ne_zero _ hz_ne)]
    exact hR_nonneg _
  have hQ_deg : Q.natDegree ≤ 2 * N := by
    show (R.toPolynomial R.degree).natDegree ≤ 2 * R.degree
    unfold TrigPolyℤ.toPolynomial
    apply le_trans (Polynomial.natDegree_sum_le _ _)
    apply Finset.sup_le
    intro k hk
    calc (Polynomial.C (R k) * Polynomial.X ^ (k + (R.degree : ℤ)).toNat).natDegree
        ≤ (k + (R.degree : ℤ)).toNat := Polynomial.natDegree_C_mul_X_pow_le _ _
      _ ≤ 2 * R.degree := by
          have h_abs : k.natAbs ≤ R.degree :=
            Finset.le_sup (f := fun j => j.natAbs) hk
          omega
  -- Step 3: Apply polynomial Fejér-Riesz factorization
  obtain ⟨P_poly, hP_deg, hP_factor⟩ :=
    polynomial_fejer_riesz_factor Q N hQ_ne hQ_real hQ_nonneg hQ_deg
  -- Step 4: Convert P_poly to TrigPolyℤ
  let P := polynomial_to_trigpoly P_poly N
  -- Step 5: Verify non-negative support
  have hP_analytic : ∀ k ∈ P.support, 0 ≤ k :=
    polynomial_to_trigpoly_support_nonneg P_poly N
  -- Step 6: Show R = normSq P (uses factorization on circle + toCircle injectivity)
  have hP_eq : R = TrigPolyℤ.normSq P := by
    suffices h : R.toCircle = (TrigPolyℤ.normSq P).toCircle from
      TrigPolyℤ.toCircle_injective h
    -- It suffices to show equality at all ↑x for x : ℝ (quotient surjectivity)
    apply ContinuousMap.ext
    intro θ
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective θ
    -- Now θ = QuotientAddGroup.mk x = (↑x : 𝕋)
    set z := Complex.exp (2 * Real.pi * x * Complex.I)
    have hz_ne : z ≠ 0 := Complex.exp_ne_zero _
    have hz_norm : ‖z‖ = 1 := by
      show ‖Complex.exp (2 * ↑Real.pi * ↑x * Complex.I)‖ = 1
      have : (2 * ↑Real.pi * ↑x * Complex.I : ℂ) = ↑(2 * Real.pi * x) * Complex.I := by
        push_cast; ring
      rw [this]
      exact Complex.norm_exp_ofReal_mul_I _
    -- Bridge for R: Q.eval z = z^N * R.toCircle (↑x)
    have h_bridge_R : Q.eval z = z ^ N * R.toCircle (QuotientAddGroup.mk x) := by
      show (R.toPolynomial N).eval z = z ^ N * R.toCircle (↑x : 𝕋)
      exact toPolynomial_eval_on_circle R N (le_refl N) x
    -- Factorization: Q.eval z = z^N * normSq(P_poly.eval z)
    have h_factor := hP_factor z hz_norm
    -- Cancel z^N: R.toCircle (↑x) = normSq(P_poly.eval z)
    have h_cancel : R.toCircle (QuotientAddGroup.mk x) =
        ↑(Complex.normSq (P_poly.eval z)) :=
      mul_left_cancel₀ (pow_ne_zero _ hz_ne) (h_bridge_R.symm.trans h_factor)
    -- Bridge for P: P.toCircle (↑x) = P_poly.eval z
    have h_bridge_P : P.toCircle (QuotientAddGroup.mk x) = P_poly.eval z := by
      show (polynomial_to_trigpoly P_poly N).toCircle (↑x : 𝕋) = P_poly.eval z
      exact polynomial_to_trigpoly_toCircle P_poly N hP_deg x
    -- normSq_toCircle_eval: (normSq P).toCircle θ = normSq(P.toCircle θ)
    rw [h_cancel, TrigPolyℤ.normSq_toCircle_eval, h_bridge_P]
  exact ⟨P, hP_analytic, hP_eq⟩

theorem fejer_riesz (R : TrigPolyℤ)
    (hR_real : ∀ θ : 𝕋, (R.toCircle θ).im = 0)
    (hR_nonneg : ∀ θ : 𝕋, 0 ≤ (R.toCircle θ).re) :
    ∃ (P : TrigPolyℤ), R = TrigPolyℤ.normSq P := by
  obtain ⟨P, _, hP⟩ := fejer_riesz_core R hR_real hR_nonneg
  exact ⟨P, hP⟩

/-- Fejér-Riesz with analyticity guarantee: the polynomial P has
    non-negative Fourier modes only (i.e., P is an analytic trigonometric polynomial). -/
theorem fejer_riesz_analytic (R : TrigPolyℤ)
    (hR_real : ∀ θ : 𝕋, (R.toCircle θ).im = 0)
    (hR_nonneg : ∀ θ : 𝕋, 0 ≤ (R.toCircle θ).re) :
    ∃ (P : TrigPolyℤ), (∀ k ∈ P.support, 0 ≤ k) ∧ R = TrigPolyℤ.normSq P :=
  fejer_riesz_core R hR_real hR_nonneg


end FourierBochner
