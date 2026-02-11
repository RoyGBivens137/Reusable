/-
Copyright (c) 2025 Zachary Mullaghy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Mullaghy, Gianfranco Romaelle
-/
import FourierBochner.Character
import FourierBochner.FejerRiesz
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.flexible false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.style.show false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false

open FourierBochner Complex Real MeasureTheory Finset
open scoped FourierTransform ComplexConjugate

namespace FourierBochner

/-! ## Section 7a: Bochner's Theorem via Point Samples -/

/-- Weak finite Bochner (forward): weak PD on Z/NZ implies non-negative DFT coefficients. -/
lemma weak_bochner_dft_nonneg (N : ℕ) [NeZero N] (g : ZMod N → ℂ)
    (hg_pd : ∀ (c : ZMod N → ℂ),
      0 ≤ (∑ i : ZMod N, ∑ j : ZMod N, conj (c i) * c j * g (i - j)).re) :
    ∀ k₀ : ZMod N,
      0 ≤ (∑ m : ZMod N, g m * conj (FourierBochner.character N k₀ m)).re := by
  classical
  intro k₀
  letI : Fintype (ZMod N) := ZMod.fintype N
  have h_quad := hg_pd (fun i => FourierBochner.character N k₀ i)
  -- Expand quadratic form: Q = N · DFT(k₀)
  have h_step : ∑ i : ZMod N, ∑ j : ZMod N,
      conj (FourierBochner.character N k₀ i) * FourierBochner.character N k₀ j *
        g (i - j) =
    ↑N * ∑ m : ZMod N, g m * conj (FourierBochner.character N k₀ m) := by
    -- Factor: conj(χ(i)) · χ(j) · g(i-j) = g(i-j) · conj(χ(i-j))
    have h_char : ∀ i j : ZMod N,
        conj (FourierBochner.character N k₀ i) * FourierBochner.character N k₀ j *
          g (i - j) =
        g (i - j) * conj (FourierBochner.character N k₀ (i - j)) := by
      intro i j
      rw [FourierBochner.character_sub_eq_mul, map_mul, Complex.conj_conj]; ring
    simp_rw [h_char]
    -- Reindex j ↦ i-j via Equiv.subLeft
    have h_reindex : ∀ i : ZMod N,
        ∑ j : ZMod N, g (i - j) * conj (FourierBochner.character N k₀ (i - j)) =
        ∑ m : ZMod N, g m * conj (FourierBochner.character N k₀ m) := by
      intro i
      exact Fintype.sum_equiv (Equiv.subLeft i) _ _
        (fun j => by simp [Equiv.subLeft_apply])
    simp_rw [h_reindex]
    -- Sum of constant = N · constant
    rw [Finset.sum_const, Finset.card_univ, ZMod.card N, nsmul_eq_mul]
  -- Extract real part: (↑N · z).re = ↑N · z.re since N is real
  have h_re : (∑ i : ZMod N, ∑ j : ZMod N,
      conj (FourierBochner.character N k₀ i) * FourierBochner.character N k₀ j *
        g (i - j)).re =
    ↑N * (∑ m : ZMod N, g m * conj (FourierBochner.character N k₀ m)).re := by
    rw [h_step, Complex.mul_re]
    simp [Complex.natCast_re, Complex.natCast_im]
  rw [h_re] at h_quad
  -- 0 ≤ N · x and N > 0 implies x ≥ 0
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  by_contra h_neg
  push_neg at h_neg
  linarith [mul_neg_of_pos_of_neg hN_pos h_neg]

/-- PD on ℝ extends to weak PD over any finite set of sample points.
    This lifts the Fin-indexed PD condition to ZMod-indexed sums. -/
private lemma pd_sum_nonneg_zmod {f : ℝ → ℂ} (hf : FourierBochner.IsPositiveDefinite f)
    (N : ℕ) [NeZero N] (x : ZMod N → ℝ) (c : ZMod N → ℂ) :
    0 ≤ (∑ i : ZMod N, ∑ j : ZMod N, conj (c i) * c j * f (x i - x j)).re := by
  classical
  letI : Fintype (ZMod N) := ZMod.fintype N
  let e := Fintype.equivFin (ZMod N)  -- ZMod N ≃ Fin (card (ZMod N))
  have h := hf.2 (Fintype.card (ZMod N)) (x ∘ e.symm) (c ∘ e.symm)
  simp only [Function.comp] at h
  -- Reindex both sums from ZMod N to Fin (card (ZMod N)) using e.symm
  suffices heq : (∑ i : ZMod N, ∑ j : ZMod N, conj (c i) * c j * f (x i - x j)) =
      ∑ i : Fin (Fintype.card (ZMod N)), ∑ j : Fin (Fintype.card (ZMod N)),
        conj (c (e.symm i)) * c (e.symm j) * f (x (e.symm i) - x (e.symm j)) by
    rwa [heq]
  rw [(e.symm.sum_comp
    (fun i => ∑ j : ZMod N, conj (c i) * c j * f (x i - x j))).symm]
  congr 1; ext k
  exact (e.symm.sum_comp
    (fun j => conj (c (e.symm k)) * c j * f (x (e.symm k) - x j))).symm

/-- Sampling a 2π-periodic PD function at equispaced points gives weak PD on Z/NZ.
    Key: g(i-j) in ZMod N equals f(x_i - x_j) in ℝ by periodicity. -/
lemma point_sample_weak_pd (f : ℝ → ℂ) (hf_pd : FourierBochner.IsPositiveDefinite f)
    (hf_per : ∀ θ, f (θ + 2 * Real.pi) = f θ) (N : ℕ) [NeZero N] :
    ∀ (c : ZMod N → ℂ),
      0 ≤ (∑ i : ZMod N, ∑ j : ZMod N, conj (c i) * c j *
        f (2 * Real.pi * ↑(i - j).val / ↑N)).re := by
  intro c
  -- f(2π(i-j).val/N) = f(x_i - x_j) via ZMod periodicity arithmetic
  -- This uses periodicity: (i-j).val differs from i.val - j.val by a multiple of N
  -- and f has period 2π, so f(2π·((i-j).val)/N) = f(2π·(i.val-j.val)/N)
  suffices h_eq : ∀ i j : ZMod N,
      f (2 * Real.pi * ↑(i - j).val / ↑N) =
        f (2 * Real.pi * ↑i.val / ↑N - 2 * Real.pi * ↑j.val / ↑N) by
    simp_rw [h_eq]
    -- Now the sum is Σ_i Σ_j conj(c_i) c_j f(x_i - x_j) with x_k = 2πk.val/N
    have h_sub : ∀ i j : ZMod N,
        2 * Real.pi * ↑i.val / ↑N - 2 * Real.pi * ↑j.val / ↑N =
        (fun m : ZMod N => 2 * Real.pi * ↑m.val / ↑N) i -
        (fun m : ZMod N => 2 * Real.pi * ↑m.val / ↑N) j := by
      intro i j; ring
    simp_rw [h_sub]
    exact pd_sum_nonneg_zmod hf_pd N _ c
  -- Prove f(2π(i-j).val/N) = f(x_i - x_j) using periodicity
  intro i j
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  -- (i-j).val ≡ i.val - j.val (mod N)
  -- From ZMod: (↑(i-j).val : ZMod N) = i - j = (↑i.val : ZMod N) - (↑j.val : ZMod N)
  have h_cong : ((i - j).val : ℤ) ≡ (↑i.val - ↑j.val : ℤ) [ZMOD (N : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    simp [ZMod.natCast_zmod_val]
  -- Extract divisibility
  rw [Int.modEq_iff_dvd] at h_cong
  obtain ⟨k, hk⟩ := h_cong  -- (i.val - j.val) - (i-j).val = k * N
  -- Convert to real arithmetic
  -- 2π(i-j).val/N = (2πi.val/N - 2πj.val/N) + (-k) * (2π)
  have h_shift : 2 * Real.pi * ↑(i - j).val / ↑N =
      (2 * Real.pi * ↑i.val / ↑N - 2 * Real.pi * ↑j.val / ↑N) + ↑(-k) * (2 * Real.pi) := by
    field_simp
    have := congr_arg (fun x : ℤ => (x : ℝ)) hk
    push_cast at this ⊢
    linarith
  -- Apply 2π-periodicity
  rw [h_shift]
  exact (Function.Periodic.int_mul hf_per (-k))
    (2 * Real.pi * ↑i.val / ↑N - 2 * Real.pi * ↑j.val / ↑N)

/-- Composition of point_sample_weak_pd and weak_bochner_dft_nonneg:
    sampling a PD periodic function at N equispaced points gives non-negative DFT. -/
private lemma dft_nonneg_of_pd (f : ℝ → ℂ)
    (hf_pd : FourierBochner.IsPositiveDefinite f)
    (hf_per : ∀ θ, f (θ + 2 * Real.pi) = f θ)
    (N : ℕ) [NeZero N] (k₀ : ZMod N) :
    0 ≤ (∑ j : ZMod N, f (2 * Real.pi * ↑j.val / ↑N) *
      conj (FourierBochner.character N k₀ j)).re := by
  apply weak_bochner_dft_nonneg N (fun k => f (2 * Real.pi * ↑k.val / ↑N)) _ k₀
  exact point_sample_weak_pd f hf_pd hf_per N

/-- DFT sum identity: ∑_{k₀} DFT(k₀) = N · f(0).
    Follows from character orthogonality: ∑_k χ(k,j) = N·δ_{j,0}. -/
private lemma dft_sum_eq_card_smul (f : ℝ → ℂ) (N : ℕ) [hN : NeZero N] :
    ∑ k₀ : ZMod N, ∑ j : ZMod N,
      f (2 * Real.pi * ↑j.val / ↑N) *
      conj (FourierBochner.character N k₀ j) =
    ↑N * f 0 := by
  conv_lhs => rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  -- Goal: ∑ j, f(2πj/N) * ∑ k₀, conj(χ(k₀,j)) = N * f(0)
  have h_char_at_zero : ∀ k : ZMod N, FourierBochner.character N k 0 = 1 := by
    intro k; unfold FourierBochner.character; simp [ZMod.val_zero]
  have h_conj_sum : ∀ j : ZMod N,
      ∑ k₀ : ZMod N, conj (FourierBochner.character N k₀ j) =
      if j = 0 then (↑N : ℂ) else 0 := by
    intro j
    have h_eq_conj : ∑ k₀ : ZMod N, conj (FourierBochner.character N k₀ j) =
        conj (∑ k₀ : ZMod N, FourierBochner.character N k₀ j) :=
      (map_sum (starRingEnd ℂ) _ _).symm
    rw [h_eq_conj]
    have h := FourierBochner.character_orthogonality_dual_general N j 0
    simp only [h_char_at_zero, map_one, mul_one] at h
    rw [h]; split_ifs <;> simp [map_natCast]
  -- Only j = 0 contributes
  rw [Finset.sum_eq_single_of_mem (0 : ZMod N) (Finset.mem_univ _)
    (fun j _ hj => by rw [h_conj_sum, if_neg hj, mul_zero])]
  rw [h_conj_sum, if_pos rfl]
  simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div]
  ring

/-- Full sum of scaled DFT coefficients equals f(0). -/
private lemma scaled_dft_sum_eq (f : ℝ → ℂ) (N : ℕ) [hN : NeZero N] :
    ∑ k₀ : ZMod N, (1 / (↑N : ℂ)) *
      ∑ j : ZMod N, f (2 * Real.pi * ↑j.val / ↑N) *
        conj (FourierBochner.character N k₀ j) = f 0 := by
  rw [← Finset.mul_sum, dft_sum_eq_card_smul]
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp

/-- Real part version: full sum of scaled DFT .re coefficients equals (f 0).re. -/
private lemma scaled_dft_sum_re_eq (f : ℝ → ℂ) (N : ℕ) [hN : NeZero N] :
    ∑ k₀ : ZMod N, ((1 / (↑N : ℂ)) *
      ∑ j : ZMod N, f (2 * Real.pi * ↑j.val / ↑N) *
        conj (FourierBochner.character N k₀ j)).re = (f 0).re := by
  have h := congr_arg Complex.re (scaled_dft_sum_eq f N)
  simp only [← Complex.reCLM_apply] at h ⊢
  rw [map_sum] at h
  simp only [Complex.reCLM_apply] at h ⊢
  exact h

/-- Riemann sums of DFT coefficients converge to the Fourier coefficient.
    This factors out the convergence argument from fourier_coeff_nonneg_of_pd. -/
private lemma fourier_riemann_tendsto (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_per : ∀ θ, f (θ + 2 * Real.pi) = f θ) (m : ℤ) :
    Filter.Tendsto
      (fun n => ((1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n), f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j)).re)
      Filter.atTop
      (nhds ((1 / (2 * Real.pi)) *
        ∫ θ in Set.Ico (0 : ℝ) (2 * Real.pi),
          f θ * Complex.exp (-Complex.I * ↑m * ↑θ)).re) := by
  -- Construct g : C(𝕋, ℂ) for Riemann sum convergence
  let f_scaled : ℝ → ℂ := fun t => f (2 * Real.pi * t)
  have f_scaled_per : Function.Periodic f_scaled 1 := by
    intro t; simp only [f_scaled, mul_add, mul_one]; exact hf_per _
  have f_scaled_cont : Continuous f_scaled :=
    hf_cont.comp (continuous_const.mul continuous_id)
  let f_lift : 𝕋 → ℂ := f_scaled_per.lift
  have f_lift_cont : Continuous f_lift := continuous_coinduced_dom.mpr f_scaled_cont
  let g : C(𝕋, ℂ) :=
    ⟨fun t => f_lift t * conj (fourier m t),
     f_lift_cont.mul (continuous_star.comp (fourier m).continuous)⟩
  -- Riemann sums of g equal DFT sums
  have h_sum_eq : ∀ n : ℕ,
      (1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n), g ((j.val : ℝ) / (2 ^ n : ℝ) : 𝕋) =
      (1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n),
          (f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j)) := by
    intro n; congr 1
    apply Finset.sum_congr rfl; intro j _
    show f_lift ((j.val : ℝ) / (2 ^ n : ℝ) : 𝕋) *
      conj (fourier m ((j.val : ℝ) / (2 ^ n : ℝ) : 𝕋)) = _
    have h1 : f_lift ((j.val : ℝ) / (2 ^ n : ℝ) : 𝕋) =
        f (2 * Real.pi * ((j.val : ℝ) / (2 ^ n : ℝ))) :=
      f_scaled_per.lift_coe _
    have h2 : fourier m ((j.val : ℝ) / (2 ^ n : ℝ) : 𝕋) =
        FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j := by
      convert FourierBochner.fourier_eval_rational_eq_character (2 ^ n) m j using 2
      simp [Nat.cast_pow]
    rw [h1, h2]; congr 1; congr 1
    exact (mul_div_assoc _ _ _).symm
  -- Apply riemann_sum_converges_to_integral
  haveI hp : Fact (Nat.Prime 2) := Fact.mk (by decide)
  have h_rsc := FourierBochner.riemann_sum_converges_to_integral g 2
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h_rsc
  have h_conv_ℂ : Filter.Tendsto
      (fun n => (1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n), f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j))
      Filter.atTop (nhds (∫ x : 𝕋, g x)) :=
    h_rsc.congr (fun n => h_sum_eq n)
  -- Take .re for real convergence
  have h_conv_re : Filter.Tendsto
      (fun n => ((1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n), f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j)).re)
      Filter.atTop (nhds (∫ x : 𝕋, g x).re) :=
    (Complex.continuous_re.tendsto _).comp h_conv_ℂ
  -- Bridge ∫_𝕋 g to the Fourier coefficient integral
  suffices h_bridge : (∫ x : 𝕋, g x).re = ((1 / (2 * Real.pi)) *
      ∫ θ in Set.Ico (0 : ℝ) (2 * Real.pi),
        f θ * Complex.exp (-Complex.I * ↑m * ↑θ)).re by
    rw [← h_bridge]; exact h_conv_re
  suffices h_c : ∫ x : 𝕋, (g : 𝕋 → ℂ) x =
      (1 / (2 * ↑Real.pi)) * ∫ θ in Set.Ico (0 : ℝ) (2 * Real.pi),
        f θ * Complex.exp (-Complex.I * ↑m * ↑θ) from congr_arg Complex.re h_c
  set H : ℝ → ℂ := fun θ => f θ * Complex.exp (-Complex.I * ↑m * (↑θ : ℂ)) with hH_def
  have hA : ∫ x : 𝕋, (g : 𝕋 → ℂ) x = ∫ t in (0:ℝ)..(1:ℝ), (g : 𝕋 → ℂ) t := by
    have h := AddCircle.intervalIntegral_preimage 1 0 (g : 𝕋 → ℂ)
    simp only [zero_add] at h; exact h.symm
  have hB : ∀ t : ℝ, (g : 𝕋 → ℂ) (↑t : 𝕋) = H ((2 * Real.pi) * t) := by
    intro t
    show f_lift (↑t : 𝕋) * starRingEnd ℂ (fourier m (↑t : 𝕋)) = _
    have h_fl : f_lift (↑t : 𝕋) = f (2 * Real.pi * t) := f_scaled_per.lift_coe t
    rw [h_fl]
    show f (2 * Real.pi * t) * starRingEnd ℂ (fourier m (↑t : 𝕋)) = H ((2 * Real.pi) * t)
    simp only [H, hH_def]
    congr 1
    rw [show starRingEnd ℂ (fourier m (↑t : 𝕋)) = fourier (-m) (↑t : 𝕋) from fourier_neg.symm]
    rw [fourier_coe_apply]
    simp only [div_one, Int.cast_neg, neg_mul]
    congr 1; push_cast; ring
  have hC : ∫ t in (0:ℝ)..(1:ℝ), H ((2 * Real.pi) * t) =
      (2 * Real.pi)⁻¹ • ∫ θ in (0:ℝ)..(2 * Real.pi), H θ := by
    have := intervalIntegral.integral_comp_mul_left H (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (a := (0:ℝ)) (b := (1:ℝ))
    simp only [mul_zero, mul_one] at this; exact this
  have hD : ∫ θ in (0:ℝ)..(2 * Real.pi), H θ =
      ∫ θ in Set.Ico (0 : ℝ) (2 * Real.pi), H θ := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    exact MeasureTheory.setIntegral_congr_set Ico_ae_eq_Ioc.symm
  rw [hA, intervalIntegral.integral_congr (fun t _ => hB t), hC, hD,
      RCLike.real_smul_eq_coe_mul]
  congr 1
  push_cast
  exact (one_div _).symm

/-- Non-negative Fourier coefficients of a continuous 2π-periodic PD function. -/
theorem fourier_coeff_nonneg_of_pd (f : ℝ → ℂ) (hf_cont : Continuous f)
    (hf_pd : FourierBochner.IsPositiveDefinite f)
    (hf_per : ∀ θ, f (θ + 2 * Real.pi) = f θ) (m : ℤ) :
    0 ≤ ((1 / (2 * Real.pi)) *
      ∫ θ in Set.Ico (0 : ℝ) (2 * Real.pi),
        f θ * Complex.exp (-Complex.I * ↑m * ↑θ)).re := by
  -- For each N, DFT of point samples has non-negative real part
  have h_dft_nn : ∀ (N : ℕ) [NeZero N],
      0 ≤ (∑ j : ZMod N, f (2 * Real.pi * ↑j.val / ↑N) *
        conj (FourierBochner.character N ((m : ℤ) : ZMod N) j)).re :=
    fun N _ => dft_nonneg_of_pd f hf_pd hf_per N ((m : ℤ) : ZMod N)
  -- Construct g : C(𝕋, ℂ) for Riemann sum convergence
  let f_scaled : ℝ → ℂ := fun t => f (2 * Real.pi * t)
  have f_scaled_per : Function.Periodic f_scaled 1 := by
    intro t; simp only [f_scaled, mul_add, mul_one]; exact hf_per _
  have f_scaled_cont : Continuous f_scaled :=
    hf_cont.comp (continuous_const.mul continuous_id)
  let f_lift : 𝕋 → ℂ := f_scaled_per.lift
  have f_lift_cont : Continuous f_lift := continuous_coinduced_dom.mpr f_scaled_cont
  let g : C(𝕋, ℂ) :=
    ⟨fun t => f_lift t * conj (fourier m t),
     f_lift_cont.mul (continuous_star.comp (fourier m).continuous)⟩
  -- Riemann sums of g equal DFT sums pointwise
  have h_sum_eq : ∀ n : ℕ,
      (1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n), g ((j.val : ℝ) / (2 ^ n : ℝ) : 𝕋) =
      (1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n),
          (f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j)) := by
    intro n; congr 1
    apply Finset.sum_congr rfl; intro j _
    show f_lift ((j.val : ℝ) / (2 ^ n : ℝ) : 𝕋) *
      conj (fourier m ((j.val : ℝ) / (2 ^ n : ℝ) : 𝕋)) = _
    have h1 : f_lift ((j.val : ℝ) / (2 ^ n : ℝ) : 𝕋) =
        f (2 * Real.pi * ((j.val : ℝ) / (2 ^ n : ℝ))) :=
      f_scaled_per.lift_coe _
    have h2 : fourier m ((j.val : ℝ) / (2 ^ n : ℝ) : 𝕋) =
        FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j := by
      convert FourierBochner.fourier_eval_rational_eq_character (2 ^ n) m j using 2
      simp [Nat.cast_pow]
    rw [h1, h2]; congr 1; congr 1
    exact (mul_div_assoc _ _ _).symm
  -- Complex convergence via riemann_sum_converges_to_integral
  haveI hp : Fact (Nat.Prime 2) := Fact.mk (by decide)
  have h_rsc := FourierBochner.riemann_sum_converges_to_integral g 2
  -- h_rsc uses ↑(2^n) (Nat.cast of 2^n); normalize to (2 : ℂ/ℝ)^n to match h_sum_eq
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h_rsc
  have h_conv_ℂ : Filter.Tendsto
      (fun n => (1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n), f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j))
      Filter.atTop (nhds (∫ x : 𝕋, g x)) :=
    h_rsc.congr (fun n => h_sum_eq n)
  -- Real part converges
  have h_conv_re : Filter.Tendsto
      (fun n => ((1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n), f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j)).re)
      Filter.atTop (nhds (∫ x : 𝕋, g x).re) :=
    (Complex.continuous_re.tendsto _).comp h_conv_ℂ
  -- Each term has non-negative real part
  -- ((1/2^n : ℂ) * z).re ≥ 0 since (1/2^n : ℂ) is a non-negative real and z.re ≥ 0
  have h_terms_nn : ∀ n : ℕ,
      0 ≤ ((1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n), f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j)).re := by
    intro n
    have h_re : ((1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n), f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j)).re =
        (1 / (2 ^ n : ℝ)) *
        (∑ j : ZMod (2 ^ n), f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((m : ℤ) : ZMod (2 ^ n)) j)).re := by
      rw [show (1 / (2 ^ n : ℂ)) = ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) from by push_cast; ring]
      exact Complex.re_ofReal_mul _ _
    rw [h_re]
    apply mul_nonneg
    · positivity
    · convert h_dft_nn (2 ^ n) using 2; push_cast; ring
  -- Limit of non-negatives is non-negative
  have h_nn : 0 ≤ (∫ x : 𝕋, g x).re :=
    ge_of_tendsto h_conv_re (Filter.Eventually.of_forall h_terms_nn)
  -- Bridge ∫_𝕋 g to the Fourier coefficient integral
  -- ∫_𝕋 g = ∫₀¹ f(2πt) conj(fourier m t) dt = (1/2π) ∫₀²π f(θ) exp(-imθ) dθ
  -- Uses AddCircle.intervalIntegral_preimage and change of variables θ = 2πt
  suffices h_bridge : (∫ x : 𝕋, g x).re =
      ((1 / (2 * Real.pi)) *
        ∫ θ in Set.Ico (0 : ℝ) (2 * Real.pi),
          f θ * Complex.exp (-Complex.I * ↑m * ↑θ)).re by
    rw [← h_bridge]; exact h_nn
  -- Prove complex equality, then take .re
  suffices h_c : ∫ x : 𝕋, (g : 𝕋 → ℂ) x =
      (1 / (2 * ↑Real.pi)) * ∫ θ in Set.Ico (0 : ℝ) (2 * Real.pi),
        f θ * Complex.exp (-Complex.I * ↑m * ↑θ) from congr_arg Complex.re h_c
  -- Define the target integrand for change of variables
  set H : ℝ → ℂ := fun θ => f θ * Complex.exp (-Complex.I * ↑m * (↑θ : ℂ)) with hH_def
  -- A: ∫_𝕋 g = ∫₀¹ g(↑t)
  have hA : ∫ x : 𝕋, (g : 𝕋 → ℂ) x = ∫ t in (0:ℝ)..(1:ℝ), (g : 𝕋 → ℂ) t := by
    have h := AddCircle.intervalIntegral_preimage 1 0 (g : 𝕋 → ℂ)
    simp only [zero_add] at h; exact h.symm
  -- B: g(↑t) = H(2πt) pointwise
  have hB : ∀ t : ℝ, (g : 𝕋 → ℂ) (↑t : 𝕋) = H ((2 * Real.pi) * t) := by
    intro t
    show f_lift (↑t : 𝕋) * starRingEnd ℂ (fourier m (↑t : 𝕋)) = _
    have h_fl : f_lift (↑t : 𝕋) = f (2 * Real.pi * t) := f_scaled_per.lift_coe t
    rw [h_fl]
    show f (2 * Real.pi * t) * starRingEnd ℂ (fourier m (↑t : 𝕋)) = H ((2 * Real.pi) * t)
    simp only [H, hH_def]
    congr 1
    rw [show starRingEnd ℂ (fourier m (↑t : 𝕋)) = fourier (-m) (↑t : 𝕋) from fourier_neg.symm]
    rw [fourier_coe_apply]
    simp only [div_one, Int.cast_neg, neg_mul]
    congr 1; push_cast; ring
  -- C: ∫₀¹ H(2πt) dt = (2π)⁻¹ · ∫₀²π H(θ) dθ via change of variables
  have hC : ∫ t in (0:ℝ)..(1:ℝ), H ((2 * Real.pi) * t) =
      (2 * Real.pi)⁻¹ • ∫ θ in (0:ℝ)..(2 * Real.pi), H θ := by
    have := intervalIntegral.integral_comp_mul_left H (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (a := (0:ℝ)) (b := (1:ℝ))
    simp only [mul_zero, mul_one] at this; exact this
  -- D: ∫₀²π H = ∫_{Ico(0,2π)} H (interval → set integral)
  have hD : ∫ θ in (0:ℝ)..(2 * Real.pi), H θ =
      ∫ θ in Set.Ico (0 : ℝ) (2 * Real.pi), H θ := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    exact MeasureTheory.setIntegral_congr_set Ico_ae_eq_Ioc.symm
  -- Combine
  rw [hA, intervalIntegral.integral_congr (fun t _ => hB t), hC, hD,
      RCLike.real_smul_eq_coe_mul]
  congr 1
  push_cast
  exact (one_div _).symm

/-- Main result: Constructive Bochner via sheaf of local means -/
theorem constructive_bochner_via_sheaf (f : ℝ → ℂ) (hf : Continuous f)
    (hf_pd : FourierBochner.IsPositiveDefinite f)
    (hf_per : ∀ θ, f (θ + 2 * Real.pi) = f θ) :
    ∃ (μ : ℤ → ℝ),
      (∀ k, 0 ≤ μ k) ∧
      (Summable μ) ∧
      ∀ θ, f θ = ∑' k : ℤ, ↑(μ k) * Complex.exp (Complex.I * ↑k * ↑θ) := by
  let μ : ℤ → ℝ := fun k => ((1 / (2 * Real.pi)) *
    ∫ θ in Set.Ico (0 : ℝ) (2 * Real.pi),
      f θ * Complex.exp (-Complex.I * ↑k * ↑θ)).re
  have h_nn : ∀ k, 0 ≤ μ k := fun k => fourier_coeff_nonneg_of_pd f hf hf_pd hf_per k
  have h_summ : Summable μ := by
    apply summable_of_sum_le h_nn
    intro u
    haveI hp2 : Fact (Nat.Prime 2) := Fact.mk (by decide)
    -- Convergence of Riemann sums for each k
    have h_tends : ∀ k ∈ u, Filter.Tendsto
        (fun n => ((1 / (2 ^ n : ℂ)) *
          ∑ j : ZMod (2 ^ n), f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
            conj (FourierBochner.character (2 ^ n) ((k : ℤ) : ZMod (2 ^ n)) j)).re)
        Filter.atTop (nhds (μ k)) :=
      fun k _ => fourier_riemann_tendsto f hf hf_per k
    -- Define the Riemann sum for a single coefficient
    let r : ℕ → ℤ → ℝ := fun n k =>
      ((1 / (2 ^ n : ℂ)) *
        ∑ j : ZMod (2 ^ n), f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) ((k : ℤ) : ZMod (2 ^ n)) j)).re
    -- Finite sum converges
    have h_sum_tends : Filter.Tendsto
        (fun n => u.sum (fun k => r n k))
        Filter.atTop (nhds (u.sum (fun k => μ k))) :=
      tendsto_finset_sum u h_tends
    -- DFT partial sum bound (eventually, for n large enough for injectivity)
    have h_bound : ∀ᶠ n in Filter.atTop, u.sum (fun k => r n k) ≤ (f 0).re := by
      -- For n large enough, the map k ↦ (k : ZMod 2^n) is injective on u
      -- Then the partial sum ≤ full sum = (f 0).re
      rw [Filter.eventually_atTop]
      -- Bound on element sizes: all |k| < M for k ∈ u
      let M : ℕ := u.sup (fun k : ℤ => k.natAbs) + 1
      refine ⟨2 * M, fun n hn => ?_⟩
      -- Define g' : ZMod(2^n) → ℝ, the scaled DFT .re coefficient
      let g' : ZMod (2 ^ n) → ℝ := fun k₀ =>
        ((1 / (2 ^ n : ℂ)) * ∑ j : ZMod (2 ^ n),
          f (2 * Real.pi * ↑j.val / ↑(2 ^ n)) *
          conj (FourierBochner.character (2 ^ n) k₀ j)).re
      -- r n k = g' ((k : ℤ) : ZMod(2^n)) by definition
      have h_rg : ∀ k : ℤ, r n k = g' ((k : ℤ) : ZMod (2 ^ n)) := fun _ => rfl
      simp_rw [h_rg]
      -- Non-negativity of each g' coefficient
      have h_nn : ∀ k₀ : ZMod (2 ^ n), 0 ≤ g' k₀ := by
        intro k₀; show 0 ≤ ((1 / (2 ^ n : ℂ)) * _).re
        rw [show (1 / (2 ^ n : ℂ)) = ((1 / (2 ^ n : ℝ) : ℝ) : ℂ) from by push_cast; ring]
        rw [Complex.re_ofReal_mul]
        apply mul_nonneg (by positivity)
        have := dft_nonneg_of_pd f hf_pd hf_per (2 ^ n) k₀
        simp only [Nat.cast_pow, Nat.cast_ofNat] at this
        exact this
      -- Injectivity of ℤ → ZMod(2^n) on u for n ≥ 2M
      have h_inj : ∀ k₁ ∈ u, ∀ k₂ ∈ u,
          (fun k : ℤ => (k : ZMod (2 ^ n))) k₁ =
          (fun k : ℤ => (k : ZMod (2 ^ n))) k₂ → k₁ = k₂ := by
        intro k₁ hk₁ k₂ hk₂ h_eq
        simp only at h_eq
        rw [ZMod.intCast_eq_intCast_iff] at h_eq
        rw [Int.modEq_iff_dvd] at h_eq
        -- h_eq : (↑(2^n) : ℤ) ∣ k₂ - k₁
        -- Bound: |k₁|, |k₂| ≤ M - 1, so |k₂ - k₁| ≤ 2(M-1) < 2M ≤ n ≤ 2^n
        have hk₁_bound : k₁.natAbs ≤ M - 1 := by
          exact Nat.le_sub_one_of_lt (Nat.lt_succ_of_le (Finset.le_sup (f := fun k : ℤ => k.natAbs) hk₁))
        have hk₂_bound : k₂.natAbs ≤ M - 1 := by
          exact Nat.le_sub_one_of_lt (Nat.lt_succ_of_le (Finset.le_sup (f := fun k : ℤ => k.natAbs) hk₂))
        -- |k₂ - k₁| < 2^n so the divisibility forces k₂ = k₁
        have h_abs_bound : (k₂ - k₁).natAbs < 2 ^ n := by
          calc (k₂ - k₁).natAbs ≤ k₂.natAbs + k₁.natAbs := Int.natAbs_sub_le k₂ k₁
            _ ≤ (M - 1) + (M - 1) := Nat.add_le_add hk₂_bound hk₁_bound
            _ = 2 * (M - 1) := by ring
            _ < 2 * M := by omega
            _ ≤ n := hn
            _ < 2 ^ n := Nat.lt_two_pow_self
        -- From divisibility and small absolute value, conclude k₂ = k₁
        have h_dvd_nat : (2 ^ n) ∣ (k₂ - k₁).natAbs := by
          have := Int.natAbs_dvd_natAbs.mpr h_eq
          rwa [Int.natAbs_natCast] at this
        have h_zero : (k₂ - k₁).natAbs = 0 :=
          Nat.eq_zero_of_dvd_of_lt h_dvd_nat h_abs_bound
        exact eq_of_sub_eq_zero (Int.natAbs_eq_zero.mp h_zero) |>.symm
      -- Full sum = (f 0).re via scaled_dft_sum_re_eq
      have h_full : Finset.univ.sum g' = (f 0).re := by
        have := scaled_dft_sum_re_eq f (2 ^ n)
        simp only [Nat.cast_pow, Nat.cast_ofNat] at this
        exact this
      -- Chain: partial sum ≤ full sum = (f 0).re
      calc u.sum (fun k => g' ((k : ℤ) : ZMod (2 ^ n)))
          = (u.image (fun k : ℤ => (k : ZMod (2 ^ n)))).sum g' :=
            (Finset.sum_image h_inj).symm
        _ ≤ Finset.univ.sum g' := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro i _ _; exact h_nn i
        _ = (f 0).re := h_full
    exact le_of_tendsto h_sum_tends h_bound
  -- (3) Pointwise Fourier inversion for absolutely convergent series
  -- then apply Mathlib's has_pointwise_sum_fourier_series_of_summable.
  have h_inv : ∀ θ, f θ = ∑' k : ℤ, ↑(μ k) * Complex.exp (Complex.I * ↑k * ↑θ) := by
    haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    -- Convert hf_per to Function.Periodic for dot notation
    have hf_per' : Function.Periodic f (2 * Real.pi) := hf_per
    -- Lift f to C(AddCircle(2π), ℂ) via Periodic.lift
    let F : C(AddCircle (2 * Real.pi), ℂ) :=
      ⟨hf_per'.lift, continuous_coinduced_dom.mpr (by convert hf using 1)⟩
    -- F(↑θ) = f(θ) for all θ
    have hF_eval : ∀ x : ℝ, (F : AddCircle (2 * Real.pi) → ℂ) (↑x) = f x :=
      fun x => hf_per'.lift_coe x
    -- Key bridge: fourierCoeff F n = ↑(μ n)
    -- Requires: (1) integral bridge, (2) Fourier coefficient reality.
    -- Uses Hermitian condition f(-x) = conj(f(x)) to prove Fourier coefficients are real.
    have h_coeff : ∀ n : ℤ, _root_.fourierCoeff (⇑F : AddCircle (2 * Real.pi) → ℂ) n = ↑(μ n) := by
      intro n
      -- Define the complex Fourier coefficient (same as μ n but without .re)
      set c : ℂ := (1 / (2 * ↑Real.pi)) *
        ∫ θ in Set.Ico (0 : ℝ) (2 * Real.pi),
          f θ * Complex.exp (-Complex.I * ↑n * ↑θ) with hc_def
      -- μ n = c.re by definition
      change _root_.fourierCoeff (⇑F) n = ↑c.re
      -- fourierCoeff F n = c (integral bridge)
      have h_fc : _root_.fourierCoeff (⇑F) n = c := by
        rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
        -- Convert ℝ • ℂ to ↑ℝ * ℂ, and inner ℂ • ℂ to ℂ * ℂ
        rw [RCLike.real_smul_eq_coe_mul]
        simp_rw [smul_eq_mul]
        -- Simplify integrand: fourier(-n)(↑x) * F(↑x) = f(x) * exp(-I*n*x)
        have h_eq : Set.EqOn
            (fun (x : ℝ) => @fourier (2 * Real.pi) (-n) (↑x : AddCircle _) *
              (F : _ → ℂ) (↑x : AddCircle _))
            (fun (x : ℝ) => f x * Complex.exp (-Complex.I * ↑n * ↑x))
            (Set.uIcc (0 : ℝ) (2 * Real.pi)) := by
          intro x _; dsimp only
          rw [hF_eval, mul_comm]
          congr 1; rw [fourier_coe_apply]; congr 1
          have h2pi_ne : (↑(2 * Real.pi) : ℂ) ≠ 0 :=
            Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
          field_simp; push_cast; ring
        rw [intervalIntegral.integral_congr h_eq]
        -- Convert interval integral → Ico set integral
        rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
        rw [MeasureTheory.setIntegral_congr_set Ico_ae_eq_Ioc.symm]
        -- Normalize coefficient: ↑(1/(2π)) = 1/(2*↑π) as ℂ
        simp only [hc_def]; congr 1 <;> push_cast <;> rfl
      -- c is real by Hermitian symmetry
      have h_im : c.im = 0 := by
        -- Suffices to show conj(c) = c
        suffices h_conj : starRingEnd ℂ c = c by
          have := congr_arg Complex.im h_conj
          rw [Complex.conj_im] at this; linarith
        rw [hc_def, map_mul]
        -- conj(1/(2π)) = 1/(2π) since it's real
        rw [show starRingEnd ℂ ((1 : ℂ) / (2 * ↑Real.pi)) = 1 / (2 * ↑Real.pi) from by
          simp [map_div₀, map_ofNat, Complex.conj_ofReal]]
        congr 1
        -- conj(∫ₛ f*exp(-inx)) = ∫ₛ conj(f*exp(-inx))
        rw [← integral_conj]
        -- Simplify: conj(f(x)*exp(-inx)) = f(-x)*exp(inx) via Hermitian condition
        have h_conj_pt : ∀ x : ℝ,
            starRingEnd ℂ (f x * Complex.exp (-Complex.I * ↑n * ↑x)) =
            f (-x) * Complex.exp (Complex.I * ↑n * (↑x : ℂ)) := by
          intro x; rw [map_mul]
          rw [show starRingEnd ℂ (f x) = f (-x) from (hf_pd.1 x).symm]
          congr 1; rw [← Complex.exp_conj]; congr 1
          simp only [map_mul, map_neg, Complex.conj_I,
            Complex.conj_ofReal, map_intCast, neg_neg]
        simp_rw [h_conj_pt]
        -- ∫ₛ f(-x)*exp(inx) = ∫ₛ f(x)*exp(-inx) via substitution x → 2π-x
        -- Convert Ico set integrals to interval integrals
        have h_Ico_ii : ∀ (g : ℝ → ℂ),
            ∫ x in Set.Ico (0:ℝ) (2*Real.pi), g x =
            ∫ x in (0:ℝ)..(2*Real.pi), g x := by
          intro g
          rw [intervalIntegral.integral_of_le (by positivity)]
          exact (MeasureTheory.setIntegral_congr_set Ico_ae_eq_Ioc.symm).symm
        rw [h_Ico_ii, h_Ico_ii]
        -- Substitute x ↦ 2π-x in the LHS using integral_comp_sub_left
        trans ∫ x in (0:ℝ)..(2*Real.pi),
          f (-(2*Real.pi - x)) *
            Complex.exp (Complex.I * ↑n * (↑(2*Real.pi - x) : ℂ))
        · -- ∫ f(-x)*exp(inx) = ∫ f(-(2π-x))*exp(in(2π-x)) by substitution
          have h := intervalIntegral.integral_comp_sub_left
            (a := 0) (b := 2 * Real.pi)
            (fun t => f (-t) * Complex.exp (Complex.I * ↑n * (↑t : ℂ)))
            (2 * Real.pi)
          simp only [sub_self, sub_zero] at h
          exact h.symm
        · -- Pointwise: f(-(2π-x))*exp(in(2π-x)) = f(x)*exp(-inx)
          apply intervalIntegral.integral_congr
          intro x _; dsimp only
          -- f(-(2π-x)) = f(x-2π) = f(x) by periodicity
          have h_sub_per : f (x - 2 * Real.pi) = f x := by
            have := hf_per (x - 2 * Real.pi); rw [sub_add_cancel] at this; exact this.symm
          rw [show -((2:ℝ) * Real.pi - x) = x - 2 * Real.pi from by ring, h_sub_per]
          congr 1
          rw [show (↑((2:ℝ) * Real.pi - x) : ℂ) = 2 * ↑Real.pi - ↑x from by
            push_cast; ring]
          rw [show Complex.I * ↑n * (2 * ↑Real.pi - ↑x) =
              ↑n * (2 * ↑Real.pi * Complex.I) + (-Complex.I * ↑n * ↑x) from by
            ring]
          rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
      -- Conclude: c = ↑(c.re) since c.im = 0
      rw [h_fc]
      exact (Complex.ext (by simp) (by simp [h_im])).symm
    -- Summability of Fourier coefficients (from h_coeff + Summable μ)
    have h_summ_F : Summable (fun n => _root_.fourierCoeff (⇑F : AddCircle (2 * Real.pi) → ℂ) n) := by
      simp_rw [h_coeff]
      exact Summable.of_norm_bounded h_summ (fun k =>
        le_of_eq (Complex.norm_of_nonneg (h_nn k)))
    -- Apply Mathlib's pointwise Fourier inversion
    intro θ
    have h_ptwise := has_pointwise_sum_fourier_series_of_summable h_summ_F
      (↑θ : AddCircle (2 * Real.pi))
    -- HasSum (fun i => fourierCoeff F i • fourier i (↑θ)) (F(↑θ))
    conv_lhs => rw [show f θ = (F : AddCircle (2 * Real.pi) → ℂ) ↑θ from (hF_eval θ).symm]
    rw [← h_ptwise.tsum_eq]
    congr 1; funext k
    simp only [h_coeff, smul_eq_mul]
    -- Need: ↑(μ k) * fourier k (↑θ) = ↑(μ k) * exp(I * ↑k * ↑θ)
    congr 1
    -- fourier k (↑θ : AddCircle(2π)) = exp(2πIkθ/(2π)) = exp(Ikθ)
    rw [fourier_coe_apply]
    congr 1
    have h2pi_ne : (↑(2 * Real.pi) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
    field_simp
    push_cast
    ring
  exact ⟨μ, h_nn, h_summ, h_inv⟩

/-- Fejér-Riesz via sheaf: non-negative trig poly = |P|² -/
theorem fejer_riesz_via_sheaf (R : ℝ → ℂ)
    (hR_trig : ∃ (N : ℕ) (c : Fin (2*N+1) → ℂ),
      ∀ θ, R θ = ∑ k : Fin (2*N+1), c k * Complex.exp (Complex.I * (k.val - N) * θ))
    (hR_real : ∀ θ, (R θ).im = 0)
    (hR_nonneg : ∀ θ, 0 ≤ (R θ).re) :
    ∃ (P : ℝ → ℂ),
      (∃ (M : ℕ) (d : Fin (M+1) → ℂ),
        ∀ θ, P θ = ∑ k : Fin (M+1), d k * Complex.exp (Complex.I * k * θ)) ∧
      ∀ θ, R θ = Complex.normSq (P θ) := by
  -- Bridge to fejer_riesz_analytic from FourierBochner.lean
  obtain ⟨N, c, hR_eq⟩ := hR_trig
  -- Construct TrigPolyℤ from Fourier coefficients
  -- R_trig(m) = c(m + N) for m ∈ [-N, N]
  classical
  let R_trig : TrigPolyℤ :=
    (Finset.univ : Finset (Fin (2*N+1))).sum
      (fun k => Finsupp.single ((k.val : ℤ) - ↑N) (c k))
  -- Evaluation bridge
  -- R_trig.toCircle(x : 𝕋) = R(2πx) because:
  --   fourier m (x : 𝕋) = exp(2πimx)
  --   and R_trig(m) = c(m+N), so ∑ R_trig(m) * exp(2πimx) = ∑ c_k * exp(2πi(k-N)x) = R(2πx)
  have h_bridge : ∀ x : ℝ, R_trig.toCircle (↑x : 𝕋) = R (2 * Real.pi * x) := by
    intro x
    rw [hR_eq]
    -- Unfold toCircle to explicit sum
    simp only [TrigPolyℤ.toCircle, ContinuousMap.coe_mk]
    -- Trans through ∑ k, c k * fourier(k.val - N)(↑x)
    trans (∑ k : Fin (2 * N + 1), c k * fourier ((k.val : ℤ) - ↑N) (↑x : 𝕋))
    · -- Distribute Finsupp.sum over the finite sum of singles
      rw [show (∑ n ∈ R_trig.support, R_trig n * fourier n (↑x : 𝕋)) =
          ((Finset.univ : Finset (Fin (2*N+1))).sum
            (fun k => Finsupp.single ((k.val : ℤ) - ↑N) (c k))).sum
          (fun n (a : ℂ) => a * fourier n (↑x : 𝕋)) from rfl]
      rw [← Finsupp.sum_finset_sum_index
        (fun n => zero_mul (fourier n (↑x : 𝕋)))
        (fun n b₁ b₂ => add_mul b₁ b₂ (fourier n (↑x : 𝕋)))]
      congr 1; funext k
      exact Finsupp.sum_single_index (zero_mul _)
    · -- Match fourier evaluation with exp
      congr 1; funext k; congr 1
      rw [fourier_coe_apply]
      simp only [Complex.ofReal_one, div_one]
      push_cast; ring_nf
  -- Step 3: Transfer reality and non-negativity through bridge
  -- Every t ∈ 𝕋 = ℝ/ℤ is (x : 𝕋) for some x : ℝ
  -- So R_trig.toCircle t = R(2πx) which is real and non-negative
  have hR_real_trig : ∀ t : 𝕋, (R_trig.toCircle t).im = 0 := by
    intro t
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [h_bridge]; exact hR_real _
  have hR_nonneg_trig : ∀ t : 𝕋, 0 ≤ (R_trig.toCircle t).re := by
    intro t
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [h_bridge]; exact hR_nonneg _
  -- Step 4: Apply Fejér-Riesz (analytic version from FourierBochner)
  obtain ⟨P, hP_analytic, hP_eq⟩ := fejer_riesz_analytic R_trig hR_real_trig hR_nonneg_trig
  -- Step 5: Define output P_func(θ) = P.toCircle(θ/(2π))
  refine ⟨fun θ => P.toCircle (↑(θ / (2 * Real.pi)) : 𝕋), ?_, ?_⟩
  · -- Step 5a: P_func is an analytic trigonometric polynomial
    by_cases hP_zero : P = 0
    · exact ⟨0, fun _ => 0, fun θ => by
        simp only [TrigPolyℤ.toCircle, ContinuousMap.coe_mk, hP_zero,
          Finsupp.support_zero, Finset.sum_empty]
        simp [Fin.sum_univ_one]⟩
    · -- P ≠ 0: use max support element as degree bound
      have h_ne : P.support.Nonempty := Finsupp.support_nonempty_iff.mpr hP_zero
      have hM_nn : (0 : ℤ) ≤ P.support.max' h_ne :=
        hP_analytic _ (Finset.max'_mem _ h_ne)
      refine ⟨(P.support.max' h_ne).toNat, fun k => P (↑k.val), fun θ => ?_⟩
      simp only [TrigPolyℤ.toCircle, ContinuousMap.coe_mk]
      set M := (P.support.max' h_ne).toNat with hM_def
      -- Step 1: Convert fourier to exp on LHS
      have h_four : ∀ n ∈ P.support,
          P n * fourier n ((θ / (2 * Real.pi) : ℝ) : AddCircle (1:ℝ)) =
          P n * Complex.exp (Complex.I * ↑n * ↑θ) := by
        intro n _; congr 1
        rw [fourier_coe_apply]
        simp only [Complex.ofReal_one, div_one]
        congr 1; push_cast; field_simp
      rw [Finset.sum_congr rfl h_four]
      -- Step 2: Extend from P.support to (range(M+1)).image(Nat.cast)
      have h_sub : P.support ⊆
          (Finset.range (M + 1)).image (Nat.cast : ℕ → ℤ) := by
        intro n hn
        simp only [Finset.mem_image, Finset.mem_range]
        refine ⟨n.toNat, ?_, Int.toNat_of_nonneg (hP_analytic n hn)⟩
        have h_le := Finset.le_max' _ n hn; omega
      rw [Finset.sum_subset h_sub (fun n _ hn => by
        simp [Finsupp.notMem_support_iff.mp hn])]
      -- Step 3: Reindex from image(range) to range via sum_image
      rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h :
        Set.InjOn (Nat.cast : ℕ → ℤ) ↑(Finset.range (M + 1)))]
      -- Step 4: Convert range to Fin
      rw [← Fin.sum_univ_eq_sum_range]
      -- Step 5: Normalize coercions (ℕ → ℤ → ℂ vs ℕ → ℂ)
      simp only [Int.cast_natCast]
  · -- Step 5b: R(θ) = |P_func(θ)|²
    intro θ
    have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    calc R θ
        = R (2 * Real.pi * (θ / (2 * Real.pi))) := by
            congr 1; field_simp
      _ = R_trig.toCircle (↑(θ / (2 * Real.pi)) : 𝕋) := (h_bridge _).symm
      _ = (TrigPolyℤ.normSq P).toCircle (↑(θ / (2 * Real.pi)) : 𝕋) := by
            rw [← hP_eq]
      _ = ↑(Complex.normSq (P.toCircle (↑(θ / (2 * Real.pi)) : 𝕋))) :=
            TrigPolyℤ.normSq_toCircle_eval P _


/-! ## Section 10: Bochner-Herglotz Spectral Measure -/

open MeasureTheory Measure ENNReal in
/-- Bochner-Herglotz Spectral Measure Theorem. -/
theorem bochner_spectral_measure (f : ℝ → ℂ) (hf : Continuous f)
    (hf_pd : FourierBochner.IsPositiveDefinite f)
    (hf_per : ∀ θ, f (θ + 2 * Real.pi) = f θ) :
    ∃ (μ : MeasureTheory.Measure ℤ), IsFiniteMeasure μ ∧
      ∀ θ : ℝ, f θ = ∑' k : ℤ,
        ↑((μ {k}).toReal) * Complex.exp (Complex.I * ↑k * ↑θ) := by
  obtain ⟨w, hw_nn, hw_summ, hw_repr⟩ := constructive_bochner_via_sheaf f hf hf_pd hf_per
  refine ⟨Measure.sum (fun k : ℤ => ENNReal.ofReal (w k) • Measure.dirac k), ?_, ?_⟩
  · -- IsFiniteMeasure: μ(univ) = ∑' ENNReal.ofReal(w k) < ⊤
    constructor
    simp only [Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one]
    exact hw_summ.tsum_ofReal_lt_top
  · -- Representation: (μ {k}).toReal = w k, then apply hw_repr
    intro θ
    rw [hw_repr θ]
    congr 1; ext k
    congr 1
    -- Compute (Measure.sum ...) {k} and take .toReal
    simp only [Measure.sum_apply _ (measurableSet_singleton k),
      Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton k),
      Set.indicator_apply, Set.mem_singleton_iff]
    simp only [mul_ite, Pi.one_apply, mul_one, mul_zero, tsum_ite_eq,
      ENNReal.toReal_ofReal (hw_nn k)]


end FourierBochner
