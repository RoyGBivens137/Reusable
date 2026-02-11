/-
Copyright (c) 2025 Zachary Mullaghy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zachary Mullaghy, Gianfranco Romaelle
-/
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.Polynomial.MahlerMeasure
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.flexible false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.style.show false
set_option linter.unusedSimpArgs false
set_option linter.style.commandStart false
/-! ## Main definitions -/

open Complex Real MeasureTheory Finset
open scoped FourierTransform ComplexConjugate

namespace FourierBochner

/-! ## Definitions -/

/-- A function f : ℝ → ℂ is positive-definite if it satisfies Hermitian symmetry and
    all Gram matrices have non-negative quadratic forms. -/
def IsPositiveDefinite (f : ℝ → ℂ) : Prop :=
  (∀ x, f (-x) = conj (f x)) ∧
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, conj (c i) * c j * f (x i - x j)).re

/-! ## Properties of Positive-Definite Functions -/

/-- Positive-definite functions satisfy f(0) ≥ 0. -/
lemma IsPositiveDefinite.zero_nonneg {f : ℝ → ℂ} (hf : IsPositiveDefinite f) :
    0 ≤ (f 0).re := by
  have := hf.2 1 (fun _ => 0) (fun _ => 1)
  simp only [univ_unique, Fin.default_eq_zero, sub_self, sum_singleton,
             map_one, mul_one, one_mul] at this
  exact this

/-! ## Finite Positive-Definite Functions on ZMod n -/

/-- A function on ℤ/nℤ is positive-definite if it satisfies conjugate symmetry -/
def IsPositiveDefiniteFinite (n : ℕ) [NeZero n] (f : ZMod n → ℂ) : Prop :=
  (∀ x, f (-x) = conj (f x)) ∧
  ∀ (c : ZMod n → ℂ), c ≠ 0 →
    letI : Fintype (ZMod n) := ZMod.fintype n
    0 < (∑ i : ZMod n, ∑ j : ZMod n, conj (c i) * c j * f (i - j)).re

/-- The k-th character on ℤ/nℤ is the k-th root of unity function. -/
noncomputable def character (n : ℕ) [NeZero n] (k : ZMod n) (m : ZMod n) : ℂ :=
  Complex.exp (2 * π * Complex.I * ((k.val * m.val : ℝ) / (n : ℝ) : ℂ))


/-- Roots of unity satisfy ω^n = 1 (the FINITE version of ‖u‖ = 1) -/
lemma character_power_n (n : ℕ) [NeZero n] (k m : ZMod n) :
    (character n k m) ^ (n : ℕ) = 1 := by
  unfold character
  -- (exp (2π I * ((k.val*m.val)/n)))^n
  -- = exp (n * 2π I * ((k.val*m.val)/n)) = exp (2π I * (k.val*m.val)) = 1
  have h := Complex.exp_nat_mul (2 * π * Complex.I * ((k.val * m.val : ℝ) / (n : ℝ) : ℂ)) n
  rw [←h]
  -- factor out `2 * π * I` so we can rewrite `↑n * (...)` inside the exponent
  have h_assoc : (n : ℂ) * (2 * π * Complex.I * ((k.val * m.val : ℝ) / (n : ℝ) : ℂ)) =
                 (2 * π * Complex.I) * ((n : ℂ) * ((k.val * m.val : ℝ) / (n : ℝ) : ℂ)) := by
    ring
  rw [h_assoc]
  have : (n : ℂ) * ((k.val * m.val : ℝ) / (n : ℝ) : ℂ) = (k.val * m.val : ℂ) := by
    push_cast; field_simp [NeZero.ne n]
  rw [this]
  -- Reorder multiplication so it matches the `exp_int_mul_two_pi_mul_I` pattern
  have h_swap : 2 * π *
   Complex.I * (k.val * m.val : ℂ) = ((k.val * m.val : ℕ) : ℤ) * (2 * π * Complex.I) := by
    norm_cast; ring
  rw [h_swap]
  -- exp(2πi * (k.val * m.val)) = 1 because k.val*m.val is an integer
  exact Complex.exp_int_mul_two_pi_mul_I ((k.val * m.val : ℕ) : ℤ)

/-- PARITY LEMMA: When n is even, -1 is a root of unity and pairs with itself. -/
lemma neg_one_root_iff_even (n : ℕ) [NeZero n] :
    (∃ k : ZMod n, character n k 1 = -1) ↔ Even n := by
  constructor
  · rintro ⟨k, hk⟩
    -- If character n k 1 = -1, then raising to the n gives (-1)^n = 1,
    -- so n must be even.
    have pow_n : (character n k 1) ^ (n : ℕ) = 1 := character_power_n n k 1
    have neg_pow : (-1 : ℂ) ^ n = 1 := by
      -- substitute character = -1
      simpa [hk] using pow_n
    have hne : (-1 : ℂ) ≠ 1 := by norm_num
    exact (neg_one_pow_eq_one_iff_even hne).mp neg_pow
  · intro hn
    rcases hn with ⟨m, rfl⟩
    -- n = m + m, and n ≠ 0 forces m ≠ 0, hence 0 < m.
    have hmpos : 0 < m := by
      by_contra h_neg
      push_neg at h_neg
      have hm0 : m = 0 := Nat.le_zero.mp h_neg
      have : m + m = 0 := by simp [hm0]
      exact (NeZero.ne (m + m)) this
    refine ⟨(m : ZMod (m + m)), ?_⟩
    unfold character
    -- Reduce the val's: (m : ZMod (m+m)).val = m since m < m+m, and 1.val = 1 since 1 < m+m.
    have hmlt : m < m + m := by
      exact lt_add_of_pos_right m hmpos
    have h1lt : 1 < m + m := by
      have hmge : 1 ≤ m := Nat.succ_le_iff.mp hmpos
      have : 2 ≤ m + m := by
        simpa using Nat.add_le_add hmge hmge
      exact lt_of_lt_of_le (by decide : 1 < 2) this
    -- rewrite the `val`s: (m : ZMod (m + m)).val = m and (1 : ZMod (m + m)).val = 1
    rw [ZMod.val_natCast_of_lt hmlt]
    -- replace any `ZMod.val 1` occurrences by `1` when present
    haveI : Fact (1 < m + m) := ⟨h1lt⟩
    rw [ZMod.val_one]
    -- Now it’s just exp(2πi * (m / (m+m))) = exp(πi) = -1
    have hmne : (m : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hmpos)
    -- massage m/(m+m) to 1/2 and finish
    -- First convert ↑(m+m) to ↑m + ↑m, then to 2*↑m (use ℝ casts to match goal with double casts)
    have h_cast : ((m + m : ℕ) : ℝ) = (m : ℝ) + (m : ℝ) := by simp [Nat.cast_add]
    have h_two_m : (m : ℝ) + (m : ℝ) = 2 * (m : ℝ) := by ring
    norm_cast
    rw [h_cast, h_two_m]
    norm_cast
    -- Now simplify: exp(2πi * m/(2m)) = exp(2πi * 1/2) = exp(πi) = -1
    -- Simplify: m * 1 = m (the 1 here is just the natural number 1 cast to ℂ)
    norm_num
    have : (2 * π * I : ℂ) * ((m : ℂ) / (2 * m : ℂ)) = (π * I : ℂ) := by
      field_simp [hmne]
    rw [this, Complex.exp_pi_mul_I]

/-- Characters live on unit circle: |exp(iθ)| = 1 for real θ. -/
lemma character_on_unit_circle (n : ℕ) [NeZero n] (k m : ZMod n) :
    ‖character n k m‖ = 1 := by
  unfold character
  -- exp(z) has norm exp(z.re), and our z has real part 0
  rw [Complex.norm_exp]
  -- The real part of (2πi * x) is 0 since I is purely imaginary
  simp only [Complex.mul_re, Complex.div_re, Complex.ofReal_re, Complex.I_re,
             Complex.mul_im, Complex.ofReal_im, Complex.I_im,
             mul_zero, zero_sub, mul_one, sub_zero, add_zero, zero_div]
  ring_nf
  simp [Real.exp_zero]

/-- STEP 2: Characters multiply with their conjugate to give 1.

On the unit circle, z * conj(z) = |z|² = 1. -/
lemma character_mul_conj (n : ℕ) [NeZero n] (k m : ZMod n) :
    character n k m * conj (character n k m) = 1 := by
  have h := character_on_unit_circle n k m
  -- Use: z * conj(z) = normSq(z) and `‖z‖ = 1` implies `normSq z = 1`
  have h_eq : Complex.normSq (character n k m) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h]
    norm_num
  rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, h_eq]
  norm_cast

/-- STEP 3: Characters multiply with their negatives to give 1.

exp(2πikm/n) * exp(-2πikm/n) = exp(0) = 1 by exp addition formula. -/
lemma character_mul_neg (n : ℕ) [NeZero n] (k m : ZMod n) :
    character n k m * character n (-k) m = 1 := by
  classical
  unfold character
  -- Handle k = 0 separately (then both characters are exp(0))
  by_cases hk : k = 0
  · subst hk
    simp
  -- In the nonzero case, (-k).val = n - k.val
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne n)
  have hnegval : (-k).val = n - k.val := by
    -- `ZMod.neg_val` is piecewise; `hk` rules out the 0-branch.
    rw [ZMod.neg_val]
    simp [hk]
  -- First combine the two fractions: a/n + b/n = (a+b)/n
  have hadd_div :
      ((k.val * m.val : ℂ) / n) + (((-k).val * m.val : ℂ) / n)
        = (((k.val + (-k).val) * m.val : ℂ) / n) := by
    -- field_simp turns /n into * (n⁻¹), then `ring` finishes.
    field_simp [hn0]
  -- Now compute k.val + (-k).val = n (as naturals), using hnegval
  have hk_le : k.val ≤ n := by
    exact Nat.le_of_lt (ZMod.val_lt k)
  have hsum_nat : k.val + (-k).val = n := by
    -- rewrite (-k).val and simplify
    simpa [hnegval, Nat.add_sub_of_le hk_le]
  have hsum_cast : ((k.val + (-k).val : ℕ) : ℂ) = (n : ℂ) := by
    exact_mod_cast hsum_nat
  -- Put it together: the total exponent becomes 2πi * (m.val : ℂ)
  rw [← Complex.exp_add]
  -- rewrite the sum inside
  have hfrac :
      ((k.val * m.val : ℂ) / n) + (((-k).val * m.val : ℂ) / n) = (m.val : ℂ) := by
    calc
      ((k.val * m.val : ℂ) / n) + (((-k).val * m.val : ℂ) / n)
          = (((k.val + (-k).val) * m.val : ℂ) / n) := hadd_div
      _ = ((↑n) * (↑m.val) / (↑n) : ℂ) := by
            have this' : ((k.val : ℂ) + ((-k).val : ℂ)) = (n : ℂ) := by
              exact_mod_cast hsum_nat
            -- rewrite (k.val + (-k).val) to n
            rw [this']
      _ = (m.val : ℂ) := by
            -- (n*m)/n = m
            field_simp [hn0]
  -- finish: exp(2πi * (m.val)) = 1 because m.val is an integer
  -- The exponent simplifies: 2πi * (k.val*m.val/n + (-k).val*m.val/n) = 2πi * m.val
  -- Rewrite the exponent using hfrac
  have h_exp_eq : 2 * π * I * ((k.val * m.val : ℝ) / (n : ℝ) : ℂ) +
                  2 * π * I * (((-k).val * m.val : ℝ) / (n : ℝ) : ℂ) =
                  (m.val : ℂ) * (2 * π * I) := by
    calc 2 * π * I * ((k.val * m.val : ℝ) / (n : ℝ) : ℂ) +
         2 * π * I * (((-k).val * m.val : ℝ) / (n : ℝ) : ℂ)
        = 2 * π * I *
         (((k.val * m.val : ℝ) / (n : ℝ) : ℂ) + (((-k).val * m.val : ℝ) / (n : ℝ) : ℂ)) := by ring
      _ = 2 * π * I * ((((k.val * m.val : ℝ) + ((-k).val * m.val : ℝ)) / (n : ℝ)) : ℂ) := by
          congr 1; push_cast; ring
      _ = 2 * π * I * (((k.val + (-k).val) * m.val : ℝ) / (n : ℝ) : ℂ) := by
          congr 1; push_cast; ring
      _ = 2 * π * I * ((n * m.val : ℝ) / (n : ℝ) : ℂ) := by
          congr 1; congr 1; congr 1
          norm_cast
          rw [hsum_nat]
      _ = 2 * π * I * (m.val : ℂ) := by
          congr 1; push_cast; field_simp [hn0]
      _ = (m.val : ℂ) * (2 * π * I) := by ring
  rw [h_exp_eq, Complex.exp_nat_mul]
  -- exp(2πi)^m.val = 1 since exp(2πi) = 1
  have : Complex.exp (2 * π * I) = 1 := by
    -- exp(2πi) = exp(πi)^2 = (-1)^2 = 1
    conv_lhs => rw [show 2 * π * I = (2 : ℕ) * (π * I) by ring]
    rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    norm_num
  simp [this]


end FourierBochner
