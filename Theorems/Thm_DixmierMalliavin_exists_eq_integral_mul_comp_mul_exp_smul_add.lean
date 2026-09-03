import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support
import P2M.Util
import P2M.Sol.S_DixmierMalliavin_exists_eq_integral_mul_comp_mul_exp_smul_add

set_option autoImplicit false

theorem DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (X : A) (ε : ℝ) (hε : 0 < ε) (Φ : A → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (Φ₁ : A → ℂ) (φ ψ : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ tsupport Φ₁ ⊆ tsupport Φ ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      tsupport φ ⊆ Set.Icc (-ε) ε ∧ tsupport ψ ⊆ Set.Icc (-ε) ε ∧
      ∀ x : A, Φ x = (∫ t, φ t * Φ₁ (x * NormedSpace.exp (t • X))) +
        ∫ t, ψ t * Φ (x * NormedSpace.exp (t • X)) := by p2m_exact_reverting @_root_.P2MW.S_DixmierMalliavin_exists_eq_integral_mul_comp_mul_exp_smul_add.solution
