import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Support
import P2M.Util
import P2M.Sol.S_DixmierMalliavin_exists_eq_sum_integral_mul_comp_mul

set_option autoImplicit false

theorem DixmierMalliavin.exists_eq_sum_integral_mul_comp_mul {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] [MeasurableSpace A] [BorelSpace A]
    (μ : MeasureTheory.Measure A) [μ.IsAddHaarMeasure] (U : Set A) (hU : U ∈ nhds (1 : A))
    (Φ : A → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ∃ (n : ℕ) (Φ' Ψ : Fin n → A → ℂ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ' k) ∧ tsupport (Φ' k) ⊆ tsupport Φ) ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (Ψ k) ∧ HasCompactSupport (Ψ k) ∧ tsupport (Ψ k) ⊆ U) ∧
      ∀ x : A, Φ x = ∑ k, ∫ y, Φ' k (x * y) * Ψ k y ∂μ := by p2m_exact_reverting @_root_.P2MW.S_DixmierMalliavin_exists_eq_sum_integral_mul_comp_mul.solution
