import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict

set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X) (hsm : MeasurableSet s) (hs : μ s ≠ ⊤)
    (V : Submodule ℂ (X → ℂ))
    (hmeas : ∀ φ ∈ V, AEStronglyMeasurable φ (μ.restrict s))
    (hinj : ∀ φ ∈ V, (∀ x ∈ s, φ x = 0) → φ = 0)
    (C : ℝ)
    (hsup : ∀ φ ∈ V, ∀ x ∈ s, ‖φ x‖ ≤ C * (eLpNorm φ 2 (μ.restrict s)).toReal) :
    FiniteDimensional ℂ V ∧ (Module.finrank ℂ V : ℝ) ≤ C ^ 2 * (μ s).toReal := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_finiteDimensional_and_finrank_le_of_forall_norm_le_mul_eLpNorm_restrict.solution
