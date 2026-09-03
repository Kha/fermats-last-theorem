import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Φ : V ≃ₗ[ℝ] V) (hΦ : ∀ x y : V, B (Φ x) (Φ y) = B x y)
    {n₁ n₂ : ℕ} (e₁ : Fin n₁ → V) (e₂ : Fin n₂ → V)
    (h₁ : LinearIndependent ℝ e₁) (h₂ : LinearIndependent ℝ e₂)
    (hspan : (Submodule.span ℝ (Set.range e₂)).map (Φ : V →ₗ[ℝ] V) = Submodule.span ℝ (Set.range e₁))
    (ρ : V → ENNReal) (hρm : Measurable ρ) (hρ : ∀ x : V, ρ (Φ x) = ρ x) :
    Measure.map Φ
        (((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ => B (e₂ i) (e₂ j)).det|)) •
            Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity ρ) =
      ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ => B (e₁ i) (e₁ j)).det|)) •
          Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity ρ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_map_withDensity_gramMeasure_eq_of_linearEquiv_of_bilinForm_eq.solution
