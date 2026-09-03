import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.Measure.exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
    {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M]
    [TopologicalSpace M] [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M]
    [MeasurableSpace M] [BorelSpace M]
    (A : Subalgebra ℝ M) (Γ : Subgroup Mˣ) (hΓ : ∀ g : Mˣ, g ∈ Γ ↔ (g : M) ∈ A)
    (n : ℕ) (e : Fin n → M) (hli : LinearIndependent ℝ e)
    (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule A)
    (χ : M →* ℝ) (hχ : Continuous χ)
    (hleft : ∀ g : Mˣ, g ∈ Γ → ∃ P : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, (g : M) * e j = ∑ i, P i j • e i) ∧ |P.det| = |χ g|)
    (hright : ∀ g : Mˣ, g ∈ Γ → ∃ Q : Matrix (Fin n) (Fin n) ℝ,
      (∀ j, e j * (g : M) = ∑ i, Q i j • e i) ∧ |Q.det| = |χ g|) :
    letI : MeasurableSpace Γ := borel Γ
    ∃ τ : Measure Γ, τ.IsHaarMeasure ∧ τ.IsMulRightInvariant ∧
      Measure.map (fun t : Γ => ((t : Mˣ) : M)) τ =
        (Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
          fun x => (ENNReal.ofReal |χ x|)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq.solution
