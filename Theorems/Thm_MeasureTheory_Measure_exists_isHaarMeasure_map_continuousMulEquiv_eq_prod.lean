import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_Measure_exists_isHaarMeasure_map_continuousMulEquiv_eq_prod

set_option autoImplicit false

universe u₁ u₂ u₃

theorem MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod
    {G : Type u₁} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    {G₁ : Type u₂} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
      [SigmaCompactSpace G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    {G₂ : Type u₃} [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SigmaCompactSpace G₂]
      [MeasurableSpace G₂] [BorelSpace G₂]
    (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (e : G ≃ₜ* G₁ × G₂) :
    ∃ μ₂ : Measure G₂, μ₂.IsHaarMeasure ∧ (μ.IsMulRightInvariant → μ₂.IsMulRightInvariant) ∧
      μ.map e = μ₁.prod μ₂ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_Measure_exists_isHaarMeasure_map_continuousMulEquiv_eq_prod.solution
