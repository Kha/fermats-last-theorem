import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom

set_option autoImplicit false

open MeasureTheory Measure

theorem MeasureTheory.aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [T2Space G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    {n : ℕ} (ψ : Fin n → (G →* ℂ)) (hψ : Function.Injective ψ) (c : Fin n → ℂ) (hc : ∀ i, c i ≠ 0)
    (h : AEStronglyMeasurable (fun g => ∑ i, c i * ψ i g) μ) (i : Fin n) :
    AEStronglyMeasurable (⇑(ψ i)) μ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_aestronglyMeasurable_of_aestronglyMeasurable_sum_smul_monoidHom.solution
