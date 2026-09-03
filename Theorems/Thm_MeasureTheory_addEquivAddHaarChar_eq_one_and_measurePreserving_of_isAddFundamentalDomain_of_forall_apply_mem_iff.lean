import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [μ.Regular]
    (Γ : AddSubgroup G) [Countable Γ] (F : Set G) (hF : MeasureTheory.IsAddFundamentalDomain Γ F μ)
    (hFtop : μ F ≠ ⊤) (φ : G ≃ₜ+ G) (hφ : ∀ x : G, φ x ∈ Γ ↔ x ∈ Γ) :
    MeasureTheory.addEquivAddHaarChar φ = 1 ∧ MeasureTheory.MeasurePreserving φ μ μ := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff.solution
