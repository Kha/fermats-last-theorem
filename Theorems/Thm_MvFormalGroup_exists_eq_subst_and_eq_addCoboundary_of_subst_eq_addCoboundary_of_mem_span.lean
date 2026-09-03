import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

universe u

theorem MvFormalGroup.exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span
    {k : Type u} [Field k] {n : ℕ} (F : MvFormalGroup n k) [F.IsComm]
    (φ : Fin n → MvPowerSeries (Fin n) k) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφF : ∀ i, MvPowerSeries.subst F.toPowerSeries (φ i) =
      MvPowerSeries.subst
        (Sum.elim
          (fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
          fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        (F.toPowerSeries i))
    (hfin : Module.Finite k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range φ)))
    (Γ : MvPowerSeries (Fin n ⊕ Fin n) k) (hΓ : F.IsSymmTwoCocycle Γ)
    (g : MvPowerSeries (Fin n) k) (hg0 : MvPowerSeries.constantCoeff g = 0)
    (hg : MvPowerSeries.subst
        (Sum.elim
          (fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
          fun j => MvPowerSeries.subst
            (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin n ⊕ Fin n) k)) (φ j))
        Γ = F.addCoboundary g)
    (hgI : g ∈ Ideal.span (Set.range φ)) :
    ∃ G : MvPowerSeries (Fin n) k, MvPowerSeries.constantCoeff G = 0 ∧
      g = MvPowerSeries.subst φ G ∧ Γ = F.addCoboundary G := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_eq_subst_and_eq_addCoboundary_of_subst_eq_addCoboundary_of_mem_span.solution
