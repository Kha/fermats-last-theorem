import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv

set_option autoImplicit false

theorem PDivisibleGroup.bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h)
    (L : Type) [CommRing L] [Algebra R L] :
    Function.Bijective (G.pointsMap (integralClosure R L).val) ∧
    (∀ σ : L ≃ₐ[R] L, ∃ σ' : integralClosure R L ≃ₐ[R] integralClosure R L,
        ∀ x : integralClosure R L, ((σ' x : integralClosure R L) : L) = σ x) ∧
    (∀ (σ : L ≃ₐ[R] L) (σ' : integralClosure R L ≃ₐ[R] integralClosure R L),
        (∀ x : integralClosure R L, ((σ' x : integralClosure R L) : L) = σ x) →
        ∀ z : G.Points (integralClosure R L),
          G.pointsMap (integralClosure R L).val (σ' • z) = σ • G.pointsMap (integralClosure R L).val z) ∧
    ∃ e : TateModule p (G.Points (integralClosure R L)) ≃ₗ[ℤ_[p]] TateModule p (G.Points L),
      (∀ (x : TateModule p (G.Points (integralClosure R L))) (n : ℕ),
          ((e x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
            G.pointsMap (integralClosure R L).val ((x : ℕ → G.Points (integralClosure R L)) n)) ∧
      ∀ (σ : L ≃ₐ[R] L) (σ' : integralClosure R L ≃ₐ[R] integralClosure R L),
        (∀ x : integralClosure R L, ((σ' x : integralClosure R L) : L) = σ x) →
        ∀ x : TateModule p (G.Points (integralClosure R L)),
          e (G.tateModuleRep (integralClosure R L) σ' x) = G.tateModuleRep L σ (e x) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_bijective_pointsMap_val_integralClosure_and_exists_tateModule_equiv.solution
