import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq

set_option autoImplicit false
theorem PDivisibleGroup.exists_linearMap_tateModule_of_comp_transition_eq
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (L : Type) [Field L] [Algebra R L]
    {h h' : ℕ} (G : PDivisibleGroup R p h) (Γ : PDivisibleGroup R p h')
    (φ : ∀ v : ℕ, G.level v →ₐc[R] Γ.level v)
    (hφ : ∀ v : ℕ, (φ v).comp (G.transition v) = (Γ.transition v).comp (φ (v + 1))) :
    ∃ Tφ : TateModule p (Γ.Points L) →ₗ[ℤ_[p]] TateModule p (G.Points L),
      (∀ (x : TateModule p (Γ.Points L)) (n w : ℕ) (g : Γ.Point L w),
        Γ.pointsMkAdd L w (Additive.ofMul g) = (x : ℕ → Γ.Points L) n →
        ((Tφ x : TateModule p (G.Points L)) : ℕ → G.Points L) n =
          G.pointsMkAdd L w (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom g).comp (φ w : G.level w →ₐ[R] Γ.level w))))) ∧
      (∀ (τ : L ≃ₐ[R] L) (x : TateModule p (Γ.Points L)),
        Tφ (Γ.tateModuleRep L τ x) = G.tateModuleRep L τ (Tφ x)) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_exists_linearMap_tateModule_of_comp_transition_eq.solution
