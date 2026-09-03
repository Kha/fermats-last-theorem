import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_exists_tateModule_pairing_eq_pair

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.exists_tateModule_pairing_eq_pair
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (L : Type) [CommRing L] [Algebra R L] :
    ∃ B : TateModule p (G.Points L) →ₗ[ℤ_[p]] TateModule p (G'.Points L) →ₗ[ℤ_[p]] TateModule p (Additive Lˣ),
      (∀ (x : TateModule p (G.Points L)) (y : TateModule p (G'.Points L)) (v : ℕ)
          (f : G.Point L v) (ψ : G'.Point L v),
          G.pointsMkAdd L v (Additive.ofMul f) = (x : ℕ → G.Points L) v →
          G'.pointsMkAdd L v (Additive.ofMul ψ) = (y : ℕ → G'.Points L) v →
          ((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L) = D.pair L v f ψ) ∧
      (∀ (σ : L ≃ₐ[R] L) (x : TateModule p (G.Points L)) (y : TateModule p (G'.Points L)) (v : ℕ),
          ((Additive.toMul ((B (G.tateModuleRep L σ x) (G'.tateModuleRep L σ y) : ℕ → Additive Lˣ) v) : Lˣ) : L) =
            σ (((Additive.toMul ((B x y : ℕ → Additive Lˣ) v) : Lˣ) : L))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_exists_tateModule_pairing_eq_pair.solution
