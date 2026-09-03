import Mathlib
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_PDivisibleGroup_PrimaryTorsion
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair

set_option autoImplicit false

theorem PDivisibleGroup.CartierDuality.exists_points_tateModule_pairing_eq_pair
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] {G G' : PDivisibleGroup R p h}
    (D : G.CartierDuality G') (L : Type) [CommRing L] [Algebra R L] :
    ∃ α : G.Points L →+ (TateModule p (G'.Points L) →ₗ[ℤ_[p]] PrimaryTorsion p (Additive Lˣ)),
      (∀ (v : ℕ) (f : G.Point L v) (y : TateModule p (G'.Points L)) (ψ : G'.Point L v),
          G'.pointsMkAdd L v (Additive.ofMul ψ) = (y : ℕ → G'.Points L) v →
          ((Additive.toMul ((α (G.pointsMkAdd L v (Additive.ofMul f)) y :
              PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) = D.pair L v f ψ) ∧
      (∀ (σ : L ≃ₐ[R] L) (z : G.Points L) (y : TateModule p (G'.Points L)),
          ((Additive.toMul ((α (σ • z) (G'.tateModuleRep L σ y) :
              PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L) =
            σ (((Additive.toMul ((α z y : PrimaryTorsion p (Additive Lˣ)) : Additive Lˣ) : Lˣ) : L))) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair.solution
