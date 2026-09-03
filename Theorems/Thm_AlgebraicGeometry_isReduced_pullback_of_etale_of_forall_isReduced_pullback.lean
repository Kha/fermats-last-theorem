import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_pullback_of_etale_of_forall_isReduced_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isReduced_pullback_of_etale_of_forall_isReduced_pullback
    {κ : Type u} [Field κ] [IsAlgClosed κ] {X Y E : Scheme.{u}}
    (f : X ⟶ Y) (g : E ⟶ Y) (fE : E ⟶ Spec (CommRingCat.of κ)) [Etale fE]
    (h : ∀ y : Spec (CommRingCat.of κ) ⟶ E, y ≫ fE = 𝟙 _ → IsReduced (pullback f (y ≫ g))) :
    IsReduced (pullback f g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_pullback_of_etale_of_forall_isReduced_pullback.solution
