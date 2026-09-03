import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_surjective_and_generalizingMap_pullback_fst_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.surjective_and_generalizingMap_pullback_fst_of_flat
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g] [Surjective g] :
    Surjective (pullback.fst f g) ∧ GeneralizingMap (pullback.fst f g).base ∧
      ∀ η : ↥(pullback f g), (∀ η' : ↥(pullback f g), η' ⤳ η → η' = η) →
        ∀ y : ↥X, y ⤳ (pullback.fst f g).base η → y = (pullback.fst f g).base η := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_surjective_and_generalizingMap_pullback_fst_of_flat.solution
