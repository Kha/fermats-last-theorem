import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.exists_opens_extension_of_fromSpecStalk
    {S G H : Scheme.{u}} (sG : G ⟶ S) (sH : H ⟶ S) [LocallyOfFiniteType sH]
    (η : G) [G.IsGermInjectiveAt η]
    (w : Spec (G.presheaf.stalk η) ⟶ H) (hw : w ≫ sH = G.fromSpecStalk η ≫ sG) :
    ∃ (U : G.Opens) (hη : η ∈ U) (v : (U : Scheme.{u}) ⟶ H),
      v ≫ sH = U.ι ≫ sG ∧ U.fromSpecStalkOfMem η hη ≫ v = w := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_opens_extension_of_fromSpecStalk.solution
