import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_genericPoint_of_isReduced_of_forall_specializes_of_forall_exists_div

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_genericPoint_of_isReduced_of_forall_specializes_of_forall_exists_div
    {Y Z : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Z)
    (hred : _root_.IsReduced (Z.presheaf.stalk (f (genericPoint Y))))
    (hmax : ∀ z : Z, z ⤳ f (genericPoint Y) → z = f (genericPoint Y))
    (V : Z.Opens) (hV : f (genericPoint Y) ∈ V)
    (hgen : ∀ x : Y.functionField, ∃ a b : Γ(Z, V),
      Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) ≠ 0 ∧
        x * Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) =
          Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V a)) :
    IsIso (f.stalkMap (genericPoint Y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_genericPoint_of_isReduced_of_forall_specializes_of_forall_exists_div.solution
