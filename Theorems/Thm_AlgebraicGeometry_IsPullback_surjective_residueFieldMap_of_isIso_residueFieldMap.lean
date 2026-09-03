import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsPullback_surjective_residueFieldMap_of_isIso_residueFieldMap

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.IsPullback.surjective_residueFieldMap_of_isIso_residueFieldMap
    {P X T S : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (H : IsPullback fst snd f g) (t : ↥P) [IsIso (f.residueFieldMap (fst.base t))] :
    Function.Surjective (snd.residueFieldMap t).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsPullback_surjective_residueFieldMap_of_isIso_residueFieldMap.solution
