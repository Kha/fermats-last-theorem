import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y] (U : X.Opens) (hU : IsIso (f ∣_ U))
    (V : X.Opens) (hV : Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op)) :
    IsIso (f.app V) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map.solution
