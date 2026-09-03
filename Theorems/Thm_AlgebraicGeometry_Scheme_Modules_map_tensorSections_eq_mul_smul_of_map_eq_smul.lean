import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_map_tensorSections_eq_mul_smul_of_map_eq_smul
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.map_tensorSections_eq_mul_smul_of_map_eq_smul
    {X : Scheme.{u}} {L L' : X.Modules} {U V : X.Opens}
    (sU : Γ(L, U)) (sV : Γ(L, V)) (sU' : Γ(L', U)) (sV' : Γ(L', V)) (t t' : Γ(X, U ⊓ V))
    (ht : L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU =
      t • L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV)
    (ht' : L'.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU' =
      t' • L'.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV') :
    (L ⊗ L').presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (Scheme.Modules.tensorSections sU sU') =
      (t * t') • (L ⊗ L').presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op
        (Scheme.Modules.tensorSections sV sV') := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_map_tensorSections_eq_mul_smul_of_map_eq_smul.solution
