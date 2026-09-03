import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
    {X : Scheme.{u}} {ι : Type u} [LinearOrder ι] (T : ι → X.Opens) (hT : ⨆ k, T k = ⊤)
    {L L' : X.Modules} (s : ∀ k, Γ(L, T k)) (s' : ∀ k, Γ(L', T k))
    (hs : ∀ k, Scheme.Modules.IsFrameOn (s k) (T k)) (hs' : ∀ k, Scheme.Modules.IsFrameOn (s' k) (T k))
    (h : ∀ (i j : ι), i < j → ∀ g : Γ(X, T i ⊓ T j),
      HSMul.hSMul g (L.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s i)) =
          L.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s j) →
        HSMul.hSMul g (L'.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op (s' i)) =
          L'.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op (s' j)) :
    ∃ e : L ≅ L', ∀ k, e.hom.app (T k) (s k) = s' k := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq.solution
