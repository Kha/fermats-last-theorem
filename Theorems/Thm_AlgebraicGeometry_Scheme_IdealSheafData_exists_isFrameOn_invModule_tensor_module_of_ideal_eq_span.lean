import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_isFrameOn_invModule_tensor_module_of_ideal_eq_span
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.ExteriorPower.instModulePresheafAb
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_isFrameOn_invModule_tensor_module_of_ideal_eq_span
    {X : Scheme.{u}} (I₁ I₂ : X.IdealSheafData) (W₂ W₃ : X.Opens)
    (a a' : Γ(X, W₂))
    (ha : ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W₂),
      I₂.ideal U = Ideal.span {X.presheaf.map (homOfLE hU).op a} ∧
        X.presheaf.map (homOfLE hU).op a ∈ nonZeroDivisors Γ(X, U))
    (ha' : ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W₂),
      I₁.ideal U = Ideal.span {X.presheaf.map (homOfLE hU).op a'} ∧
        X.presheaf.map (homOfLE hU).op a' ∈ nonZeroDivisors Γ(X, U))
    (h₃ : ∀ (U : X.affineOpens), (U : X.Opens) ≤ W₃ → I₁.ideal U = ⊤ ∧ I₂.ideal U = ⊤)
    (t : Γ(X, W₂ ⊓ W₃))
    (ht : t * X.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op a =
      X.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op a') :
    ∃ (p : Γ(I₁.invModule ⊗ I₂.module, W₂)) (q : Γ(I₁.invModule ⊗ I₂.module, W₃)),
      Scheme.Modules.IsFrameOn p W₂ ∧ Scheme.Modules.IsFrameOn q W₃ ∧
      (I₁.invModule ⊗ I₂.module).presheaf.map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op q =
        t • (I₁.invModule ⊗ I₂.module).presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op p := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_isFrameOn_invModule_tensor_module_of_ideal_eq_span.solution
