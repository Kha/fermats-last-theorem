import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_tilde_pullbackSpecIso_unit

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

theorem AlgebraicGeometry.tilde.pullbackSpecIso_unit {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : ModuleCat.{u} R) :
    ((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).unit.app M ≫
      (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).map
        (tilde.pullbackSpecIso φ M).hom ≫
      (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app
        (tilde ((ModuleCat.extendScalars φ.hom).obj M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_tilde_pullbackSpecIso_unit.solution
