import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

theorem AlgebraicGeometry.tilde.pullbackSpecIso_hom_app_top_unit_toOpen {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : ModuleCat.{u} R) (m : M) :
    ((tilde.pullbackSpecIso φ M).hom.app ⊤).hom
      ((((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤).hom
        ((tilde.toOpen M ⊤).hom m)) =
    (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom ((1 : S) ⊗ₜ m) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_tilde_pullbackSpecIso_hom_app_top_unit_toOpen.solution
