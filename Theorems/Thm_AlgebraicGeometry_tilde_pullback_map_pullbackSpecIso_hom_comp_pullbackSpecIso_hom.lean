import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.tilde.pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom
    {R S T : CommRingCat.{u}} (φ : R ⟶ S) (ψ : S ⟶ T) (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map ψ)).map (tilde.pullbackSpecIso φ M).hom ≫
        (tilde.pullbackSpecIso ψ ((ModuleCat.extendScalars φ.hom).obj M)).hom =
      (Scheme.Modules.pullbackComp (Spec.map ψ) (Spec.map φ)).hom.app (tilde M) ≫
        (Scheme.Modules.pullbackCongr (Spec.map_comp φ ψ).symm).hom.app (tilde M) ≫
        (tilde.pullbackSpecIso (φ ≫ ψ) M).hom ≫
        (tilde.functor T).map ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_tilde_pullback_map_pullbackSpecIso_hom_comp_pullbackSpecIso_hom.solution
