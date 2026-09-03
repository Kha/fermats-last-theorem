import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Definitions.Def_AlgebraicGeometry_ModulesTildePullback
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_baseChange_sections_of_isIso_fromTildeGamma
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec R).Modules) (hM : IsIso M.fromTildeΓ) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv
        ((moduleSpecΓFunctor (R := R)).obj M)
        ((moduleSpecΓFunctor (R := S)).obj ((Scheme.Modules.pullback (Spec.map φ)).obj M))).symm
      ((moduleSpecΓFunctor (R := R)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
        (Scheme.Modules.pushforwardSpecCompΓIso φ).hom.app ((Scheme.Modules.pullback (Spec.map φ)).obj M))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_baseChange_sections_of_isIso_fromTildeGamma.solution
