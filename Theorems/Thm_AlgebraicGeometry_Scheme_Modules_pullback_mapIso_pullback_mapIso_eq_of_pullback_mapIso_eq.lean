import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullback_mapIso_pullback_mapIso_eq_of_pullback_mapIso_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.pullback_mapIso_pullback_mapIso_eq_of_pullback_mapIso_eq
    {A A' B B' : Scheme.{u}} (g : A' ⟶ A) (e : B ⟶ A) (e' : B' ⟶ A') (u : B' ⟶ B) (hsq : e' ≫ g = u ≫ e)
    (L M : A.Modules)
    (ρL : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (ρM : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (φ : L ≅ M) (hφ : (Scheme.Modules.pullback e).mapIso φ = ρL ≪≫ ρM.symm) :
    (Scheme.Modules.pullback e').mapIso ((Scheme.Modules.pullback g).mapIso φ) =
      ((Scheme.Modules.pullbackComp e' g).app L ≪≫ (Scheme.Modules.pullbackCongr hsq).app L ≪≫
          ((Scheme.Modules.pullbackComp u e).app L).symm ≪≫ (Scheme.Modules.pullback u).mapIso ρL ≪≫
          Scheme.Modules.pullbackUnitIso u) ≪≫
        ((Scheme.Modules.pullbackComp e' g).app M ≪≫ (Scheme.Modules.pullbackCongr hsq).app M ≪≫
          ((Scheme.Modules.pullbackComp u e).app M).symm ≪≫ (Scheme.Modules.pullback u).mapIso ρM ≪≫
          Scheme.Modules.pullbackUnitIso u).symm := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_mapIso_pullback_mapIso_eq_of_pullback_mapIso_eq.solution
