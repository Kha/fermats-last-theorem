import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_unitSection

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"

theorem solution
    {X X' : Scheme.{u}} (c : X' ⟶ X) (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L') :
    ((Scheme.Modules.pullbackTensorPowIso c L 0 ≪≫ Scheme.Modules.tensorPowMapIso e 0).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow 0)).app ⊤) (Scheme.Modules.unitSection ⊤))
      = Scheme.Modules.unitSection ⊤ := by
  have h := AlgebraicGeometry.Scheme.Modules.pullbackTensorUnitObjIso_hom_app_pullbackLocalSection_unitSection_monoidalV2 c (⊤ : X.Opens)
  rw [Scheme.Modules.pullbackLocalSection_def] at h
  simp only [Iso.trans_hom, Scheme.Modules.pullbackTensorPowIso, Scheme.Modules.tensorPowMapIso, Iso.refl_hom, Category.comp_id]
  exact h
