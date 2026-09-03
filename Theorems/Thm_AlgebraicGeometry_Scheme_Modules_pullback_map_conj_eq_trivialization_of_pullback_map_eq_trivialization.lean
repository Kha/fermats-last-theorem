import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
    {B A Y Y₂ T T₂ : Scheme.{u}} (e : B ⟶ A) (ι : Y ⟶ A) (ι₂ : Y₂ ⟶ A)
    (ε : T ⟶ Y) (p : T ⟶ B) (hp : ε ≫ ι = p ≫ e)
    (ε₂ : T₂ ⟶ Y₂) (p₂ : T₂ ⟶ B) (hp₂ : ε₂ ≫ ι₂ = p₂ ≫ e)
    (j : Y₂ ⟶ Y) (hj : j ≫ ι = ι₂) (lam : T₂ ⟶ T) (hlam : ε₂ ≫ j = lam ≫ ε) (hlamp : lam ≫ p = p₂)
    (L M : A.Modules)
    (hLe : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (hMe : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (φ : (Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback ι).obj M)
    (hφ : (Scheme.Modules.pullback ε).map φ.hom =
        ((Scheme.Modules.pullbackComp ε ι).app L ≪≫ (Scheme.Modules.pullbackCongr hp).app L ≪≫
            ((Scheme.Modules.pullbackComp p e).app L).symm ≪≫ (Scheme.Modules.pullback p).mapIso hLe ≪≫
            Scheme.Modules.pullbackUnitIso p).hom ≫
        ((Scheme.Modules.pullbackComp ε ι).app M ≪≫ (Scheme.Modules.pullbackCongr hp).app M ≪≫
            ((Scheme.Modules.pullbackComp p e).app M).symm ≪≫ (Scheme.Modules.pullback p).mapIso hMe ≪≫
            Scheme.Modules.pullbackUnitIso p).inv) :
    (Scheme.Modules.pullback ε₂).map
        (((Scheme.Modules.pullbackComp j ι).app L ≪≫ (Scheme.Modules.pullbackCongr hj).app L).symm ≪≫
          (Scheme.Modules.pullback j).mapIso φ ≪≫
          ((Scheme.Modules.pullbackComp j ι).app M ≪≫ (Scheme.Modules.pullbackCongr hj).app M)).hom =
      ((Scheme.Modules.pullbackComp ε₂ ι₂).app L ≪≫ (Scheme.Modules.pullbackCongr hp₂).app L ≪≫
          ((Scheme.Modules.pullbackComp p₂ e).app L).symm ≪≫ (Scheme.Modules.pullback p₂).mapIso hLe ≪≫
          Scheme.Modules.pullbackUnitIso p₂).hom ≫
      ((Scheme.Modules.pullbackComp ε₂ ι₂).app M ≪≫ (Scheme.Modules.pullbackCongr hp₂).app M ≪≫
          ((Scheme.Modules.pullbackComp p₂ e).app M).symm ≪≫ (Scheme.Modules.pullback p₂).mapIso hMe ≪≫
          Scheme.Modules.pullbackUnitIso p₂).inv := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization.solution
