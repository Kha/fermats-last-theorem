import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_pair_of_pullback_map_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullback_map_conj_eq_trivialization_pair_of_pullback_map_eq
    {B A Y Y₂ T T₂ : Scheme.{u}} (e : B ⟶ A) (ι κ : Y ⟶ A) (ι₂ κ₂ : Y₂ ⟶ A)
    (ε : T ⟶ Y) (p q : T ⟶ B) (hp : ε ≫ ι = p ≫ e) (hq : ε ≫ κ = q ≫ e)
    (ε₂ : T₂ ⟶ Y₂) (p₂ q₂ : T₂ ⟶ B) (hp₂ : ε₂ ≫ ι₂ = p₂ ≫ e) (hq₂ : ε₂ ≫ κ₂ = q₂ ≫ e)
    (j : Y₂ ⟶ Y) (hjι : j ≫ ι = ι₂) (hjκ : j ≫ κ = κ₂)
    (lam : T₂ ⟶ T) (hlam : ε₂ ≫ j = lam ≫ ε) (hlamp : lam ≫ p = p₂) (hlamq : lam ≫ q = q₂)
    (L : A.Modules)
    (hLe : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (φ : (Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback κ).obj L)
    (hφ : (Scheme.Modules.pullback ε).map φ.hom =
        ((Scheme.Modules.pullbackComp ε ι).app L ≪≫ (Scheme.Modules.pullbackCongr hp).app L ≪≫
            ((Scheme.Modules.pullbackComp p e).app L).symm ≪≫ (Scheme.Modules.pullback p).mapIso hLe ≪≫
            Scheme.Modules.pullbackUnitIso p).hom ≫
        ((Scheme.Modules.pullbackComp ε κ).app L ≪≫ (Scheme.Modules.pullbackCongr hq).app L ≪≫
            ((Scheme.Modules.pullbackComp q e).app L).symm ≪≫ (Scheme.Modules.pullback q).mapIso hLe ≪≫
            Scheme.Modules.pullbackUnitIso q).inv) :
    (Scheme.Modules.pullback ε₂).map
        (((Scheme.Modules.pullbackComp j ι).app L ≪≫ (Scheme.Modules.pullbackCongr hjι).app L).symm ≪≫
          (Scheme.Modules.pullback j).mapIso φ ≪≫
          ((Scheme.Modules.pullbackComp j κ).app L ≪≫ (Scheme.Modules.pullbackCongr hjκ).app L)).hom =
      ((Scheme.Modules.pullbackComp ε₂ ι₂).app L ≪≫ (Scheme.Modules.pullbackCongr hp₂).app L ≪≫
          ((Scheme.Modules.pullbackComp p₂ e).app L).symm ≪≫ (Scheme.Modules.pullback p₂).mapIso hLe ≪≫
          Scheme.Modules.pullbackUnitIso p₂).hom ≫
      ((Scheme.Modules.pullbackComp ε₂ κ₂).app L ≪≫ (Scheme.Modules.pullbackCongr hq₂).app L ≪≫
          ((Scheme.Modules.pullbackComp q₂ e).app L).symm ≪≫ (Scheme.Modules.pullback q₂).mapIso hLe ≪≫
          Scheme.Modules.pullbackUnitIso q₂).inv := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_pair_of_pullback_map_eq.solution
