import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_map_tensorPowAdd_hom_comp_pullbackTensorPowIso_tensorPowMapIso_hom

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.map_tensorPowAdd_hom_comp_pullbackTensorPowIso_tensorPowMapIso_hom
    {X X' : Scheme.{u}} (c : X' ⟶ X) (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (m n : ℕ) :
    (Scheme.Modules.pullback c).map (Scheme.Modules.tensorPowAdd L m n).hom ≫
        (Scheme.Modules.pullbackTensorPowIso c L (m + n) ≪≫ Scheme.Modules.tensorPowMapIso e (m + n)).hom =
      (Scheme.Modules.pullbackTensorObjIso c (L.tensorPow m) (L.tensorPow n)).hom ≫
        ((Scheme.Modules.pullbackTensorPowIso c L m ≪≫ Scheme.Modules.tensorPowMapIso e m).hom ⊗ₘ
          (Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom) ≫
        (Scheme.Modules.tensorPowAdd L' m n).hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_map_tensorPowAdd_hom_comp_pullbackTensorPowIso_tensorPowMapIso_hom.solution
