import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory _root_.CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme in

theorem solution
    {Y T : AlgebraicGeometry.Scheme.{u}} (q : Y ⟶ T) (V : T.Opens) (L : Y.Modules) (N : T.Modules)
    (eN : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj N ≅ 𝟙_ ((V : AlgebraicGeometry.Scheme.{u}).Modules)) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj
        (L ⊗ (AlgebraicGeometry.Scheme.Modules.pullback q).obj N) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj L) := by
  have hfact : (q ⁻¹ᵁ V).ι ≫ q = (q ∣_ V) ≫ V.ι := (morphismRestrict_ι q V).symm
  refine ⟨Scheme.Modules.pullbackTensorObjIso (q ⁻¹ᵁ V).ι L _ ≪≫ (Iso.refl _ ⊗ᵢ ?_) ≪≫ ρ_ _⟩
  exact (Scheme.Modules.pullbackComp (q ⁻¹ᵁ V).ι q).app N ≪≫
    (Scheme.Modules.pullbackCongr hfact).app N ≪≫
    ((Scheme.Modules.pullbackComp (q ∣_ V) V.ι).app N).symm ≪≫
    (Scheme.Modules.pullback (q ∣_ V)).mapIso eN ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (q ∣_ V)
