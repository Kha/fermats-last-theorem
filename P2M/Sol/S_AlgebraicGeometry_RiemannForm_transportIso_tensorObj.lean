import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_app_tensorObj
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RiemannForm_transportIso_tensorObj
attribute [-simp] AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RiemannForm"

namespace MonoTransportTensor

theorem pullbackCongr_app_tensorObj {X Y : Scheme.{0}} {f₁ f₂ : X ⟶ Y} (h : f₁ = f₂) (M N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).app (M ⊗ N) =
      Scheme.Modules.pullbackTensorObjIso f₁ M N ≪≫
        ((Scheme.Modules.pullbackCongr h).app M ⊗ᵢ (Scheme.Modules.pullbackCongr h).app N) ≪≫
        (Scheme.Modules.pullbackTensorObjIso f₂ M N).symm := by
  subst h
  ext
  simp [Scheme.Modules.pullbackCongr]

end MonoTransportTensor

open MonoTransportTensor in
theorem solution
    {A : Scheme.{0}} {T g : A ⟶ A} (h : T ≫ g = g) (M M' : A.Modules) :
    transportIso h (M ⊗ M') =
      (Scheme.Modules.pullback T).mapIso (Scheme.Modules.pullbackTensorObjIso g M M') ≪≫
        Scheme.Modules.pullbackTensorObjIso T ((Scheme.Modules.pullback g).obj M) ((Scheme.Modules.pullback g).obj M') ≪≫
        (transportIso h M ⊗ᵢ transportIso h M') ≪≫
        (Scheme.Modules.pullbackTensorObjIso g M M').symm := by
  unfold transportIso
  rw [Scheme.Modules.pullbackComp_app_tensorObj T g M M', pullbackCongr_app_tensorObj h M M']
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, tensorIso_hom, Category.assoc, Iso.inv_hom_id_assoc,
    tensorHom_comp_tensorHom_assoc]
