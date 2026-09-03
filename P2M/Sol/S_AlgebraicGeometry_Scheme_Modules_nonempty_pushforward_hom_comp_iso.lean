import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace PushIso

variable {X Y : Scheme.{u}} (φ : X ≅ Y)

noncomputable def pushEquiv : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward φ.hom) (Scheme.Modules.pushforward φ.inv)
    ((Scheme.Modules.pushforwardId X).symm ≪≫ Scheme.Modules.pushforwardCongr φ.hom_inv_id.symm ≪≫
      (Scheme.Modules.pushforwardComp φ.hom φ.inv).symm)
    (Scheme.Modules.pushforwardComp φ.inv φ.hom ≪≫ Scheme.Modules.pushforwardCongr φ.inv_hom_id ≪≫
      Scheme.Modules.pushforwardId Y)

noncomputable def pullbackIsoPushforwardInv :
    Scheme.Modules.pullback φ.hom ≅ Scheme.Modules.pushforward φ.inv :=
  (Scheme.Modules.pullbackPushforwardAdjunction φ.hom).leftAdjointUniq (pushEquiv φ).symm.toAdjunction

end PushIso

theorem solution
    {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z) (F : X.Modules) :
    Nonempty ((Scheme.Modules.pushforward (e.hom ≫ f)).obj F ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback e.inv).obj F)) :=
  ⟨(Scheme.Modules.pushforwardComp e.hom f).symm.app F ≪≫
    (Scheme.Modules.pushforward f).mapIso ((PushIso.pullbackIsoPushforwardInv e.symm).app F).symm⟩
