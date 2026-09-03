import Definitions.Def_AlgebraicGeometry_PolarisationRosati

import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_tensor_cube_pullback_inv_of_iso

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

namespace G2LocIsoCube

variable {S : Type u} [CommRing S]

theorem locIso_of_iso {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of S)) {M M' : X.Modules} (i : M ≅ M') :
    LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso i⟩⟩

noncomputable def pullbackInvHomIso {A A' : Scheme.{u}} (e : A ≅ A') (P' : A'.Modules) :
    (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj P') ≅ P' :=
  (Scheme.Modules.pullbackComp e.inv e.hom).app P' ≪≫ (Scheme.Modules.pullbackCongr e.inv_hom_id).app P' ≪≫
    (Scheme.Modules.pullbackId A').app P'

noncomputable def pullbackCubeIso {A A' : Scheme.{u}} (h : A' ⟶ A) (M : A.Modules) :
    (Scheme.Modules.pullback h).obj (M ⊗ M ⊗ M) ≅
      (Scheme.Modules.pullback h).obj M ⊗ (Scheme.Modules.pullback h).obj M ⊗ (Scheme.Modules.pullback h).obj M :=
  Scheme.Modules.pullbackTensorObjIso h M (M ⊗ M) ≪≫
    whiskerLeftIso ((Scheme.Modules.pullback h).obj M) (Scheme.Modules.pullbackTensorObjIso h M M)

end G2LocIsoCube

open G2LocIsoCube in
theorem solution
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}
    (e : A ≅ A') (he : e.hom ≫ f' = f) (P M : A.Modules) (P' : A'.Modules)
    (hP : LocIsoOnBase f P (M ⊗ M ⊗ M))
    (hPP' : LocIsoOnBase f ((Scheme.Modules.pullback e.hom).obj P') P) :
    LocIsoOnBase f' P'
      ((Scheme.Modules.pullback e.inv).obj M ⊗ (Scheme.Modules.pullback e.inv).obj M ⊗ (Scheme.Modules.pullback e.inv).obj M) := by
  have E := LocIsoOnBase.equivalence f'

  have h1 : LocIsoOnBase f ((Scheme.Modules.pullback e.hom).obj P') (M ⊗ M ⊗ M) :=
    (LocIsoOnBase.equivalence f).trans hPP' hP
  have hcomm : e.inv ≫ f = f' ≫ 𝟙 (Spec (CommRingCat.of S)) := by
    rw [Category.comp_id, ← he, Iso.inv_hom_id_assoc]
  have h2 := LocIsoOnBase.pullback_of_comp_eq f' e.inv (𝟙 _) hcomm h1

  exact E.trans (E.trans (E.symm (locIso_of_iso f' (pullbackInvHomIso e P'))) h2) (locIso_of_iso f' (pullbackCubeIso e.inv M))
