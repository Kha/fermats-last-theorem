import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_pullback_squareZero
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_pullback_rigSection_of_squareZero_of_pullback_iso
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 24000000

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {B : Type u} [CommRing B] [Algebra R B] (I : Ideal B) (hI : I ^ 2 = ⊥)
    (ι : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I))))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))))
    (hι : ι.1 = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (M : RigidifiedLineBundle c ε (Spec.map (CommRingCat.ofHom (algebraMap R (B ⧸ I)))))
    (L' : (pullback c (Spec.map (CommRingCat.ofHom (algebraMap R B)))).Modules)
    (hL' : Scheme.Modules.IsInvertible L')
    (isoL : Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ι)).obj L' ≅ M.L)) :
    Nonempty
      ((Scheme.Modules.pullback (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L'
        ≅ SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf) := by
  have hεL'inv : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback
        (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L') :=
    hL'.pullback _

  have step1 :
      (Scheme.Modules.pullback ι.1).obj
        ((Scheme.Modules.pullback
          (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L')
        ≅ SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ I))).ringCatSheaf :=
    (Scheme.Modules.pullbackComp _ _).app L' ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ι).symm).app L' ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L').symm ≪≫
      (Scheme.Modules.pullback _).mapIso isoL.some ≪≫
      M.rigidified.some

  have htriv : Nonempty ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
        ((Scheme.Modules.pullback
          (rigSection c (Spec.map (CommRingCat.ofHom (algebraMap R B))) ε)).obj L')
        ≅ SheafOfModules.unit (Spec (CommRingCat.of (B ⧸ I))).ringCatSheaf) := by
    rw [← hι]; exact ⟨step1⟩
  exact Scheme.Modules.IsInvertible.nonempty_iso_unit_of_pullback_squareZero I hI _ hεL'inv htriv
