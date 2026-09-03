import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_hom

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem GoodReductionJacobian.RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_hom
    {S₁ S₂ : Type} [CommRing S₁] [CommRing S₂] (φ : S₁ →+* S₂)
    {A₁ A₂ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of S₁)} {f₂ : A₂ ⟶ Spec (CommRingCat.of S₂)}
    (L₁ : RelativeGroupLaw S₁ f₁) (L₂ : RelativeGroupLaw S₂ f₂)
    (v : A₂ ⟶ A₁) (hv : v ≫ f₁ = f₂ ≫ Spec.map (CommRingCat.ofHom φ))
    (hom : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S₂)) (P Q : SchemeHomOver t f₂),
      (L₂.mul t P Q).1 ≫ v =
        (L₁.mul (t ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ v, by rw [Category.assoc, hv, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ v, by rw [Category.assoc, hv, ← Category.assoc, Q.2]⟩).1) :
    v ≫ negMor f₁ L₁ = negMor f₂ L₂ ≫ v := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_hom.solution
