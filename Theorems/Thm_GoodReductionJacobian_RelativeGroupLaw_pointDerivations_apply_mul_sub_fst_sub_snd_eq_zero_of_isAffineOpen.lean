import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen
attribute [-instance] AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
attribute [-simp] AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Scheme.TwoAffineOpenCover

universe u
theorem GoodReductionJacobian.RelativeGroupLaw.pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (Ue : A.Opens) (hUe : IsAffineOpen Ue)
    (U' : (pullback f f).Opens) (hU' : IsAffineOpen U')
    (hU₁ : U' ≤ pullback.fst f f ⁻¹ᵁ Ue) (hU₂ : U' ≤ pullback.snd f f ⁻¹ᵁ Ue)
    (hUμ : U' ≤ (L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1 ⁻¹ᵁ Ue)
    (eP : Spec (CommRingCat.of k) ⟶ (U' : Scheme.{u}))
    (heP₁ : eP ≫ U'.ι ≫ pullback.fst f f = (L.one (𝟙 _)).1) (heP₂ : eP ≫ U'.ι ≫ pullback.snd f f = (L.one (𝟙 _)).1)
    (M : Type u) [AddCommGroup M] [Module k M]
    (D : letI := algebraOfHom (pullback.fst f f ≫ f) U'
      ↥(Algebra.PointDerivations k Γ(pullback f f, U')
          ((U'.topIso.inv ≫ eP.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom) M))
    (a : Γ(A, Ue)) :
    D.1 (((pullback f f).presheaf.map (homOfLE hUμ).op).hom
            (((L.mul (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩ ⟨pullback.snd f f, pullback.condition.symm⟩).1.app Ue).hom a) -
          ((pullback f f).presheaf.map (homOfLE hU₁).op).hom (((pullback.fst f f).app Ue).hom a) -
          ((pullback f f).presheaf.map (homOfLE hU₂).op).hom (((pullback.snd f f).app Ue).hom a)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_pointDerivations_apply_mul_sub_fst_sub_snd_eq_zero_of_isAffineOpen.solution
