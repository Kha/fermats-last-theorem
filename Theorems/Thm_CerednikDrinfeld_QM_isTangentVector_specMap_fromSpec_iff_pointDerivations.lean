import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_isTangentVector_specMap_fromSpec_iff_pointDerivations
attribute [-instance] AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
attribute [-simp] AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Scheme.TwoAffineOpenCover

theorem CerednikDrinfeld.QM.isTangentVector_specMap_fromSpec_iff_pointDerivations
    (κ : Type) [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ))
    (L : RelativeGroupLaw κ fX)
    (U : X.Opens) (hU : IsAffineOpen U)
    (e₁ : Spec (CommRingCat.of κ) ⟶ (U : Scheme.{0})) (he₁ : e₁ ≫ U.ι = (L.one (𝟙 _)).1) :
    letI := algebraOfHom fX U

    (∀ (δ : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) κ)) (χ : Γ(X, U) →+* DualNumber κ),
        (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
        (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ a) = (δ : Γ(X, U) →ₗ[κ] κ) a) →
        ∃ h : (Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec) ≫ fX = tangentBase κ (RingHom.id κ),
          IsTangentVector L κ (RingHom.id κ) ⟨Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec, h⟩) ∧

    (∀ P : SchemeHomOver (tangentBase κ (RingHom.id κ)) fX, IsTangentVector L κ (RingHom.id κ) P →
        ∃ (δ : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) κ)) (χ : Γ(X, U) →+* DualNumber κ),
          (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) ∧
          (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ a) = (δ : Γ(X, U) →ₗ[κ] κ) a) ∧
          P.1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec) ∧

    (∀ χ χ' : Γ(X, U) →+* DualNumber κ,
        Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom χ') ≫ hU.fromSpec → χ = χ') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_isTangentVector_specMap_fromSpec_iff_pointDerivations.solution
