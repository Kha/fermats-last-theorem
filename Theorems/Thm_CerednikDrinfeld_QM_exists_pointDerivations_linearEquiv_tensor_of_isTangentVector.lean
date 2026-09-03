import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_exists_pointDerivations_linearEquiv_tensor_of_isTangentVector
attribute [-instance] AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
attribute [-simp] AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Scheme.TwoAffineOpenCover

theorem CerednikDrinfeld.QM.exists_pointDerivations_linearEquiv_tensor_of_isTangentVector
    (κ : Type) [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ)) [LocallyOfFiniteType fX]
    (L : RelativeGroupLaw κ fX)
    (U : X.Opens) (hU : IsAffineOpen U)
    (e₁ : Spec (CommRingCat.of κ) ⟶ (U : Scheme.{0})) (he₁ : e₁ ≫ U.ι = (L.one (𝟙 _)).1)

    (V : Type) [AddCommGroup V] [Module κ V]
    (τ : V → SchemeHomOver (tangentBase κ (RingHom.id κ)) fX)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase κ (RingHom.id κ)) fX, P ∈ Set.range τ ↔ IsTangentVector L κ (RingHom.id κ) P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase κ (RingHom.id κ)) (τ v) (τ w))
    (hsmul : ∀ (c : κ) (v : V), (τ (c • v)).1 = tangentScale κ c ≫ (τ v).1) :
    letI := algebraOfHom fX U
    ∃ Φ : ∀ (M : Type) [AddCommGroup M] [Module κ M],
        ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) M) ≃ₗ[κ]
          (V ⊗[κ] M),

      (∀ (M M' : Type) [AddCommGroup M] [Module κ M] [AddCommGroup M'] [Module κ M'] (g : M →ₗ[κ] M')
          (δ : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) M)),
        Φ M' (Algebra.PointDerivations.map _ g δ) = TensorProduct.map (LinearMap.id : V →ₗ[κ] V) g (Φ M δ)) ∧

      (∀ (δ : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) κ))
          (χ : Γ(X, U) →+* DualNumber κ),
        (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
        (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ a) = (δ : Γ(X, U) →ₗ[κ] κ) a) →
        (τ (TensorProduct.rid κ V (Φ κ δ))).1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_exists_pointDerivations_linearEquiv_tensor_of_isTangentVector.solution
