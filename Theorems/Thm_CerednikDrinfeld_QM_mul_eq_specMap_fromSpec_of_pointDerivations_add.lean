import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_QM_mul_eq_specMap_fromSpec_of_pointDerivations_add

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Scheme.TwoAffineOpenCover

theorem CerednikDrinfeld.QM.mul_eq_specMap_fromSpec_of_pointDerivations_add
    (κ : Type) [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ))
    (L : RelativeGroupLaw κ fX)
    (U : X.Opens) (hU : IsAffineOpen U)
    (e₁ : Spec (CommRingCat.of κ) ⟶ (U : Scheme.{0})) (he₁ : e₁ ≫ U.ι = (L.one (𝟙 _)).1) :
    letI := algebraOfHom fX U
    ∀ (δ δ' : ↥(Algebra.PointDerivations κ Γ(X, U) ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) κ)) (χ χ' χ'' : Γ(X, U) →+* DualNumber κ),
      (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ a) = (δ : Γ(X, U) →ₗ[κ] κ) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ' a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ' a) = (δ' : Γ(X, U) →ₗ[κ] κ) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.fst (χ'' a) = ((U.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of κ)).hom).hom) a) →
      (∀ a : Γ(X, U), TrivSqZeroExt.snd (χ'' a) = (δ : Γ(X, U) →ₗ[κ] κ) a + (δ' : Γ(X, U) →ₗ[κ] κ) a) →
      ∀ (P P' : SchemeHomOver (tangentBase κ (RingHom.id κ)) fX),
        P.1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec →
        P'.1 = Spec.map (CommRingCat.ofHom χ') ≫ hU.fromSpec →
        (L.mul (tangentBase κ (RingHom.id κ)) P P').1 = Spec.map (CommRingCat.ofHom χ'') ≫ hU.fromSpec := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_QM_mul_eq_specMap_fromSpec_of_pointDerivations_add.solution
