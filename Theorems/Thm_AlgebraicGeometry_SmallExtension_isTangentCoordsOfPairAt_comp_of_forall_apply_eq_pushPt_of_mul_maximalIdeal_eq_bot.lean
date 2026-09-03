import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct
  AlgebraicGeometry.SmallExtension CerednikDrinfeld.QM Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot
    (T' : Type u) [CommRing T'] [IsLocalRing T'] (I : Ideal T')

    (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)

    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T')

    (C : Type u) [CommRing C] [Algebra T' C]
    {U Y Y' : Scheme.{u}} (z : U ⟶ Y) (z' : U ⟶ Y') (u v : Spec (CommRingCat.of C) ⟶ U)

    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)

    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (ak : Ak ⟶ Y) (ak' : Ak ⟶ Y')

    (W : Type u) [AddCommGroup W] [Module (ResidueField T') W]
    (τW : W → SchemeHomOver (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) xk)
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) xk, P ∈ Set.range τW ↔ IsTangentVector Lk (ResidueField T') (RingHom.id (ResidueField T')) P)
    (hWadd : ∀ v w : W, τW (v + w) = Lk.mul (tangentBase (ResidueField T') (RingHom.id (ResidueField T'))) (τW v) (τW w))
    (hWsmul : ∀ (a : (ResidueField T')) (v : W), (τW (a • v)).1 = tangentScale (ResidueField T') a ≫ (τW v).1)

    (Φ : letI := algebraOfHom xk Ue
      ∀ (M : Type u) [AddCommGroup M] [Module (ResidueField T') M], ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M) ≃ₗ[(ResidueField T')] (W ⊗[(ResidueField T')] M))
    (hΦnat : letI := algebraOfHom xk Ue
      ∀ (M M' : Type u) [AddCommGroup M] [Module (ResidueField T') M] [AddCommGroup M'] [Module (ResidueField T') M'] (g : M →ₗ[(ResidueField T')] M') (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) M)),
        Φ M' (Algebra.PointDerivations.map ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) g δ) = TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField T')] W) g (Φ M δ))
    (hΦpin : letI := algebraOfHom xk Ue
      ∀ (δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) (ResidueField T'))) (χ : Γ(Ak, Ue) →+* DualNumber (ResidueField T')),
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.fst (χ a) = ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) a) →
        (∀ a : Γ(Ak, Ue), TrivSqZeroExt.snd (χ a) = (δ : Γ(Ak, Ue) →ₗ[(ResidueField T')] (ResidueField T')) a) →
        (τW (TensorProduct.rid (ResidueField T') W (Φ (ResidueField T') δ))).1 = Spec.map (CommRingCat.ofHom χ) ≫ hUe.fromSpec)

    (ψ : Ak ⟶ Ak) (hψ : ψ ≫ xk = xk)
    (hψhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of (ResidueField T'))) (P Q : SchemeHomOver t xk),
      pushPt ψ hψ (Lk.mul t P Q) = Lk.mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))
    (θψ : W →ₗ[(ResidueField T')] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w))

    (hzψ : ∀ {S : Scheme.{u}} (g : S ⟶ U) (gk : S ⟶ Ak), g ≫ z = gk ≫ ak → g ≫ z' = gk ≫ ψ ≫ ak')

    (δ : letI := algebraOfHom xk Ue
      ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue) ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom) (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C))))
    (hδ : letI := algebraOfHom xk Ue
      IsTangentCoordsOfPairAt I V ι C (u ≫ z) (v ≫ z) xk Lk ak Ue (fun a => δ.1 a)) :
    letI := algebraOfHom xk Ue
    IsTangentCoordsOfPairAt I V ι C (u ≫ z') (v ≫ z') xk Lk ak' Ue
      (fun a => ((Φ (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C)) →ₗ[(ResidueField T')] (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C))) (Φ (Module.Dual (ResidueField T') V →ₗ[(ResidueField T')] ((ResidueField T') ⊗[T'] C)) δ))).1 a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot.solution
