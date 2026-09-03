import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_exists_iso_of_twoAffineLineCover
attribute [-instance] AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation
attribute [-simp] AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve Polynomial

theorem AlgebraicCurve.CurveModel.exists_iso_of_twoAffineLineCover
    (κ : Type u) [Field κ] [IsAlgClosed κ] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of κ))
    (i₀ i₁ : Spec (CommRingCat.of (Polynomial κ)) ⟶ Z) [IsOpenImmersion i₀] [IsOpenImmersion i₁]
    (hi₀ : i₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap κ (Polynomial κ))))
    (hi₁ : i₁ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap κ (Polynomial κ))))
    (hcov : Set.range i₀.base ∪ Set.range i₁.base = Set.univ)
    (hglue : Spec.map (CommRingCat.ofHom (algebraMap (Polynomial κ) (Localization.Away (X : Polynomial κ)))) ≫ i₀ =
      Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := κ)
        (IsLocalization.Away.invSelf (S := Localization.Away (X : Polynomial κ)) (X : Polynomial κ))).toRingHom) ≫ i₁)
    (hmeet : Set.range i₀.base ∩ Set.range i₁.base ⊆
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial κ) (Localization.Away (X : Polynomial κ)))) ≫ i₀).base) :
    ∃ (M : CurveModel κ (RatFunc κ)) (e : M.C ≅ Z), e.hom ≫ z = M.toBase := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_exists_iso_of_twoAffineLineCover.solution
