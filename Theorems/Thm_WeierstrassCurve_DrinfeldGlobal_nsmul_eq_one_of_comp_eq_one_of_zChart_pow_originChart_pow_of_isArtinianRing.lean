import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing
attribute [-instance] WeierstrassCurve.instIsCommFormalGroup
attribute [-simp] MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq WeierstrassCurve.wIter_zero FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel open WeierstrassCurve.DrinfeldGlobal hiding nsmul_eq_one_of_comp_originChartIota_of_pow_eq_zero_of_isAdicComplete
attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing
    (A : Type) [CommRing A] (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (q : ℕ) [Fact q.Prime]
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra A T] [CharP T q]
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (hΔq : IsUnit (W.map (frobenius T q)).Δ)
    (Φ : projModelCR W.toProjective ⟶ projModelCR (W.map (frobenius T q)).toProjective)
    (hΦ : Φ ≫ projModelStrCR (W.map (frobenius T q)).toProjective = projModelStrCR W.toProjective)
    (hZ : ∃ ψ : ZChartRing (W.map (frobenius T q)).toProjective →+* ZChartRing W.toProjective,
        ψ (xOverZ (W.map (frobenius T q)).toProjective) = xOverZ W.toProjective ^ q ∧
        ψ (yOverZ (W.map (frobenius T q)).toProjective) = yOverZ W.toProjective ^ q ∧
        zChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ zChartι (W.map (frobenius T q)).toProjective)
    (hY : ∃ ψ : OriginChartRing (W.map (frobenius T q)).toProjective →+* OriginChartRing W.toProjective,
        ψ (xOverY (W.map (frobenius T q)).toProjective) = xOverY W.toProjective ^ q ∧
        ψ (zOverY (W.map (frobenius T q)).toProjective) = zOverY W.toProjective ^ q ∧
        originChartι W.toProjective ≫ Φ = Spec.map (CommRingCat.ofHom ψ) ≫ originChartι (W.map (frobenius T q)).toProjective)
    [IsFinite Φ]
    (B : Type) [CommRing B] [IsArtinianRing B] [IsLocalRing B] (ρ : T →+* B)
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (projModelStrCR W.toProjective))
    (hx : (⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (projModelStrCR (W.map (frobenius T q)).toProjective)) =
      (𝒢 T (W.map (frobenius T q)) hΔq).one _) :
    (𝒢 T W hΔ).nsmul _ q x = (𝒢 T W hΔ).one _ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing.solution
