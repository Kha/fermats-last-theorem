import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing
import P2M.Util
namespace P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_schemeNsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow
attribute [-instance] WeierstrassCurve.instIsCommFormalGroup
attribute [-simp] MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq WeierstrassCurve.wIter_zero FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq WeierstrassProjModel.kw_lrThird_substHom_X

set_option autoImplicit false
p2m_open "AlgebraicGeometry CategoryTheory NeronModelInfra WeierstrassProjModel P2MW.S_WeierstrassCurve_DrinfeldGlobal_comp_schemeNsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow.WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal"
attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory.Limits

namespace WeierstrassProjModel
p2m_export "WeierstrassProjModel" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.idPoint projModelCR projModelStrCR"
namespace RelativeGroupLaw
p2m_export "WeierstrassProjModel.RelativeGroupLaw" "nsmul one_natural nsmul_natural idPoint schemeNsmul schemeNsmul_over one"
namespace FrobKerKilledAux
p2m_open "WeierstrassProjModel.RelativeGroupLaw WeierstrassProjModel"

universe u

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f)

theorem one_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G.one t).1 = t ≫ (G.one (𝟙 _)).1 := by
  have h := G.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← h, schemeHomOverComp_coe]

theorem nsmul_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h, schemeHomOverComp_coe]
  rfl

end WeierstrassProjModel.RelativeGroupLaw.FrobKerKilledAux

open WeierstrassProjModel.RelativeGroupLaw.FrobKerKilledAux in

theorem solution
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
    {S : Scheme} (t : S ⟶ Spec (CommRingCat.of T)) (x : SchemeHomOver t (projModelStrCR W.toProjective))
    (hx : (⟨x.1 ≫ Φ, by rw [Category.assoc, hΦ]; exact x.2⟩ : SchemeHomOver t (projModelStrCR (W.map (frobenius T q)).toProjective)) =
      (𝒢 T (W.map (frobenius T q)) hΔq).one t) :
    (⟨x.1 ≫ (𝒢 T W hΔ).schemeNsmul q, by rw [Category.assoc, (𝒢 T W hΔ).schemeNsmul_over]; exact x.2⟩ :
        SchemeHomOver t (projModelStrCR W.toProjective)) = (𝒢 T W hΔ).one t := by

  have hx1 : x.1 ≫ Φ = t ≫ ((𝒢 T (W.map (frobenius T q)) hΔq).one (𝟙 _)).1 := by
    have h := congrArg Subtype.val hx
    rw [one_coe (𝒢 T (W.map (frobenius T q)) hΔq) t] at h
    exact h

  have key : pullback.fst Φ ((𝒢 T (W.map (frobenius T q)) hΔq).one (𝟙 _)).1 ≫ (𝒢 T W hΔ).schemeNsmul q =
      pullback.snd Φ ((𝒢 T (W.map (frobenius T q)) hΔq).one (𝟙 _)).1 ≫ ((𝒢 T W hΔ).one (𝟙 _)).1 := by
    apply AlgebraicGeometry.Scheme.Hom.eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing
      (pullback.snd Φ ((𝒢 T (W.map (frobenius T q)) hΔq).one (𝟙 _)).1)
    intro B _ _ _ z
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (z ≫ pullback.snd Φ ((𝒢 T (W.map (frobenius T q)) hΔq).one (𝟙 _)).1)
    have hw : (z ≫ pullback.fst Φ ((𝒢 T (W.map (frobenius T q)) hΔq).one (𝟙 _)).1) ≫ projModelStrCR W.toProjective =
        Spec.map (CommRingCat.ofHom φ.hom) := by
      rw [CommRingCat.ofHom_hom, hφ, ← hΦ, Category.assoc, pullback.condition_assoc,
        ((𝒢 T (W.map (frobenius T q)) hΔq).one (𝟙 _)).2, Category.comp_id]
    have hwx : (⟨(z ≫ pullback.fst Φ ((𝒢 T (W.map (frobenius T q)) hΔq).one (𝟙 _)).1) ≫ Φ, by
          rw [Category.assoc, hΦ]; exact hw⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom φ.hom)) (projModelStrCR (W.map (frobenius T q)).toProjective)) =
        (𝒢 T (W.map (frobenius T q)) hΔq).one _ := by
      apply Subtype.ext
      rw [one_coe (𝒢 T (W.map (frobenius T q)) hΔq) (Spec.map (CommRingCat.ofHom φ.hom))]
      show (z ≫ pullback.fst Φ _) ≫ Φ = Spec.map (CommRingCat.ofHom φ.hom) ≫ _
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← hφ, CommRingCat.ofHom_hom]
    have hloc := WeierstrassCurve.DrinfeldGlobal.nsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow_of_isArtinianRing
      A 𝒢 h𝒢 h𝒢O q T W hΔ hΔq Φ hΦ hZ hY B φ.hom ⟨_, hw⟩ hwx
    have h := congrArg Subtype.val hloc
    rw [nsmul_coe, one_coe (𝒢 T W hΔ) (Spec.map (CommRingCat.ofHom φ.hom))] at h
    change (z ≫ pullback.fst Φ _) ≫ (𝒢 T W hΔ).schemeNsmul q = Spec.map (CommRingCat.ofHom φ.hom) ≫ _ at h
    rw [Category.assoc, CommRingCat.ofHom_hom, hφ, Category.assoc] at h
    exact h

  apply Subtype.ext
  rw [one_coe (𝒢 T W hΔ) t]
  show x.1 ≫ (𝒢 T W hΔ).schemeNsmul q = t ≫ ((𝒢 T W hΔ).one (𝟙 _)).1
  rw [← pullback.lift_fst x.1 t hx1, Category.assoc, key, ← Category.assoc, pullback.lift_snd]
