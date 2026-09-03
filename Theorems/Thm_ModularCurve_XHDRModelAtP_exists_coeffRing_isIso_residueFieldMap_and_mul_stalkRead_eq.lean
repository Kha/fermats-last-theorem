import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_XHDRModelAtP_exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq
attribute [-instance] GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA MvPolynomial.CrossingQuotient.Resolution.instIsAffineXSchemeOpenCover MvPolynomial.CrossingQuotient.isOpenImmersion_overlapToChartRight MvPolynomial.CrossingQuotient.isOpenImmersion_torusToOverlap MvPolynomial.CrossingQuotient.isLocallyDirected_glueDiagram MvPolynomial.CrossingQuotient.GlueIndex.instPreorder MvPolynomial.CrossingQuotient.isOpenImmersion_torusToChart MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ιTorus MvPolynomial.CrossingQuotient.isOpenImmersion_glueMap MvPolynomial.CrossingQuotient.GlueIndex.instLE MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ιOverlap MvPolynomial.CrossingQuotient.isLocalization_away_torusRing MvPolynomial.CrossingQuotient.isOpenImmersion_glueDiagram_map MvPolynomial.CrossingQuotient.Resolution.isOpenImmersion_ι
attribute [-simp] WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ MvPolynomial.CrossingQuotient.GlueIndex.chart_le_overlap MvPolynomial.CrossingQuotient.GlueIndex.torus.sizeOf_spec MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_torus MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_chart MvPolynomial.CrossingQuotient.GlueIndex.overlap.sizeOf_spec MvPolynomial.CrossingQuotient.Resolution.ι_toSpec MvPolynomial.CrossingQuotient.Resolution.ι_toCrossing_assoc MvPolynomial.CrossingQuotient.glueMap_torus_overlap MvPolynomial.CrossingQuotient.GlueIndex.chart_le_torus MvPolynomial.CrossingQuotient.glueMap_overlap_overlap MvPolynomial.CrossingQuotient.GlueIndex.torus_le MvPolynomial.CrossingQuotient.Resolution.openCover_f MvPolynomial.CrossingQuotient.Resolution.ι_toCrossing MvPolynomial.CrossingQuotient.glueMap_torus_chart MvPolynomial.CrossingQuotient.glueMap_torus_torus MvPolynomial.CrossingQuotient.glueDiagram_obj MvPolynomial.CrossingQuotient.GlueIndex.chart.injEq MvPolynomial.CrossingQuotient.GlueIndex.chart_le_chart MvPolynomial.CrossingQuotient.GlueIndex.chart.sizeOf_spec MvPolynomial.CrossingQuotient.Resolution.openCover_X MvPolynomial.CrossingQuotient.Resolution.openCover_I₀ MvPolynomial.CrossingQuotient.GlueIndex.overlap.injEq
attribute [-simp] MvPolynomial.CrossingQuotient.glueMap_chart_chart MvPolynomial.CrossingQuotient.GlueIndex.overlap_le_overlap MvPolynomial.CrossingQuotient.Resolution.ι_toSpec_assoc MvPolynomial.CrossingQuotient.lift_V MvPolynomial.CrossingQuotient.lift_U MvPolynomial.CrossingQuotient.monomial_neg_natCast MvPolynomial.CrossingQuotient.monomial_zero MvPolynomial.CrossingQuotient.monomial_natCast MvPolynomial.CrossingQuotient.powMap_mk_X AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    :
    ∀ f : ↥(xHFunctionFieldBar M H),
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (ρO' : R p →+* O')
        (ιA' : O' →+* ↥A) (_ : Function.Injective ιA') (_ : IsLocalHom ιA') (_ : ιA'.comp ρO' = ρ)
        (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp ρO' = algebraMap (R p) (AlgebraicClosure ℚ)) (_ : A.subtype.comp ιA' = jO')
        (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp ρO' = (IsLocalRing.residue ↥A).comp ρ),
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ' : XQ ⟶ XO (ΓM M H) hj ρO' :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI bc' := bcMap (ΓM M H) hj ρO' ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI x' : ↥(XO (ΓM M H) hj ρO') := bc'.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    letI B := (XO (ΓM M H) hj ρO').presheaf.stalk x'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj ρO').presheaf.germ ⊤ x' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj ρO').appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
      ∃ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x'),
      letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρO').presheaf.stalkSpecializes hsp).hom))
      (XO.toBase (ΓM M H) hj ρO').base x' = IsLocalRing.closedPoint O' ∧
      IsIso ((XO.toBase (ΓM M H) hj ρO').residueFieldMap x') ∧
      ∃ r s₀ : ↥B, s₀ ≠ 0 ∧ f * emb s₀ = emb r := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XHDRModelAtP_exists_coeffRing_isIso_residueFieldMap_and_mul_stalkRead_eq.solution
