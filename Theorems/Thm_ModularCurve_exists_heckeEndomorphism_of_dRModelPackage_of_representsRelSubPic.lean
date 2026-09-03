import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroToricTorsion
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_GaloisRep_Flat
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic
attribute [-instance] instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X
attribute [-simp] ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  AlgebraicGeometry.RelPicard
theorem ModularCurve.exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (D : RelativePic0Designation ℤ (DRModel.toBase p))
    (hD : RepresentsRelSubPic (DRModel.toBase p) 𝔛.εinf (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf) D)

    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hconn : GeometricallyConnected D.toBase)

    (hcomm : (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).IsCommutative)
    (hlft : LocallyOfFiniteType D.toBase)
    (hpre : ∀ s : Spec (CommRingCat.of ℤ), _root_.IsPreconnected (D.toBase.base ⁻¹' {s}))
    (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) D.toBase)
    (pts_add : ∀ x y : JZero p, pts (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul _ (pts x) (pts y))

    (hnflat : ∀ n : ℕ, 0 < n → Flat
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).schemeNsmul n))
    (hnsurj : ∀ n : ℕ, 0 < n → Surjective
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).schemeNsmul n))

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hvi : ∀ m : ℕ, ¬ p ∣ m →
      {x : JZero p | x ∈ jZeroTorsion p m ∧
          ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥A))) D.toBase,
            (pts x).1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1}
        = (jZeroToricTorsion p A m : Set (JZero p)))
    (hptors : ∀ ζ : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ D.P,
      ζ ≫ D.toBase = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (algebraMap ℤ ↥A))) →
      ∃ m : ℕ, 0 < m ∧ ¬ p ∣ m ∧
        ζ ≫ (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).schemeNsmul m =
          ζ ≫ D.toBase ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).one (𝟙 _)).1)

    (hR1 : ∀ {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
      {G H : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of R)) (h : H ⟶ Spec (CommRingCat.of R))
      [IsIntegral G] [LocallyOfFiniteType g] [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (η : G) (_hη : g.base η = IsLocalRing.closedPoint R)
      (_hirr : ∀ x : G, g.base x = IsLocalRing.closedPoint R → η ⤳ x)
      [IsDiscreteValuationRing (G.presheaf.stalk η)]
      (φK : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ pullback h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (hφK : φK ≫ pullback.snd h _ = pullback.snd g _)
      (Dset : Set G) (_hD : ∀ z ∈ Dset, g.base z = IsLocalRing.closedPoint R) (_hDη : η ∈ closure Dset)
      (_hpts : ∀ z ∈ Dset, ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A)
      (c : Spec (CommRingCat.of A) ⟶ pullback g h),
      (c ≫ pullback.fst g h).base (IsLocalRing.closedPoint A) = z ∧
      c.base ⟨⊥, Ideal.isPrime_bot⟩ ∈ Set.range
      (pullback.lift (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))
      (by rw [pullback.condition, Category.assoc, ← hφK, Category.assoc, pullback.condition])).base),
      ∃ (V : G.Opens) (v : (V : Scheme.{0}) ⟶ H),
      v ≫ h = V.ι ≫ g ∧ (∀ x : G, g.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧ η ∈ V ∧
      ∃ hle : Set.range (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))).base ⊆ Set.range V.ι.base,
      IsOpenImmersion.lift V.ι (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) hle ≫ v =
      φK ≫ pullback.fst h (Spec.map (CommRingCat.ofHom (algebraMap R K))))

    (hC1 : letI := heckeModuleBar p
      ∀ t : HeckeAlg,
      ∃ φη : SchemeHomOver
          (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
          (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ))
            (x y : SchemeHomOver s (pullback.snd D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))),
          NeronModelInfra.schemeHomOverComp
              (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).baseChange
                  (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s x y) φη =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).baseChange
                (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη)) ∧
        (∀ (x : JZero p)
            (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
              pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
          z ≫ pullback.fst D.toBase _ = (pts x).1 → zt ≫ pullback.fst D.toBase _ = (pts (t • x)).1 → zt = z ≫ φη.1))

    (hC2 : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ p →
      ∀ φη : SchemeHomOver
          (pullback.snd D.toBase (specGenericFibreInclusion ℤ ℚ))
          (pullback.snd D.toBase (specGenericFibreInclusion ℤ ℚ)),
      ∃ gA : pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ⟶ D.P,
        gA ≫ D.toBase = pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) ≫ D.toBase ∧
        ∀ j : pullback D.toBase (specGenericFibreInclusion ℤ ℚ) ⟶
              pullback D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))),
          j ≫ pullback.fst D.toBase (Spec.map (CommRingCat.ofHom (algebraMap ℤ ↥(GaloisRep.ratLocalizedAt ℓ)))) =
            pullback.fst D.toBase (specGenericFibreInclusion ℤ ℚ) →
          j ≫ gA = φη.1 ≫ pullback.fst D.toBase (specGenericFibreInclusion ℤ ℚ)) :

    letI := heckeModuleBar p
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf) hD).mul s
            (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_heckeEndomorphism_of_dRModelPackage_of_representsRelSubPic.solution
