import Definitions.Def_ModularCurve_ProlongationTuple
import P2M.Util
import P2M.Sol.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top
attribute [-instance] ValuationSubring.instIsAlgClosedResidueField ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.exists_orderSubalgebra_finite_span_eq_top
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hqN : ¬ q ∣ N) (hred : Function.Surjective red) :
    letI : Algebra
        ↥((CharPReduction.modularLocalized N A.toSubring red).comap
          (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))))
        ↥(modularFunctionFieldBar (N * q)) :=
      ((heckeAlphaBar (AlgebraicClosure ℚ) N q).toRingHom.comp
        ((CharPReduction.modularLocalized N A.toSubring red).comap
          (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ)))).subtype).toAlgebra
    ∃ S : Subalgebra
        ↥((CharPReduction.modularLocalized N A.toSubring red).comap
          (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))))
        ↥(modularFunctionFieldBar (N * q)),
      (∀ g : modularFunctionFieldBar (N * q), g ∈ S ↔
        (g : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (N * q) A.toSubring red ∧
          ((atkinLehnerBar N q g : modularFunctionFieldBar (N * q)) :
              LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (N * q) A.toSubring red) ∧
      (∀ v : modularFunctionFieldBar N,
        (v : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized N A.toSubring red →
          heckeAlphaBar (AlgebraicClosure ℚ) N q v ∈ S) ∧
      jQFun N q ∈ S ∧
      (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (N * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (N * q) dvd_rfl)⟩ :
          modularFunctionFieldBar (N * q)) ∈ S ∧
      Module.Finite
        ↥((CharPReduction.modularLocalized N A.toSubring red).comap
          (algebraMap ↥(modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ)))) ↥S ∧
      (letI := AlgebraicCurve.algebraAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q)
       Submodule.span (modularFunctionFieldBar N) (S : Set (modularFunctionFieldBar (N * q))) = ⊤) ∧
      (∀ a b : modularFunctionFieldC k N, ∃ s ∈ S,
        ∃ (h₁ : (s : LaurentSeries (AlgebraicClosure ℚ))
              ∈ CharPReduction.modularLocalized (N * q) A.toSubring red)
          (h₂ : ((atkinLehnerBar N q s : modularFunctionFieldBar (N * q)) :
                LaurentSeries (AlgebraicClosure ℚ))
              ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
          CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₁⟩ = (a : LaurentSeries k) ∧
          CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨_, h₂⟩ = (b : LaurentSeries k)) ∧
      (∀ (f : LaurentSeries (AlgebraicClosure ℚ))
          (hfN : f ∈ CharPReduction.modularLocalized N A.toSubring red)
          (hfNq : f ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
        CharPReduction.modularRedLocHom (N * q) A.toSubring red ⟨f, hfNq⟩ =
          CharPReduction.modularRedLocHom N A.toSubring red ⟨f, hfN⟩) ∧
      (∀ (v : modularFunctionFieldBar N)
          (hv : (v : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized N A.toSubring red)
          (hw : ((atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
              modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ))
            ∈ CharPReduction.modularLocalized (N * q) A.toSubring red),
        CharPReduction.modularRedLocHom (N * q) A.toSubring red
            ⟨((atkinLehnerBar N q (heckeAlphaBar (AlgebraicClosure ℚ) N q v) :
                modularFunctionFieldBar (N * q)) : LaurentSeries (AlgebraicClosure ℚ)), hw⟩ =
          qExpand k q (CharPReduction.modularRedLocHom N A.toSubring red
            ⟨(v : LaurentSeries (AlgebraicClosure ℚ)), hv⟩)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_orderSubalgebra_finite_span_eq_top.solution
