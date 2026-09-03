import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_Isogeny_ConditionalCurrency
import Definitions.Def_ModularCurve_X1HeckeModule
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X
attribute [-simp] ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one

set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (ι : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar M))
    (hι : ∀ x : ↥(xHFunctionFieldBar M H), ((ι x : ↥(x1FunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ (w₁ : ↥(x1FunctionFieldBar M) ≃ₐ[AlgebraicClosure ℚ] ↥(x1FunctionFieldBar M))
      (w : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (w' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),

      ((∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
          (hβ : HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hfinβ)
          (x : JOne M),
        heckePic0OneBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w₁ • x)
          = SemilinearAut.ofAlgAut w₁ • heckePic0OneBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : ℕ) (x : JOne M),
        diamondOneBar M d (SemilinearAut.ofAlgAut w₁ • diamondOneBar M d x)
          = SemilinearAut.ofAlgAut w₁ • x) ∧
      (∀ x : JOne M, SemilinearAut.ofAlgAut w₁ • (SemilinearAut.ofAlgAut w₁ • x) = x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ), c.Coprime M →
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) → ∀ x : JOne M,
          SemilinearAut.ofAlgAut w₁ • (σ • x)
            = σ • diamondOneBar M c (SemilinearAut.ofAlgAut w₁ • x))) ∧

      ((∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hfinβ)
          (x : JH M H),
        heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : (ZMod M)ˣ) (x : JH M H),
        diamondHBar M H d (SemilinearAut.ofAlgAut w • diamondHBar M H d x)
          = SemilinearAut.ofAlgAut w • x) ∧
      (∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x : JH M H,
            SemilinearAut.ofAlgAut w • (σ • x)
              = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x))) ∧
      ((∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ)
          (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) ℓ) hfinβ)
          (x : JH (M / p) (infSubgroup p M H hpM)),
        heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w' • x)
          = SemilinearAut.ofAlgAut w' • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : (ZMod (M / p))ˣ) (x : JH (M / p) (infSubgroup p M H hpM)),
        diamondHBar (M / p) (infSubgroup p M H hpM) d (SemilinearAut.ofAlgAut w' • diamondHBar (M / p) (infSubgroup p M H hpM) d x)
          = SemilinearAut.ofAlgAut w' • x) ∧
      (∀ x : JH (M / p) (infSubgroup p M H hpM), SemilinearAut.ofAlgAut w' • (SemilinearAut.ofAlgAut w' • x) = x) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime (M / p)),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ (M / p) = 1 → σ ζ = ζ ^ c) →
          ∀ x : JH (M / p) (infSubgroup p M H hpM),
            SemilinearAut.ofAlgAut w' • (σ • x)
              = σ • diamondHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w' • x))) ∧

      (∀ u : ↥(xHFunctionFieldBar M H), ι (w u) = w₁ (ι u)) ∧

      (∀ (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
          (hα : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
          (hβ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
            ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), ((βH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
          (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
          (hαfin : FiniteAlong (AlgebraicClosure ℚ) αH) (hβfin : FiniteAlong (AlgebraicClosure ℚ) βH)
          (hαN : NormFormulaAlong (AlgebraicClosure ℚ) αH hαfin) (hβN : NormFormulaAlong (AlgebraicClosure ℚ) βH hβfin),
        (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), αH (w' u) = w (βH u)) ∧
          (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), βH (w' u) = w (αH u)) ∧

          (∀ x : JH M H,
        Pic0.pushforwardAlongHom βH hβint hβfin hβN (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w' • Pic0.pushforwardAlongHom αH hαint hαfin hαN x) ∧
          (∀ x : JH M H,
        Pic0.pushforwardAlongHom αH hαint hαfin hαN (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w' • Pic0.pushforwardAlongHom βH hβint hβfin hβN x)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_frickeAlgEquiv_triple_x1_xH_galois_smul_and_apply_inclusion_eq_and_forall_apply_degeneracy_eq.solution
