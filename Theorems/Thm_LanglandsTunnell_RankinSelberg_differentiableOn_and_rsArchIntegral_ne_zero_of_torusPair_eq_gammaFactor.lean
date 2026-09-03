import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerModelLocal

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_differentiableOn_and_rsArchIntegral_ne_zero_of_torusPair_eq_gammaFactor

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse~exists_const_sum_rsArchIntegral_eq_mul_of_torus_identities~exists_const_rsArchIntegral_eq_mul_integral_diagonal"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.differentiableOn_and_rsArchIntegral_ne_zero_of_torusPair_eq_gammaFactor
    (WA : GL (Fin 2) ℝ → ℂ) (WF : GL (Fin 3) (InfiniteAdeleRing ℚ) → ℂ)
    (_hN : ∀ n ∈ RSCarrier.realUnipotent, ∀ q : GL (Fin 2) ℝ,
      WA (n * q) * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (n * q))))
        = WA q * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q))))
    (_hK : ∀ k ∈ AutomorphicForm.WindowedSiegel.rowIsometrySubgroup ℝ, Matrix.GeneralLinearGroup.det k = 1 → ∀ q : GL (Fin 2) ℝ,
      WA (q * k) * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (q * k))))
        = WA q * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q))))
    (ΓR ΓC : Multiset ℂ) (σa : ℝ) (e : ℂ) (_he : e ≠ 0)
    (_hT : ∀ s : ℂ, σa < s.re →
      (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
        if ha : a₁ ≠ 0 ∧ 0 < a₂ then
          let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
          ((WA q * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
            (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
        else 0)
        = e * ((ΓR.map fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
            (ΓC.map fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod)) :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (_hW : Measurable WA)
      (_hF : Measurable fun g : GL (Fin 2) ℝ => WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g))))
      (_hint : ∀ (μN : Measure RSCarrier.realUnipotent) [μN.IsHaarMeasure], ∃ σI : ℝ,
        ∀ s : ℂ, σI < s.re → MeasureTheory.Integrable
          (fun g : GL (Fin 2) ℝ =>
            (WA g * WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) g)))) *
              (((|(Matrix.GeneralLinearGroup.det g : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2)))
          (RSCarrier.archMeasure.withDensity (HaarQuotient.density RSCarrier.realUnipotent μN))),
    ∀ (μNA : Measure RSCarrier.realUnipotent) [μNA.IsHaarMeasure],
      ∃ (hA : GL (Fin 2) ℝ) (hA3 : GL (Fin 3) (InfiniteAdeleRing ℚ)) (σ : ℝ),
        DifferentiableOn ℂ
            (fun s : ℂ => RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s
              (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA (M * hA)))
              (fun M : GL (Fin 2) ℝ => WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)))
            {s : ℂ | σ < s.re} ∧
        ∃ s : ℂ, σ < s.re ∧
          RSCarrier.rsArchIntegral RSCarrier.archMeasure μNA s
              (fun M : GL (Fin 2) ℝ => ((((|(Matrix.GeneralLinearGroup.det M : ℝ)| : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) * WA (M * hA)))
              (fun M : GL (Fin 2) ℝ => WF (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) M)) * hA3)) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_differentiableOn_and_rsArchIntegral_ne_zero_of_torusPair_eq_gammaFactor.solution
