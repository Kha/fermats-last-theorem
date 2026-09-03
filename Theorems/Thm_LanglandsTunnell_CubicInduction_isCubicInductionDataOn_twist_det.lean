import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_isCubicInductionDataOn_twist_det
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions
attribute [-simp] LanglandsTunnell.CubicInduction.fnTwist3_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent LanglandsTunnell.CubicInduction.longWeyl3_coe LanglandsTunnell.CubicInduction.lowerUnipotent21_coe LanglandsTunnell.CubicInduction.weylPrime3_coe UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal open LanglandsTunnell.CubicInduction hiding hasSphericalTorusValuesAt_twist_det_of_isUnramifiedCharAt inducedLevelAt_twist_eq_of_isUnramifiedCharAt mem_gl3CyclicSubspace_twist_det twist_det_localPackage open MeasureTheory

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.isCubicInductionDataOn_twist_det
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (pins : AutomorphicForm.CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hν : LanglandsTunnell.Converse.IsAdmissibleTwist K ν)
    (F : CubicInductionForm K pins ψ ν)
    (χA : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχA : LanglandsTunnell.Converse.IsAdmissibleTwist ℚ χA)
    (hχinf : ∀ v : InfinitePlace ℚ, v.IsReal → LanglandsTunnell.Converse.IsArchCompAt ℚ χA v 0 0)
    (S : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hSν : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsBadPlace K ν v → v ∈ S)
    (hSχ : ∀ v : HeightOneSpectrum (𝓞 ℚ), ¬ IsUnramifiedCharAt χA v → v ∈ S) :
    IsCubicInductionDataOn K pins ψ (ν * χA.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) S
      { form := fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.form x
        whittaker := fun x : AdelicGL 3 (𝓞 ℚ) ℚ => ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * F.whittaker x
        whittakerLoc := fun (v : HeightOneSpectrum (𝓞 ℚ)) (y : LocalGL3 v) =>
          ((NumberField.TateGlobal.localChar χA v (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) * F.whittakerLoc v y
        whittakerArch := F.whittakerArch
        centralChar := F.centralChar * χA ^ 3
        dualWhittaker := fun x : AdelicGL 3 (𝓞 ℚ) ℚ =>
          ((χA (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ)⁻¹ * F.dualWhittaker x } := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_isCubicInductionDataOn_twist_det.solution
