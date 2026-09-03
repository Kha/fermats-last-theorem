import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicLambda
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_HeckeTate_finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp
attribute [-instance] instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open LanglandsTunnell.Converse LanglandsTunnell.HeckeTate LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicLambda
open LanglandsTunnell.CubicInduction Polynomial

theorem LanglandsTunnell.HeckeTate.finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hτ : IsUnramifiedCharAt τ p) :
    (∏ᶠ 𝔓 ∈ primeFibre ℚ K p,
        ((heckeDatum K (μ * τ.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm)
            uR aR uC kC).euler 𝔓).comp (X ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal)))
      = (inducedEulerPoly ℚ (inducedCoeff K μ) p).comp (C (eulerCoeff ℚ τ p) * X) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_HeckeTate_finprod_euler_comp_X_pow_inertiaDeg_eq_inducedEulerPoly_comp.solution
