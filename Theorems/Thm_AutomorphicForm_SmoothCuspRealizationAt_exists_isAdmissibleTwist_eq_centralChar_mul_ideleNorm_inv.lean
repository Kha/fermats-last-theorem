import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import P2M.Util
import P2M.Sol.S_AutomorphicForm_SmoothCuspRealizationAt_exists_isAdmissibleTwist_eq_centralChar_mul_ideleNorm_inv
attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open scoped nonZeroDivisors

theorem AutomorphicForm.SmoothCuspRealizationAt.exists_isAdmissibleTwist_eq_centralChar_mul_ideleNorm_inv
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral R)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ‖Φ.b p‖ = 1) :
    ∃ η₀ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      IsAdmissibleTwist ℚ η₀ ∧
      IsAdmissibleTwist K (η₀.comp (M4aHerbrand.GenuineDescent.genuineBaseChange ℚ K).idelicNorm) ∧
      ∀ z : (productionPinsGeneral ℚ).Z,
        ((η₀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℂˣ) : ℂ) =
          ((R.centralChar z : ℂˣ) : ℂ) * ((NumberField.TateGlobal.ideleNorm ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : ℝ) : ℂ)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_exists_isAdmissibleTwist_eq_centralChar_mul_ideleNorm_inv.solution
