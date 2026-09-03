import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_forall_apply_row_localLevelOne_eq_zero_and_eq_apply_zero_of_isLocallyConstant_of_hasCompactSupport

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.exists_forall_apply_row_localLevelOne_eq_zero_and_eq_apply_zero_of_isLocallyConstant_of_hasCompactSupport
    (p : HeightOneSpectrum (𝓞 ℚ))
    (Φ₂ : p.adicCompletion ℚ × p.adicCompletion ℚ → ℂ) (hΦ₂ : IsLocallyConstant Φ₂ ∧ HasCompactSupport Φ₂)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ∃ (nlo nhi : ℤ), nlo ≤ nhi ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ n : ℤ,
        (n < nlo →
          Φ₂ ((algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ n * ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0),
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ n * ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) = 0) ∧
        (nhi ≤ n →
          Φ₂ ((algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ n * ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0),
              (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) ^ n * ((k : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1)) = Φ₂ (0, 0)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_apply_row_localLevelOne_eq_zero_and_eq_apply_zero_of_isLocallyConstant_of_hasCompactSupport.solution
