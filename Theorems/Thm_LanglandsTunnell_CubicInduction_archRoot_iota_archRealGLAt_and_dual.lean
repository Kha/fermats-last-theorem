import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
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
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_archRoot_iota_archRealGLAt_and_dual

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.CubicInduction.archRoot_iota_archRealGLAt_and_dual (h : GL (Fin 2) ℝ) (w : InfinitePlace ℚ) :
    archRoot₁ ℚ w (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h)) =
        |(Matrix.GeneralLinearGroup.det h : ℝ)| /
          (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) ∧
      archRoot₂ ℚ w (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h)) =
        Real.sqrt (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) ∧
      archRoot₁ ℚ w (longWeyl3 * transposeInv3
          (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h))) =
        Real.sqrt (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) ∧
      archRoot₂ ℚ w (longWeyl3 * transposeInv3
          (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) h))) =
        |(Matrix.GeneralLinearGroup.det h : ℝ)| /
          (((h : Matrix (Fin 2) (Fin 2) ℝ) 1 0) ^ 2 + ((h : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_archRoot_iota_archRealGLAt_and_dual.solution
