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
import P2M.Sol.S_AutomorphicForm_WhittakerModel_norm_diagUnits2_mul_le_of_forall_mem_localLevelOne_norm_diagUnits2_mul_le

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem AutomorphicForm.WhittakerModel.norm_diagUnits2_mul_le_of_forall_mem_localLevelOne_norm_diagUnits2_mul_le
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwN : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), ‖w (unipotent x * g)‖ = ‖w g‖)
    (C τ : ℝ) (A : ℕ) (hC : 0 ≤ C)
    (hgauge : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ a₁ a₂ : (p.adicCompletion ℚ)ˣ,
      ‖w (diagUnits2 a₁ a₂ * k)‖ ≤
        C * ‖((a₂ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ τ * max 1 ((‖((a₁ * a₂⁻¹ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ A)⁻¹)) :
    ∀ (g₀ : GL (Fin 2) (p.adicCompletion ℚ)) (a₁ a₂ : (p.adicCompletion ℚ)ˣ),
      ‖w (diagUnits2 a₁ a₂ * g₀)‖ ≤
        C * ‖((a₂ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ τ * (max ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖ ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖) ^ τ *
          max 1 ((‖((a₁ * a₂⁻¹ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ A)⁻¹) *
          max 1 (((‖((Matrix.GeneralLinearGroup.det g₀ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ / (max ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖ ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖) ^ 2) ^ A)⁻¹) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_WhittakerModel_norm_diagUnits2_mul_le_of_forall_mem_localLevelOne_norm_diagUnits2_mul_le.solution
