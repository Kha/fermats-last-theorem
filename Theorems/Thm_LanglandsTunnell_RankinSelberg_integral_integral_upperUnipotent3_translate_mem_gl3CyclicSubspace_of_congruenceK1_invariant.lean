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
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

theorem LanglandsTunnell.RankinSelberg.integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant
    (p : HeightOneSpectrum (𝓞 ℚ)) (f : ℕ)
    (W₀ : LocalGL3 p → ℂ)
    (hK1 : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₀ (g * k) = W₀ g)
    (φ φ₁ : p.adicCompletion ℚ → ℂ)
    (hφ : IsSchwartzBruhat φ) (hφ₁ : IsSchwartzBruhat φ₁) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ p
    (fun g : LocalGL3 p =>
        ∫ u, ∫ y, W₀ (g * upperUnipotent3 u 0 y) * (φ u * φ₁ y)
          ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p) ∂(LanglandsTunnell.TateLocal.selfDualHaarAt ℚ p)) ∈
      gl3CyclicSubspace W₀ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_integral_integral_upperUnipotent3_translate_mem_gl3CyclicSubspace_of_congruenceK1_invariant.solution
