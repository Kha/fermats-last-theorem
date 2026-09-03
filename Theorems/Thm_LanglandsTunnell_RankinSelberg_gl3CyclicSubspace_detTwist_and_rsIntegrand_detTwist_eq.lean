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
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_gl3CyclicSubspace_detTwist_and_rsIntegrand_detTwist_eq

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical in

open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.gl3CyclicSubspace_detTwist_and_rsIntegrand_detTwist_eq
    (p : HeightOneSpectrum (𝓞 ℚ)) (μ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (W : LocalGL3 p → ℂ) (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (w₀p : GL (Fin 2) (p.adicCompletion ℚ)) (hw₀p : (w₀p : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :

    (∀ W₃ : LocalGL3 p → ℂ,
      W₃ ∈ gl3CyclicSubspace (fun g : LocalGL3 p => ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * W g) ↔
        (fun g : LocalGL3 p => ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * W₃ g) ∈ gl3CyclicSubspace W) ∧
    (∀ w₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ,
      w₂ ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
              ((μ (Matrix.GeneralLinearGroup.det (g * h)) : ℂˣ) : ℂ)⁻¹ * w (g * h)) ↔
        (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * w₂ g) ∈
          Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h))) ∧

    (∀ (W₃ : LocalGL3 p → ℂ) (w₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (s : ℂ),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        ((((μ (Matrix.GeneralLinearGroup.det (iotaGL g : LocalGL3 p)) : ℂˣ) : ℂ) * W₃ (iotaGL g)) * (((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ * w₂ g)) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) =
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (W₃ (iotaGL g) * w₂ g) * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))) ∧

    (∀ (W₃ : LocalGL3 p → ℂ) (w₂ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (s : ℂ),
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (dualWhittakerFn3 (fun x : LocalGL3 p => ((μ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * W₃ x) (iotaGL g) *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) *
            (((μ (Matrix.GeneralLinearGroup.det (w₀p * transposeInvN (Fin 2) g)) : ℂˣ) : ℂ)⁻¹ * w₂ (w₀p * transposeInvN (Fin 2) g))) g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)) =
      (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
        (dualWhittakerFn3 W₃ (iotaGL g) *
          (fun g : GL (Fin 2) (p.adicCompletion ℚ) => ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) * w₂ (w₀p * transposeInvN (Fin 2) g)) g) *
          ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_gl3CyclicSubspace_detTwist_and_rsIntegrand_detTwist_eq.solution
