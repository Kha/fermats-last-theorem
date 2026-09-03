import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_AutomorphicForm_SmoothingKernel
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_dualSection_mem_principalSeries2_and_jacquetIntegral_eq

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.dualSection_mem_principalSeries2_and_jacquetIntegral_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ))
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ)
    (w₀ : GL (Fin 2) (p.adicCompletion ℚ))
    (hw₀ : (w₀ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; 1, 0]) :
    (fun g : GL (Fin 2) (p.adicCompletion ℚ) => f (w₀ * AutomorphicForm.transposeInvN (Fin 2) g)) ∈
        principalSeries2 p ![(χ 1)⁻¹, (χ 0)⁻¹] ∧
    (letI := localBorel ℚ p
     ∀ (θ : AddChar (p.adicCompletion ℚ) ℂ) (ν : Measure (p.adicCompletion ℚ)) [ν.IsAddHaarMeasure]
       (g : GL (Fin 2) (p.adicCompletion ℚ)),
       (Integrable (fun y : p.adicCompletion ℚ =>
            f (w₀ * AutomorphicForm.transposeInvN (Fin 2) (w₀ * AutomorphicForm.unipotentGL2 y * g)) * θ⁻¹ y) ν ↔
          Integrable (fun y : p.adicCompletion ℚ =>
            f (w₀ * AutomorphicForm.unipotentGL2 y * (w₀ * AutomorphicForm.transposeInvN (Fin 2) g)) * θ y) ν) ∧
       ∫ y, f (w₀ * AutomorphicForm.transposeInvN (Fin 2) (w₀ * AutomorphicForm.unipotentGL2 y * g)) * θ⁻¹ y ∂ν =
         ∫ y, f (w₀ * AutomorphicForm.unipotentGL2 y * (w₀ * AutomorphicForm.transposeInvN (Fin 2) g)) * θ y ∂ν) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_dualSection_mem_principalSeries2_and_jacquetIntegral_eq.solution
