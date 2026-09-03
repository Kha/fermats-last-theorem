import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2KernelCasimir
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_archConvN_and_eq_of_forall_integral_kernelCasimir

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.CubicInduction
  LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.SlabL2.casimir_archConvN_and_eq_of_forall_integral_kernelCasimir :
    (∀ (Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), Continuous Φ → ∀ (β : (Fin 3 → Fin 3 → ℝ) → ℂ), IsSmoothArchFactor β →
      (IsSmoothArchFactor (kernelCasimir1 β) ∧ IsSmoothArchFactor (kernelCasimir2 β) ∧
          IsSmoothArchFactor (kernelCasimir3 β)) ∧
        WhittakerBlock.casimir1 (archConvN (Fin 3) ℚ Φ fun h => β (kernelEnt h)) =
            archConvN (Fin 3) ℚ Φ (fun h => kernelCasimir1 β (kernelEnt h)) ∧
          WhittakerBlock.casimir2 (archConvN (Fin 3) ℚ Φ fun h => β (kernelEnt h)) =
              archConvN (Fin 3) ℚ Φ (fun h => kernelCasimir2 β (kernelEnt h)) ∧
            WhittakerBlock.casimir3 (archConvN (Fin 3) ℚ Φ fun h => β (kernelEnt h)) =
              archConvN (Fin 3) ℚ Φ (fun h => kernelCasimir3 β (kernelEnt h))) ∧
      ∀ (f : (Fin 3 → Fin 3 → ℝ) → ℂ) (c : ℂ),
        (ContDiffOn ℝ 1 f {m | (Matrix.of m).det ≠ 0} →
          (∀ β : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor β →
            (letI := archGLBorelN (Fin 3) ℚ
             ∫ h, f (kernelEnt h) * kernelCasimir1 β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ) =
              c * (letI := archGLBorelN (Fin 3) ℚ
                   ∫ h, f (kernelEnt h) * β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ)) →
            ∀ m : Fin 3 → Fin 3 → ℝ, (Matrix.of m).det ≠ 0 → -kernelCasimir1 f m = c * f m) ∧
        (ContDiffOn ℝ 2 f {m | (Matrix.of m).det ≠ 0} →
          (∀ β : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor β →
            (letI := archGLBorelN (Fin 3) ℚ
             ∫ h, f (kernelEnt h) * kernelCasimir2 β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ) =
              c * (letI := archGLBorelN (Fin 3) ℚ
                   ∫ h, f (kernelEnt h) * β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ)) →
            ∀ m : Fin 3 → Fin 3 → ℝ, (Matrix.of m).det ≠ 0 → kernelCasimir2 f m = c * f m) ∧
        (ContDiffOn ℝ 3 f {m | (Matrix.of m).det ≠ 0} →
          (∀ β : (Fin 3 → Fin 3 → ℝ) → ℂ, IsSmoothArchFactor β →
            (letI := archGLBorelN (Fin 3) ℚ
             ∫ h, f (kernelEnt h) * kernelCasimir3 β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ) =
              c * (letI := archGLBorelN (Fin 3) ℚ
                   ∫ h, f (kernelEnt h) * β (kernelEnt h) ∂archGLHaarN (Fin 3) ℚ)) →
            ∀ m : Fin 3 → Fin 3 → ℝ, (Matrix.of m).det ≠ 0 → -kernelCasimir3T f m = c * f m) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_casimir_archConvN_and_eq_of_forall_integral_kernelCasimir.solution
