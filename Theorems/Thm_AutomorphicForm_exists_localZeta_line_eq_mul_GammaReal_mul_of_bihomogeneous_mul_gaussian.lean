import Mathlib
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_localZeta_line_eq_mul_GammaReal_mul_of_bihomogeneous_mul_gaussian

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open LanglandsTunnell.TateLocal

theorem AutomorphicForm.exists_localZeta_line_eq_mul_GammaReal_mul_of_bihomogeneous_mul_gaussian
    (F : Type) [Field F] (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion]
    (μa : Measure w.Completion) [μa.IsAddHaarMeasure]
    (χ : (w.Completion)ˣ →* ℂˣ)
    (_hχ : ∀ u, ‖((χ u : ℂˣ) : ℂ)‖ = 1)
    (_hχc : Continuous fun u : (w.Completion)ˣ => ((χ u : ℂˣ) : ℂ))
    (a b : ℕ)
    (_hχab : ∀ u : (w.Completion)ˣ, ‖(u : w.Completion)‖ = 1 →
        ((χ u : ℂˣ) : ℂ) * (Completion.extensionEmbedding w (u : w.Completion) ^ a
          * starRingEnd ℂ (Completion.extensionEmbedding w (u : w.Completion)) ^ b) = 1) :
    ∃ (c τ : ℝ), 0 < c ∧
      ∀ (P : (Fin 2 → w.Completion) → ℂ),
        (∀ (t : w.Completion) (y : Fin 2 → w.Completion),
          P (fun i => t * y i)
            = Completion.extensionEmbedding w t ^ a
              * starRingEnd ℂ (Completion.extensionEmbedding w t) ^ b * P y) →
        ∀ z : ℂ, 0 < z.re →
          ∀ x : Fin 2 → w.Completion, ∑ i, ‖x i‖ ^ 2 = 1 →
            localZeta μa
                (fun t => P (fun i => t * x i)
                  * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖t * x i‖ ^ 2 : ℝ)) : ℂ)))
                χ z
              = (c : ℂ) * Complex.Gammaℝ ((w.mult : ℂ) * z + ((a + b : ℕ) : ℂ) + (τ : ℂ) * Complex.I)
                * P x := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_localZeta_line_eq_mul_GammaReal_mul_of_bihomogeneous_mul_gaussian.solution
