import Mathlib
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open LanglandsTunnell.TateLocal

theorem AutomorphicForm.exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval
    (F : Type) [Field F] (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion]
    (μa : Measure w.Completion) [μa.IsAddHaarMeasure]
    (χ : (w.Completion)ˣ →* ℂˣ)
    (_hχ : ∀ u, ‖((χ u : ℂˣ) : ℂ)‖ = 1)
    (_hχc : Continuous fun u : (w.Completion)ˣ => ((χ u : ℂˣ) : ℂ))
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) :
    ∃ (m : ℕ) (Φ : Fin m → (Fin 2 → w.Completion) → ℂ) (e : Fin m → ℂ → ℂ),
      (∀ j, Differentiable ℂ (e j)) ∧
      (∀ j, ∃ Q : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ y : Fin 2 → w.Completion,
        Φ j y = MvPolynomial.eval
              (Sum.elim (fun i => Completion.extensionEmbedding w (y i))
                (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (y i)))) Q
            * Complex.exp (-(Real.pi : ℂ) * ∑ i, (((‖y i‖ ^ 2 : ℝ)) : ℂ))) ∧
      ∀ z : ℂ, 0 < z.re →
        ∀ x : Fin 2 → w.Completion, ∑ i, ‖x i‖ ^ 2 = 1 →
          (∀ u : (w.Completion)ˣ, ‖(u : w.Completion)‖ = 1 →
            MvPolynomial.eval
                (Sum.elim (fun i => Completion.extensionEmbedding w ((u : w.Completion) * x i))
                  (fun i => starRingEnd ℂ (Completion.extensionEmbedding w ((u : w.Completion) * x i)))) P
              = ((χ u : ℂˣ) : ℂ)⁻¹ *
                MvPolynomial.eval
                  (Sum.elim (fun i => Completion.extensionEmbedding w (x i))
                    (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (x i)))) P) →
          (∑ j, e j z * localZeta μa (fun t => Φ j (fun i => t * x i)) χ z)
            = MvPolynomial.eval
                (Sum.elim (fun i => Completion.extensionEmbedding w (x i))
                  (fun i => starRingEnd ℂ (Completion.extensionEmbedding w (x i)))) P := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_sum_mul_localZeta_line_polynomial_mul_gaussian_eq_eval.solution
