import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import P2M.Util
import P2M.Sol.S_NumberField_InfinitePlace_Completion_exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem NumberField.InfinitePlace.Completion.exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous
    (F : Type) [Field F] (w : InfinitePlace F)
    (χ : (w.Completion)ˣ →* ℂˣ)
    (_hχc : Continuous fun x : (w.Completion)ˣ => ((χ x : ℂˣ) : ℂ)) :
    ∃ s : ℂ,
      (∀ (u : (w.Completion)ˣ) (r : ℝ), 0 < r → extensionEmbedding w (u : w.Completion) = (r : ℂ) →
        ((χ u : ℂˣ) : ℂ) = (r : ℂ) ^ s) ∧
      ((∀ u : (w.Completion)ˣ, ‖((χ u : ℂˣ) : ℂ)‖ = 1) → s.re = 0) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_InfinitePlace_Completion_exists_forall_apply_eq_cpow_of_extensionEmbedding_eq_of_continuous.solution
