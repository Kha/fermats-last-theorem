import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import P2M.Util
import P2M.Sol.S_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace

open scoped Classical in

theorem AutomorphicForm.LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod
    (F : Type) [Field F] [NumberField F]
    (kdat : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (_habm : ∀ w, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 →
      ‖∫ y : mixedEmbedding.mixedSpace F,
          (∏ i : {w : InfinitePlace F // w.IsReal},
              ((((y.1 i : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (kdat i)
                * (((1 + (y.1 i) ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2)))
          * (∏ w : {w : InfinitePlace F // w.IsComplex},
              (y.2 w) ^ (abm w).1 * (starRingEnd ℂ) (y.2 w) ^ (abm w).2.1
                * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((abm w).2.2 : ℂ) / 2))‖ ≤ C := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod.solution
